"""Strict source verification with an independent kernel process per local module."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

sys.dont_write_bytecode = True
from proof_io import AXIOM_COMMAND, AXIOM_REPORT, ENTRY, MANIFEST, MODULE_IMPORT, STANDARD
from proof_io import SUPPORT, checksum_text, closure, code_only, digest, path_for


ROOT = Path(__file__).resolve().parent
LIBRARY = ROOT / ".lake/build/lib/lean"


def output(*cmd):
    run = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if run.returncode:
        raise RuntimeError(f"{cmd[0]} exited {run.returncode}\n{run.stdout}")
    return run.stdout


def verify_sources():
    modules = closure(ROOT)
    if tuple(modules) != tuple((ROOT / "modules.txt").read_text().splitlines()):
        raise ValueError("Module list differs from the transitive source imports")
    files = {path_for(m).as_posix(): data for m, data in modules.items()}
    files.update({name: (ROOT / name).read_bytes() for name in SUPPORT})
    actual = {p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*") if p.is_file()}
    expected = set(files) | {MANIFEST}
    if expected != actual:
        raise ValueError(f"Unexpected initial members: {sorted(actual ^ expected)}")
    if (ROOT / MANIFEST).read_text() != checksum_text(files):
        raise ValueError("Source manifest digest mismatch")
    return modules, files


def verify_lock(packages):
    for package in json.loads((ROOT / "lake-manifest.json").read_text())["packages"]:
        checkout = packages / package["name"]
        commit = output("git", "-C", checkout, "rev-parse", "HEAD").strip()
        if commit != package["rev"] or output("git", "-C", checkout, "status", "--porcelain", "--untracked-files=no").strip():
            raise ValueError(f"Dependency checkout differs from the lock: {package['name']}")
        print("locked-dependency", package["name"], commit, flush=True)


def verify_axioms(printed, expected, *, exact=False):
    seen = AXIOM_REPORT.findall(printed)
    if len(seen) != len(expected):
        raise ValueError(f"Missing transitive axiom report in:\n{printed}")
    for command, (name, raw) in zip(expected, seen, strict=True):
        if name != command and (exact or not name.endswith("." + command)):
            raise ValueError(f"Expected {command}, reported {name}")
        current = {item.strip() for item in raw.split(",") if item.strip()}
        if not current <= STANDARD:
            raise ValueError(f"Unauthorized axioms in {name}: {sorted(current - STANDARD)}")
    return len(seen)


def replay(module, raw, modules):
    source = path_for(module)
    code = code_only(raw.decode())
    real_imports = set()
    for record in output("lake", "env", "lean", "--deps", source).splitlines():
        path = Path(record).resolve()
        if path.is_relative_to(LIBRARY):
            real_imports.add(".".join(path.relative_to(LIBRARY).with_suffix("").parts))
    expected_imports = set(MODULE_IMPORT.findall(code)) & modules
    if real_imports != expected_imports:
        raise ValueError(f"Lean resolved an unexpected local import for {module}: {real_imports ^ expected_imports}")

    requested = AXIOM_COMMAND.findall(code)
    reports = output("lake", "env", "lean", "-DwarningAsError=true", source) if requested else ""
    count = verify_axioms(reports, requested)
    check = output("lake", "env", "leanchecker", "--verbose", module)
    compiled = (LIBRARY / source.with_suffix(".olean")).read_bytes()
    status = f"kernel_replay_exit=0 {module} source_sha256={digest(raw)} object_sha256={digest(compiled)}"
    return reports + check + status + "\n", count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("packages", type=Path, help="Separate clean external Lake packages backed by the matching cache")
    parser.add_argument("workers", nargs="?", type=int, default=2)
    args = parser.parse_args()
    if not 1 <= args.workers <= 4:
        parser.error("Choose between one and four workers")
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        os.environ.pop(key, None)
    os.environ["LEAN_NUM_THREADS"] = "1"
    if (ROOT / ".lake").exists():
        raise ValueError("Use a fresh extraction without a project .lake directory")
    modules, files = verify_sources()
    print(f"PASS lexical proof scan and exact source manifest on {len(modules)} modules", flush=True)
    packages = args.packages.resolve(strict=True)
    verify_lock(packages)
    version = output("lean", "--version").strip()
    if "version 4.33.1" not in version or "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" not in version:
        raise ValueError(f"Unexpected Lean version: {version}")
    print(version, flush=True)
    print(platform.system(), platform.machine(), "Initial project objects: 0", flush=True)
    (ROOT / ".lake").mkdir()
    (ROOT / ".lake/packages").symlink_to(packages, target_is_directory=True)
    subprocess.run(["lake", "--no-ansi", "--wfail", "build", "+" + ENTRY], cwd=ROOT, check=True,
                   env=dict(os.environ, LEAN_NUM_THREADS=str(args.workers)))
    print("strict_build_exit=0", flush=True)

    checks = (ROOT / "audit-names.txt").read_text().splitlines()
    audit = ROOT / ".lake/AuditThresholdTwo.lean"
    audit.write_text(f"import {ENTRY}\n" + "".join(f"#check {name}\n" for name in checks) +
                     "".join(f"#print axioms {name}\n" for name in checks))
    result = output("lake", "env", "lean", "-DwarningAsError=true", audit)
    targeted = verify_axioms(result, checks, exact=True)
    print("BEGIN targeted audit\n" + result + "END targeted audit", flush=True)

    counted = 0
    all_modules = set(modules)
    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        tasks = [pool.submit(replay, module, raw, all_modules) for module, raw in modules.items()]
        for task in tasks:
            log, count = task.result()
            print(log, end="", flush=True)
            counted += count
    if any((ROOT / name).read_bytes() != raw for name, raw in files.items()):
        raise ValueError("Frozen source changed during the build")
    print(f"PASS {len(modules)} cold project modules, {len(modules)} independent kernel replays, "
          f"{counted} source axiom reports and {targeted} targeted reports", flush=True)


if __name__ == "__main__":
    main()
