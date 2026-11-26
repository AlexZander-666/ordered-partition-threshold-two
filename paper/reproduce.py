"""Replay both finite certificates and rebuild the paper twice in fresh directories."""

import argparse
from hashlib import sha256
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory
from zipfile import ZipFile


ROOT = Path(__file__).resolve().parent
MEMBERS = ("main.tex", "anc/finite.py", "anc/brackets.json", "anc/two_step.py", "anc/two-step-brackets.json")
EPOCH = "1795737600"
CANONICAL_PDF = "0bf7d05219d463a0295d469f5c78410b7db4233b1710ab12883fa32aefcd9568"


def get_sources():
    with ZipFile(ROOT / "arxiv-source.zip") as archive:
        if tuple(archive.namelist()) != MEMBERS or archive.testzip() is not None:
            raise ValueError("The source ZIP has unexpected members or a failed CRC.")
        zipped = {name: archive.read(name) for name in MEMBERS}
    loose = {name: (ROOT / name).read_bytes() for name in MEMBERS if (ROOT / name).exists()}
    if loose:
        if loose != zipped:
            raise ValueError("Loose sources are incomplete or differ from the source ZIP.")
        return loose, zipped
    return zipped, zipped


def replay(files, compiler, label, folder):
    for name, data in files.items():
        path = folder / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    for name in ("anc/finite.py", "anc/two_step.py"):
        subprocess.run([sys.executable, "-B", name], cwd=folder, check=True)
    env = dict(os.environ, SOURCE_DATE_EPOCH=EPOCH, FORCE_SOURCE_DATE="1", TZ="UTC")
    for pass_num in (1, 2):
        argv = [compiler, "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error", "main.tex"]
        run = subprocess.run(argv, cwd=folder, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if run.returncode:
            raise RuntimeError(run.stdout.decode(errors="replace"))
        print(f"{label} LaTeX pass {pass_num}: exit 0")
    log = (folder / "main.log").read_text()
    warnings = re.findall(
        r"^(?:Overfull|Missing character|LaTeX Warning|Package \S+ Warning).*", log, re.M
    )
    if warnings:
        raise RuntimeError("\n".join(warnings))
    return (folder / "main.pdf").read_bytes()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, help="Also save the rebuilt PDF to a new path")
    args = parser.parse_args()
    local_tex = Path.home() / ".cache/spark-math-research/texlive/2026/bin/aarch64-linux/pdflatex"
    compiler = os.environ.get("PDFLATEX") or shutil.which("pdflatex")
    if not compiler and local_tex.is_file():
        compiler = str(local_tex)
    if not compiler:
        raise SystemExit("Install TeX Live 2026 or set PDFLATEX to its executable.")

    loose, zipped = get_sources()
    with TemporaryDirectory(prefix="threshold-two-rebuild-") as work:
        folder = Path(work)
        pdf = replay(loose, compiler, "first source tree", folder / "first")
        if replay(zipped, compiler, "second source tree", folder / "second") != pdf:
            raise RuntimeError("Fresh builds produced different PDF bytes.")
    checksum = sha256(pdf).hexdigest()
    print(f"{checksum}  rebuilt.pdf")
    if args.output:
        with args.output.open("xb") as output:
            output.write(pdf)
    if checksum != CANONICAL_PDF:
        raise SystemExit("Local builds agree, but differ from the submitted PDF. Check the TeX version.")
    print("PASS both source trees and the submitted TeX Live 2026 PDF match byte for byte.")


if __name__ == "__main__":
    main()
