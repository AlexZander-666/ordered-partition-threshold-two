"""Rebuild the manuscript twice from loose source and twice from its source ZIP."""

import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
from tempfile import TemporaryDirectory
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo


ROOT = Path(__file__).resolve().parent
MEMBERS = ('main.tex', 'anc/finite.py', 'anc/brackets.json', 'anc/two_step.py', 'anc/two-step-brackets.json')
EPOCH = "1795737600"


def run_certificates(folder, label):
    for name in ("anc/finite.py", "anc/two_step.py"):
        result = subprocess.run(
            [sys.executable, "-B", name], cwd=folder, capture_output=True, text=True, check=True
        )
        print(f"{label} {name}: exit 0")
        print(result.stdout, end="")


def compile_pdf(folder, executable, label):
    env = dict(os.environ, SOURCE_DATE_EPOCH=EPOCH, FORCE_SOURCE_DATE="1", TZ="UTC")
    for pass_num in (1, 2):
        run = subprocess.run(
            [executable, "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error", "main.tex"],
            cwd=folder,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        if run.returncode:
            raise RuntimeError(run.stdout.decode(errors="replace"))
        print(f"{label} pass {pass_num}: exit 0")
    log = (folder / "main.log").read_text()
    warnings = re.findall(r"^(?:Overfull|Missing character|LaTeX Warning|Package \S+ Warning).*", log, re.M)
    if warnings:
        raise RuntimeError("\n".join(warnings))
    return (folder / "main.pdf").read_bytes()


def main():
    local_tex = Path.home() / ".cache/spark-math-research/texlive/2026/bin/aarch64-linux/pdflatex"
    executable = os.environ.get("PDFLATEX") or shutil.which("pdflatex")
    if not executable and local_tex.is_file():
        executable = str(local_tex)
    if not executable:
        raise SystemExit("Install TeX Live 2026 or set PDFLATEX to its executable.")

    files = {name: (ROOT / name).read_bytes() for name in MEMBERS}
    with TemporaryDirectory(prefix=".threshold-two-build-", dir=ROOT) as work:
        folder = Path(work)
        loose = folder / "loose"
        archive_source = folder / "archive-source"
        loose.mkdir()
        archive_source.mkdir()
        archive = folder / "arxiv-source.zip"
        with ZipFile(archive, "w") as zipped:
            for name, data in files.items():
                member = ZipInfo(name, (2026, 11, 27, 0, 0, 0))
                member.external_attr = 0o100644 << 16
                zipped.writestr(member, data, ZIP_DEFLATED)
                path = loose / name
                path.parent.mkdir(exist_ok=True)
                path.write_bytes(data)
        with ZipFile(archive) as zipped:
            assert zipped.testzip() is None
            assert tuple(zipped.namelist()) == MEMBERS
            zipped.extractall(archive_source)
        assert all((archive_source / name).read_bytes() == data for name, data in files.items())
        run_certificates(loose, "loose source")
        run_certificates(archive_source, "source ZIP")
        pdf = compile_pdf(loose, executable, "loose source")
        assert compile_pdf(archive_source, executable, "source ZIP") == pdf
        staged = folder / "main.pdf"
        staged.write_bytes(pdf)
        staged.replace(ROOT / "main.pdf")
        archive.replace(ROOT / "arxiv-source.zip")

    print("Both clean builds produced the same PDF bytes. ZIP contents and CRCs checked.")
    for name in ("main.pdf", "arxiv-source.zip", *MEMBERS):
        data = (ROOT / name).read_bytes()
        print(f"{hashlib.sha256(data).hexdigest()}  {name}")


if __name__ == "__main__":
    main()
