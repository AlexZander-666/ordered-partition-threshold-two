"""Inventory and lexical checks for the threshold-two Lean source archive."""

from hashlib import sha256
from pathlib import Path
import re
import stat
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo


ENTRY = "OrderedPartitions.TwoPoleAllSizes"
SUPPORT = ("README.md", "audit-names.txt", "lake-manifest.json", "lakefile.toml",
           "lean-toolchain", "modules.txt", "proof_io.py", "verify.py")
MANIFEST = "SOURCE-SHA256SUMS"
MODULE_IMPORT = re.compile(r"(?m)^[ \t]*(?:(?:public|private)[ \t]+)?import[ \t]+(?:all[ \t]+)?(\w[\w.]*)")
AXIOM_REPORT = re.compile(r"(?m)^'([^']+)' (?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])\s*$")
AXIOM_COMMAND = re.compile(r"(?m)^[ \t]*#print[ \t]+axioms[ \t]+(\S+)[ \t]*$")
FORBIDDEN = re.compile(
    r"\b(?:sorry|sorryAx|admit|native_decide|axiom|unsafe|implemented_by|extern|ofReduceBool|"
    r"trustCompiler|run_tac|skipKernelTC)\b"
)
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
LEXICAL = re.compile(r'/\-|\-/|--|"')


def digest(data):
    return sha256(data).hexdigest()


def path_for(module):
    return Path(*module.split(".")).with_suffix(".lean")


def blank(data):
    return re.sub(r"[^\n]", " ", data)


def code_only(source):
    """Blank nested block comments, line comments and strings while retaining line numbers."""
    pieces = []
    i = 0
    while match := LEXICAL.search(source, i):
        start = match.start()
        pieces.append(source[i:start])
        marker = match.group()
        if marker == "--":
            i = source.find("\n", start)
            if i == -1:
                i = len(source)
        elif marker == "/-":
            depth, i = 1, start + 2
            while depth:
                token = LEXICAL.search(source, i)
                if token is None:
                    raise ValueError("Unterminated block comment")
                if token.group() in ("/-", "-/"):
                    depth += 1 if token.group() == "/-" else -1
                i = token.end()
        elif marker == '"':
            end = re.match(r'"(?:\\.|[^"\\])*"', source[start:], re.S)
            if end is None:
                raise ValueError("Unterminated string")
            i = start + end.end()
        else:
            raise ValueError("Unexpected block comment terminator")
        pieces.append(blank(source[start:i]))
    pieces.append(source[i:])
    return "".join(pieces)


def closure(root):
    modules = {}
    pending = set()

    def visit(module):
        if module in modules:
            return
        if module in pending:
            raise ValueError(f"Cyclic import at {module}")
        pending.add(module)
        path = root / path_for(module)
        raw = path.read_bytes()
        code = code_only(raw.decode())
        match = FORBIDDEN.search(code)
        if match:
            line = code.count("\n", 0, match.start()) + 1
            raise ValueError(f"Forbidden proof construct {match.group()} at {path_for(module)}:{line}")
        for imported in MODULE_IMPORT.findall(code):
            if imported.startswith("OrderedPartitions.") or (root / path_for(imported)).is_file():
                visit(imported)
        pending.remove(module)
        modules[module] = raw

    visit(ENTRY)
    return modules


def archive(path, members):
    with ZipFile(path, "w") as output:
        for name, data in sorted(members.items()):
            entry = ZipInfo(name, (2026, 11, 27, 0, 0, 0))
            entry.create_system = 3
            entry.external_attr = 0o100644 << 16
            output.writestr(entry, data, ZIP_DEFLATED, compresslevel=9)


def read_archive(path):
    with ZipFile(path) as source:
        result = {}
        for entry in source.infolist():
            name = entry.filename
            logical = Path(name)
            if (entry.orig_filename != name or name in result or logical.is_absolute() or
                ".." in logical.parts or logical.as_posix() != name or "\\" in name or
                stat.S_IFMT(entry.external_attr >> 16) != stat.S_IFREG):
                raise ValueError(f"Unexpected source archive member {name!r}")
            result[name] = source.read(entry)
        return result


def checksum_text(files):
    return "".join(f"{digest(data)}  {name}\n" for name, data in sorted(files.items()))
