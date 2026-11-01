# Helper for the wave-3 anchor specs (streamlined extraction, D65): mechanical binding of frozen anchors.
# - imports(path): the frozen definition anchors that a frozen declaration file imports directly (bound anchors only,
#   matched by file path through packets/anchor-binding.tsv); for a definition these are its DEPS (SPEC §1.3), for a
#   theorem its statement-symbol edges (SPEC §5).
# - doc(path): the declaration docstring (frozen file; never a proof body).
# - locator(source_range): the MAIN locator 'unit:x-y' of a binding source range.
import csv
import re
from pathlib import Path

G = Path("docs/graph/LP")
BIND = list(csv.DictReader(open(G / "packets/anchor-binding.tsv"), delimiter="\t"))
BY_PATH = {r["path"]: r for r in BIND}
BY_NODE = {r["node"]: r for r in BIND}


def imports(path):
    """bound anchors imported directly AND named in the declaration (from `namespace` on): imports that the
    declaration does not use are dropped"""
    text = Path(path).read_text()
    decl = text[text.find("\nnamespace "):]
    out = []
    for m in re.finditer(r"^public import (\S+)$", text, re.M):
        p = m.group(1).replace(".", "/") + ".lean"
        if p in BY_PATH:
            short = BY_PATH[p]["export"].split(".")[-1]
            if re.search(r"(?<![\w.])" + re.escape(short) + r"(?![\w])", decl) or \
                    re.search(r"\." + re.escape(short) + r"(?![\w])", decl):
                out.append(BY_PATH[p]["node"])
    return out


def doc(path):
    m = re.search(r"/-- (.*?)-/\s*\n\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable )?(?:def|theorem|abbrev|structure)",
                  Path(path).read_text(), re.S)
    return re.sub(r"\s+", " ", m.group(1)).replace("`", "").strip() if m else "-"


def locator(src):
    if src.startswith("reused"):
        return None
    unit = "s1" if "§1" in src else re.match(r"MAIN (L\d+|T\d+)", src).group(1)
    rngs = re.findall(r"(\d+)–(\d+)", src)
    if rngs:
        x, y = rngs[0]
    else:
        nums = [n for n in re.findall(r"\((\d+)\)", src) if int(n) > 10]
        x = y = nums[-1]
    return f"{unit}:{x}-{y}"
