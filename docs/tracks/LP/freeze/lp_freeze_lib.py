"""Shared helpers for the LP freeze and seal scripts (RUNBOOK §7; decision D62).

Every hash, body split and binder list comes from the frozen-anchor guard itself
(`scripts/check_frozen_anchors.py`, class `Guard`): `Guard.digest`, `Guard.check_theorem_region`
(prefix / body / suffix split) and `Guard.explicit_binders`. The approved object is read from git
(`<sha>:<draft dir>`), never from the working tree.
"""
from __future__ import annotations

import importlib.util
import json
import re
import subprocess
from pathlib import Path

PLACEHOLDERS = ("<APPROVAL-DATE>", "<DECISION>")
MARKER_BEGIN = "  -- FROZEN_ANCHOR_PROOF_BEGIN\n"
MARKER_END = "  -- FROZEN_ANCHOR_PROOF_END\n"


def load_guard(root: Path):
    """Import the repository's guard module (the hashing code of record)."""
    spec = importlib.util.spec_from_file_location("check_frozen_anchors", root / "scripts/check_frozen_anchors.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def git_show(root: Path, sha: str, rel: str) -> bytes:
    return subprocess.run(["git", "-C", str(root), "show", f"{sha}:{rel}"], capture_output=True, check=True).stdout


def parse_approved(spec: str) -> tuple[str, str]:
    sha, _, d = spec.partition(":")
    assert sha and d, f"--approved must be <sha>:<draft dir>, got {spec!r}"
    return sha, d.rstrip("/")


def approved_entries(root: Path, spec: str) -> list[dict]:
    sha, d = parse_approved(spec)
    return json.loads(git_show(root, sha, f"{d}/manifest-entries.json"))["entries"]


def approved_text(root: Path, spec: str, path: str) -> str:
    sha, d = parse_approved(spec)
    return git_show(root, sha, f"{d}/{path}.txt").decode("utf-8")


def fill(text: str, date: str, decision: str) -> str:
    """Fill the two placeholders; each must occur exactly once."""
    for p in PLACEHOLDERS:
        assert text.count(p) == 1, f"placeholder {p} occurs {text.count(p)} times"
    return text.replace("<APPROVAL-DATE>", date).replace("<DECISION>", decision)


def body_bounds(guard_mod, root: Path, text: str) -> tuple[int, int]:
    """(body_start, body_end) exactly as the guard computes them (Guard.check_theorem_region)."""
    g = guard_mod.Guard(root)
    stub = {"state": "DRAFT_SORRY", "prefix_sha256": None, "suffix_sha256": None}
    bounds = g.check_theorem_region(stub, "split", text, {"max_body_lines": 3, "max_body_bytes": 240})
    assert bounds is not None, g.errors
    return bounds


def split_theorem(guard_mod, root: Path, text: str) -> tuple[str, str, str]:
    s, e = body_bounds(guard_mod, root, text)
    return text[:s], text[s:e], text[e:]


def explicit_binders(guard_mod, root: Path, prefix: str) -> list[str]:
    return guard_mod.Guard(root).explicit_binders(prefix)


def digest(guard_mod, data: str | bytes) -> str:
    return guard_mod.Guard.digest(data)


def seal_body(export: str, binders: list[str], width: int = 100) -> str:
    """`  by exact <export> <binders>` wrapped at `width` columns with a 6-space continuation (RUNBOOK (d).3)."""
    lines, cur = [], "  by exact " + export
    for b in binders:
        if len(cur) + 1 + len(b) > width:
            lines.append(cur)
            cur = "      " + b
        else:
            cur += " " + b
    lines.append(cur)
    return "".join(l + "\n" for l in lines)


def docstring_seal(text: str) -> str | None:
    """The sealing string written in the frozen docstring: `... only to `by exact ...` when the provider ...`."""
    m = re.search(r"only\s+to\s+`(by\s+exact\s[^`]*)`\s+when\s+the\s+provider", text, re.S)
    return " ".join(m.group(1).split()) if m else None


def module_of(path: str) -> str:
    return path[: -len(".lean")].replace("/", ".")


def frozen_import_order(entries: list[dict], texts: dict[str, str]) -> list[str]:
    """Modules of the given entries in an order where every imported entry module comes first."""
    mods = {module_of(e["path"]): e["path"] for e in entries}
    deps = {m: [x for x in re.findall(r"(?m)^(?:public )?import (\S+)$", texts[p]) if x in mods]
            for m, p in mods.items()}
    order, seen = [], set()

    def visit(m, stack=()):
        if m in seen:
            return
        assert m not in stack, f"import cycle at {m}"
        for d in deps[m]:
            visit(d, stack + (m,))
        seen.add(m)
        order.append(m)
    for m in sorted(mods):
        visit(m)
    return order


def provider_stub(export_fqn: str, provider_export: str, copyright_block: str) -> str:
    """Provider stub in the W precedent's form (`KAM/Provider/Wave/Nlw2.lean` at d7aae35d): no declaration."""
    import textwrap
    para = (f"The proof of `{export_fqn}` is assembled here as `{provider_export}`, from graph predecessors and "
            "approved external inputs only. While the frozen anchor is `DRAFT_SORRY`, this module is quarantined: no "
            "module other than the anchor may import it.")
    return (copyright_block + "module\n\n/-!\n# Provider for the frozen theorem `" + export_fqn + "`\n\n"
            + textwrap.fill(para, 100, break_on_hyphens=False) + "\n-/\n")


COPYRIGHT = ("/-\nCopyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.\n"
             "Released under Apache 2.0 license as described in the file LICENSE.\n"
             "Authors: Scott Armstrong, Zohar Komargodski\n-/\n")
