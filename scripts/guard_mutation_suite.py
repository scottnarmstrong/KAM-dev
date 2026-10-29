#!/usr/bin/env python3
"""Mutation suite for the KAM freeze guards (driven by scripts/guard_mutation_suite.sh).

Copies the working tree (tracked + untracked, minus .git/.lake/.drafts) to a throwaway directory,
checks that the unmutated copy passes the source-level landing gate, then applies each known-bad
mutation one at a time, runs the gate and asserts that it REJECTS (non-zero exit, no Python
traceback), then restores the touched files. The gate is `scripts/lint_sources.sh` of the copy,
with the Lean-dependent ABI-hash step stubbed out unless --with-abi is given; the layer(s) that
fired are read from the gate's stderr. Exit 1 if any mutation is accepted (a guard bug) or crashes.
The suite only reports guard gaps; it never fixes a guard.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path

REAL = Path(__file__).resolve().parent.parent
FROZEN_THM = "KAM/Frozen/Planetary/Theorems/SecularBoxSafety.lean"
FROZEN_DEF = "KAM/Frozen/Defs/ActionNbhd.lean"
FROZEN_DRAFT = "KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean"
PLAIN = "KAM/Canonical/Adjoint.lean"
PROVIDER = "KAM/Provider/AposterioriKam.lean"
MANIFEST = "manifest/frozen-anchors.json"
DRAFT_MODULE = "KAM.Frozen.Planetary.Theorems.PlanetaryExponentialSafety"
DRAFT_PROVIDER = "KAM.Provider.Planetary.PlanetaryExponentialSafety"
HDR = ("/-\nCopyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.\n"
       "Released under Apache 2.0 license as described in the file LICENSE.\n"
       "Authors: Scott Armstrong, Zohar Komargodski\n-/\n")


def module_file(body: str, imports: str = "") -> str:
    return (HDR + "module\n\n" + imports + "\n/-!\n# Mutation scratch module\n-/\n\n"
            "@[expose] public section\n\nnamespace KAM.MutationScratch\n\n" + body + "\nend KAM.MutationScratch\n")


class Tree:
    """A mutable copy of the repository with undo."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self.saved: dict[str, bytes | None] = {}

    def read(self, rel: str) -> str:
        return (self.root / rel).read_bytes().decode("utf-8")

    def write(self, rel: str, text: str | bytes) -> None:
        path = self.root / rel
        if rel not in self.saved:
            self.saved[rel] = path.read_bytes() if (path.exists() or path.is_symlink()) and not path.is_symlink() else None
        path.parent.mkdir(parents=True, exist_ok=True)
        if path.is_symlink():
            path.unlink()
        path.write_bytes(text if isinstance(text, bytes) else text.encode("utf-8"))

    def symlink(self, rel: str, target: str) -> None:
        path = self.root / rel
        self.saved.setdefault(rel, None)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.symlink_to(target)

    def edit(self, rel: str, old: str, new: str, count: int = 1) -> None:
        text = self.read(rel)
        if old not in text:
            raise RuntimeError(f"mutation setup: {old!r} not found in {rel}")
        self.write(rel, text.replace(old, new, count))

    def append(self, rel: str, extra: str) -> None:
        self.write(rel, self.read(rel) + extra)

    def restore(self) -> None:
        for rel, data in self.saved.items():
            path = self.root / rel
            if path.is_symlink() or path.exists():
                path.unlink()
            if data is not None:
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(data)
        self.saved.clear()


def manifest_edit(t: Tree, fn) -> None:
    data = json.loads(t.read(MANIFEST))
    fn(data)
    t.write(MANIFEST, json.dumps(data, indent=1, ensure_ascii=False) + "\n")


def anchor(data: dict, path: str) -> dict:
    return next(a for a in data["anchors"] if a["path"] == path)


def flip_hex(h: str) -> str:
    return ("0" if h[0] != "0" else "1") + h[1:]


def first_digit_after(text: str, marker: str) -> tuple[int, str]:
    start = text.index(marker)
    m = re.compile(r"\d").search(text, start)
    assert m
    return m.start(), m.group()


def flip_byte(t: Tree, rel: str, marker: str) -> None:
    text = t.read(rel)
    pos, digit = first_digit_after(text, marker)
    t.write(rel, text[:pos] + ("7" if digit != "7" else "8") + text[pos + 1:])


def long_file() -> str:
    return module_file("\n".join(f"theorem pad{i} : True := trivial" for i in range(1500)))


# (id, description, expected layer substring or None, needs_abi, mutation function)
def mutations() -> list[tuple[str, str, str, bool, object]]:
    M = []

    def add(mid, desc, layer, fn, abi=False):
        M.append((mid, desc, layer, abi, fn))

    # (a) frozen statements
    add("a1", "one byte of a frozen theorem statement (digit in the saturn box)", "FROZEN-ANCHOR",
        lambda t: flip_byte(t, FROZEN_THM, "theorem secularBoxSafety"))
    add("a2", "one byte of a frozen definition body (whole-file hash)", "FROZEN-ANCHOR",
        lambda t: t.edit(FROZEN_DEF, "< r}", "≤ r}"))
    add("a3", "one byte of a frozen theorem's docstring", "FROZEN-ANCHOR",
        lambda t: t.edit(FROZEN_THM, "P-SECULAR-BOX", "P-SECULAR-BOY"))
    add("a4", "trailing byte appended to a frozen theorem file (suffix hash)", "FROZEN-ANCHOR",
        lambda t: t.append(FROZEN_THM, "\n"))
    add("a5", "SEALED proof body replaced by `by sorry`", "FROZEN-ANCHOR",
        lambda t: t.edit(FROZEN_THM, "by exact KAM.Provider.Planetary.secularBoxSafety", "by sorry"))
    add("a6", "SEALED proof body is a non-assembly tactic block", "FROZEN-ANCHOR",
        lambda t: t.edit(FROZEN_THM, "by exact KAM.Provider.Planetary.secularBoxSafety",
                         "by\n  have h : True := trivial\n  exact KAM.Provider.Planetary.secularBoxSafety"))
    add("a7", "DRAFT_SORRY body replaced by a real term", "FROZEN-ANCHOR",
        lambda t: t.edit(FROZEN_DRAFT, "by sorry", "by exact absurd rfl (by decide : (1 : ℕ) ≠ 1)"))
    add("a8", "second declaration added to a frozen theorem file", "FROZEN-ANCHOR",
        lambda t: t.edit(FROZEN_THM, "end KAM.Planetary", "theorem extra : True := trivial\n\nend KAM.Planetary"))
    add("a9", "frozen theorem made `private`", "FROZEN-ANCHOR",
        lambda t: t.edit(FROZEN_THM, "theorem secularBoxSafety", "private theorem secularBoxSafety"))
    add("a10", "frozen proof-region marker removed", "FROZEN-ANCHOR",
        lambda t: t.edit(FROZEN_THM, "FROZEN_ANCHOR_PROOF_BEGIN", "FROZEN_ANCHOR_PROOF_BEGINX"))
    add("a11", "extra import added to the frozen prefix", "FROZEN-ANCHOR",
        lambda t: t.edit(FROZEN_THM, "public import KAM.Frozen.Planetary.Defs.SecularAMD",
                         "public import KAM.Frozen.Planetary.Defs.SecularAMD\npublic import KAM.Canonical.Adjoint"))
    add("a12", "frozen file deleted from the tree (manifest still lists it)", "FROZEN-ANCHOR",
        lambda t: (t.write(FROZEN_DEF, b""), (t.root / FROZEN_DEF).unlink()))
    # (b) sorry
    add("b1", "`sorry` in a non-frozen module", "forbidden sorry",
        lambda t: t.append(PLAIN, "\ntheorem mut_b1 : (1 : ℕ) = 2 := by sorry\n"))
    add("b2", "`sorry` in a provider module", "forbidden sorry",
        lambda t: t.append(PROVIDER, "\ntheorem mut_b2 : (1 : ℕ) = 2 := by sorry\n"))
    add("b3", "`admit` in a non-frozen module", "admit",
        lambda t: t.append(PLAIN, "\ntheorem mut_b3 : (1 : ℕ) = 2 := by admit\n"))
    add("b4", "`sorry` after a string containing `--`", "forbidden sorry",
        lambda t: t.append(PLAIN, '\ndef mut_b4 : String := "--"\ntheorem mut_b4t : (1 : ℕ) = 2 := sorry\n'))
    add("b5", "`sorry` in an untracked new file under KAM/Frozen", "",
        lambda t: t.write("KAM/Frozen/MutB5.lean", module_file("theorem b5 : (1 : ℕ) = 2 := sorry\n")))
    # (c) axiom, opaque, unsafe
    add("c1", "`axiom` in a non-frozen module", "forbidden axiom",
        lambda t: t.append(PLAIN, "\naxiom mut_c1 : False\n"))
    add("c2", "`private axiom`", "forbidden axiom",
        lambda t: t.append(PLAIN, "\nprivate axiom mut_c2 : False\n"))
    add("c3", "`opaque` constant", "forbidden opaque",
        lambda t: t.append(PLAIN, "\nopaque mut_c3 : ℕ\n"))
    add("c4", "`unsafe def`", "forbidden unsafe",
        lambda t: t.append(PLAIN, "\nunsafe def mut_c4 : ℕ := 0\n"))
    # (d) provider quarantine
    add("d1", "non-anchor module imports a sealed provider", "provider",
        lambda t: t.edit(PLAIN, "public import KAM.Canonical.Setting",
                         "public import KAM.Canonical.Setting\nimport KAM.Provider.AposterioriKam"))
    add("d2", "non-anchor module `public import`s a DRAFT provider", "provider",
        lambda t: t.edit(PLAIN, "public import KAM.Canonical.Setting",
                         f"public import KAM.Canonical.Setting\npublic import {DRAFT_PROVIDER}"))
    add("d3", "transitive: new module imports a provider, plain module imports the new one", "provider",
        lambda t: (t.write("KAM/MutD3.lean", module_file("", f"public import {DRAFT_PROVIDER}\n")),
                   t.edit(PLAIN, "public import KAM.Canonical.Setting",
                          "public import KAM.Canonical.Setting\npublic import KAM.MutD3")))
    # (e) DRAFT_SORRY anchor
    add("e1", "non-anchor module imports a DRAFT_SORRY anchor", "DRAFT_SORRY",
        lambda t: t.edit(PLAIN, "public import KAM.Canonical.Setting",
                         f"public import KAM.Canonical.Setting\nimport {DRAFT_MODULE}"))
    add("e2", "transitive import of a DRAFT_SORRY anchor through a new module", "DRAFT_SORRY",
        lambda t: (t.write("KAM/MutE2.lean", module_file("", f"public import {DRAFT_MODULE}\n")),
                   t.edit(PLAIN, "public import KAM.Canonical.Setting",
                          "public import KAM.Canonical.Setting\npublic import KAM.MutE2")))
    add("e3", "DRAFT_SORRY export used by name without an import", "DRAFT_SORRY",
        lambda t: t.append(PLAIN, "\n#check KAM.Planetary.planetaryExponentialSafety\n"))
    # (f) native_decide
    add("f1", "`native_decide`", "native_decide",
        lambda t: t.append(PLAIN, "\ntheorem mut_f1 : (2 : ℕ) + 2 = 4 := by native_decide\n"))
    add("f2", "`decide +native`", "native_decide",
        lambda t: t.append(PLAIN, "\ntheorem mut_f2 : (2 : ℕ) + 2 = 4 := by decide +native\n"))
    add("f3", "`Lean.ofReduceBool` use", "native_decide",
        lambda t: t.append(PLAIN, "\n#print axioms Lean.ofReduceBool\ntheorem mut_f3 := @Lean.ofReduceBool\n"))
    # (g) resource overrides
    add("g1", "`set_option maxHeartbeats`", "resource-limit",
        lambda t: t.append(PLAIN, "\nset_option maxHeartbeats 400000\n"))
    add("g2", "`set_option maxHeartbeats ... in` before a theorem", "resource-limit",
        lambda t: t.append(PLAIN, "\nset_option maxHeartbeats 0 in\ntheorem mut_g2 : True := trivial\n"))
    add("g3", "`set_option maxRecDepth`", "resource-limit",
        lambda t: t.append(PLAIN, "\nset_option maxRecDepth 100000\n"))
    add("g4", "`set_option synthInstance.maxHeartbeats`", "resource-limit",
        lambda t: t.append(PLAIN, "\nset_option synthInstance.maxHeartbeats 0\n"))
    add("g5", "`set_option  maxHeartbeats` with extra spaces mid-line", "resource-limit",
        lambda t: t.append(PLAIN, "\nopen Nat in set_option   maxHeartbeats 0 in\ntheorem mut_g5 : True := trivial\n"))
    add("g6", "`set_option maxHeartbeats` in a lakefile-style option array", "",
        lambda t: t.write("KAM/MutG6.lean", module_file("set_option maxHeartbeats 1 in theorem g6 : True := trivial\n")))
    # (h) size
    add("h1", "Lean file of 1501+ lines", "over 1500",
        lambda t: t.write("KAM/MutH1.lean", long_file()))
    add("h2", "Lean line over 100 characters", "over 100",
        lambda t: t.append(PLAIN, "\ntheorem mut_h2 : True := trivial -- " + "x" * 120 + "\n"))
    # (i) module system
    add("i1", "non-module `.lean` file", "check_lean_modules",
        lambda t: t.write("KAM/MutI1.lean", "import Mathlib.Tactic.Linarith\n\ntheorem i1 : True := trivial\n"))
    add("i2", "`module` keyword after a doc comment (not first token)", "check_lean_modules",
        lambda t: t.write("KAM/MutI2.lean", "/-- doc -/\nmodule\n\ntheorem i2 : True := trivial\n"))
    add("i3", "symlinked `.lean` file", "check_lean_modules",
        lambda t: t.symlink("KAM/MutI3.lean", "Canonical/Adjoint.lean"))
    add("i4", "existing module loses its `module` header", "check_lean_modules",
        lambda t: t.edit(PLAIN, "\nmodule\n", "\n"))
    # (j) manifest
    add("j1", "manifest full_file_sha256 edited", "FROZEN-ANCHOR",
        lambda t: manifest_edit(t, lambda d: anchor(d, FROZEN_DEF).__setitem__(
            "full_file_sha256", flip_hex(anchor(d, FROZEN_DEF)["full_file_sha256"]))))
    add("j2", "manifest abi_sha256 edited (needs Lean: --with-abi)", "ABI",
        lambda t: manifest_edit(t, lambda d: anchor(d, FROZEN_DEF).__setitem__(
            "abi_sha256", flip_hex(anchor(d, FROZEN_DEF)["abi_sha256"]))), abi=True)
    add("j3", "anchor removed from the manifest (its file stays)", "FROZEN-ANCHOR",
        lambda t: manifest_edit(t, lambda d: d["anchors"].remove(anchor(d, FROZEN_DEF))))
    add("j4", "manifest state SEALED -> DRAFT_SORRY for a sealed theorem", "FROZEN-ANCHOR",
        lambda t: manifest_edit(t, lambda d: anchor(d, FROZEN_THM).__setitem__("state", "DRAFT_SORRY")))
    add("j5", "manifest is invalid JSON", "FROZEN-ANCHOR",
        lambda t: t.append(MANIFEST, "garbage"))
    add("j6", "manifest anchors emptied", "FROZEN",
        lambda t: manifest_edit(t, lambda d: d.__setitem__("anchors", [])))
    add("j7", "manifest seal limit raised", "FROZEN-ANCHOR",
        lambda t: manifest_edit(t, lambda d: d["seal_limits"].__setitem__("max_body_lines", 300)))
    add("j8", "manifest author approval field dropped", "FROZEN-ANCHOR",
        lambda t: manifest_edit(t, lambda d: anchor(d, FROZEN_DEF).pop("author_approval")))
    add("j9", "manifest definition_closure hash edited for a theorem's dependency", "FROZEN-ANCHOR",
        lambda t: manifest_edit(t, lambda d: next(
            a for a in d["anchors"] if a["definition_closure"])["definition_closure"][0].__setitem__(
            "sha256", "0" * 64)))
    # (k) metaprogramming and further landing-guards.md cases
    add("k1", "`open ... in elab` (elaborator mid-line)", "elaborator",
        lambda t: t.append(PLAIN, '\nopen Lean Meta Elab Term in elab "fake" : term => return Lean.mkConst ``True\n'))
    add("k2", "`macro`", "elaborator", lambda t: t.append(PLAIN, '\nmacro "mut_k2" : term => `(True)\n'))
    add("k3", "`macro_rules`", "elaborator",
        lambda t: t.append(PLAIN, '\nmacro_rules | `(mut_k3) => `(True)\n'))
    add("k4", "`syntax` command", "elaborator", lambda t: t.append(PLAIN, '\nsyntax "mut_k4" : term\n'))
    add("k5", "`elab_rules`", "elaborator",
        lambda t: t.append(PLAIN, '\nelab_rules : term | `(mut_k5) => return Lean.mkConst ``True\n'))
    add("k6", "`run_cmd`", "run-command", lambda t: t.append(PLAIN, "\nrun_cmd Lean.logInfo \"x\"\n"))
    add("k7", "`run_elab`/`run_meta`", "run-command",
        lambda t: t.append(PLAIN, "\nrun_meta Lean.logInfo \"x\"\n"))
    add("k8", "`addDecl` in a user-defined command body", "addDecl",
        lambda t: t.append(PLAIN, "\ndef mut_k8 : Lean.CoreM Unit := Lean.addDecl (Lean.Declaration.defnDecl default)\n"))
    add("k9", "`set_option debug.skipKernelTC`", "debug",
        lambda t: t.append(PLAIN, "\nset_option debug.skipKernelTC true\n"))
    add("k10", "`attribute [command_elab ...]`", "elaborator",
        lambda t: t.append(PLAIN, "\nattribute [command_elab Lean.Parser.Command.declaration] mut_k10\n"))
    add("k11", "`@[term_elab ...]` attribute", "elaborator",
        lambda t: t.append(PLAIN, "\n@[term_elab Lean.Parser.Term.app] def mut_k11 : Lean.Elab.Term.TermElab := fun _ _ => default\n"))
    add("k12", "`by_elab`", "run-command",
        lambda t: t.append(PLAIN, "\ntheorem mut_k12 : True := by_elab return Lean.mkConst ``True.intro\n"))
    add("k13", "`EuclideanSpace` in code", "EuclideanSpace",
        lambda t: t.append(PLAIN, "\nabbrev MutK13 := EuclideanSpace ℝ (Fin 2)\n"))
    add("k14", "new module not imported by KAM.lean (stale root)", "root",
        lambda t: t.write("KAM/MutK14.lean", module_file("theorem k14 : True := trivial\n")))
    add("k15", "module imports the root `KAM`", "root",
        lambda t: t.edit(PLAIN, "public import KAM.Canonical.Setting",
                         "public import KAM.Canonical.Setting\nimport KAM"))
    add("k16", "errata ledger edited without re-rendering", "errata",
        lambda t: t.edit("docs/errata/ledger.json", "{", '{"mutation_marker": 1,', 1))
    add("k17", "import cycle between two plain modules", "cycle",
        lambda t: (t.write("KAM/MutK17A.lean", module_file("", "public import KAM.MutK17B\n")),
                   t.write("KAM/MutK17B.lean", module_file("", "public import KAM.MutK17A\n"))))
    add("k18", "BOM / non-UTF-8 junk before `module`", "check_lean_modules",
        lambda t: t.write("KAM/MutK18.lean", b"\xff\xfe" + module_file("").encode()))
    add("k19", "`sorry` hidden in a docstring-adjacent nested comment close", "forbidden sorry",
        lambda t: t.append(PLAIN, "\n/- a -/ theorem mut_k19 : (1 : ℕ) = 2 := sorry\n"))
    add("k20", "`sorryAx` used explicitly", "sorry",
        lambda t: t.append(PLAIN, "\ntheorem mut_k20 : (1 : ℕ) = 2 := sorryAx _ false\n"))
    add("k21", "Challenge-style `comparator.json` with Challenge imported", "Challenge",
        lambda t: (t.write("comparator.json", json.dumps({
            "challenge_module": "KAM.Canonical.Adjoint", "solution_module": "KAM.Canonical.Setting",
            "theorem_names": [], "permitted_axioms": ["propext"], "enable_nanoda": True})),))
    return M


# layer names recognised in the gate's stderr
LAYERS = [
    (r"forbidden sorry", "lint:sorry"), (r"forbidden admit", "lint:admit"),
    (r"forbidden axiom", "lint:axiom"), (r"forbidden unsafe", "lint:unsafe"),
    (r"forbidden opaque", "lint:opaque"), (r"resource-limit", "lint:resource-limit"),
    (r"EuclideanSpace", "lint:EuclideanSpace"), (r"over 100 characters", "lint:line-length"),
    (r"over 1500 lines", "lint:file-size"), (r"KAM\.lean is out of date", "gen_root_imports"),
    (r"ERRATA-AND-DEVIATIONS\.md is out of date", "render_errata"), (r"check_lean_modules: FAIL", "check_lean_modules"),
    (r"FROZEN-ANCHOR GUARD FAILED", "check_frozen_anchors"),
    (r"Lean files under KAM/Frozen without any manifest anchor", "lint:empty-manifest"),
    (r"ABI DRIFT", "abi_hashes"),
]


def run_gate(root: Path, timeout: int) -> tuple[int, str, str]:
    env = os.environ | {"PYTHONDONTWRITEBYTECODE": "1"}
    p = subprocess.run(["nice", "-n", "10", "sh", "scripts/lint_sources.sh"], cwd=root, capture_output=True,
                       text=True, errors="replace", timeout=timeout, env=env)
    return p.returncode, p.stdout, p.stderr


def classify(out: str, err: str) -> list[str]:
    text = out + "\n" + err
    return [name for pat, name in LAYERS if re.search(pat, text)]


def make_copy(dest: Path, with_abi: bool) -> None:
    files = subprocess.run(["git", "-C", str(REAL), "ls-files", "-z", "--cached", "--others", "--exclude-standard"],
                           capture_output=True, check=True).stdout.split(b"\0")
    for raw in files:
        if not raw:
            continue
        rel = raw.decode()
        if rel.startswith((".drafts/", ".lake/")) or not (REAL / rel).exists():
            continue
        src, dst = REAL / rel, dest / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        if src.is_symlink():
            dst.symlink_to(os.readlink(src))
        else:
            shutil.copy2(src, dst)
    lint = dest / "scripts/lint_sources.sh"
    text = lint.read_text()
    if with_abi:
        (dest / ".lake").mkdir()
        for name in ("build", "config", "packages"):
            (dest / ".lake" / name).symlink_to(REAL / ".lake" / name)
        (dest / "lake-manifest.json").exists()
    else:
        text, n = re.subn(r'^(\s*)python3 -I "\$project_root/scripts/abi_hashes\.py".*$', r"\1true", text, flags=re.M)
        if n != 1:
            raise SystemExit("cannot stub the ABI step in the copy: lint_sources.sh changed shape")
    lint.write_text(text)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--with-abi", action="store_true", help="keep the Lean-based ABI-hash layer (needs the build)")
    ap.add_argument("--only", help="comma-separated mutation ids")
    ap.add_argument("--scratch", help="parent directory of the throwaway copy (default $TMPDIR or /tmp)")
    ap.add_argument("--keep", action="store_true", help="keep the throwaway copy")
    ap.add_argument("--timeout", type=int, default=900, help="per-gate-run timeout, seconds")
    ap.add_argument("--json", help="write results as JSON to this path")
    args = ap.parse_args()

    # Never under `.drafts/`: the guards skip that directory, so mutations there would go unseen.
    scratch_parent = Path(args.scratch or os.environ.get("TMPDIR") or "/tmp")
    if ".drafts" in scratch_parent.resolve().parts or ".lake" in scratch_parent.resolve().parts:
        raise SystemExit("--scratch must not lie under .drafts or .lake (the guards skip those)")
    work = Path(tempfile.mkdtemp(prefix="guard-mutation-", dir=scratch_parent))
    try:
        t0 = time.time()
        make_copy(work, args.with_abi)
        tree = Tree(work)
        print(f"copy at {work} ({time.time() - t0:.1f}s)", flush=True)
        t1 = time.time()
        rc, out, err = run_gate(work, args.timeout)
        base_t = time.time() - t1
        ok_marker = "FROZEN-ANCHOR GUARD OK" in out and "check_lean_modules: PASS" in out
        if rc != 0 or not ok_marker:
            print("BASELINE FAILS on the unmutated copy; refusing to run mutations:\n" + err[-3000:] + out[-1500:])
            return 3
        print(f"baseline: gate passes ({base_t:.0f}s per run)", flush=True)

        only = set(args.only.split(",")) if args.only else None
        rows = []
        for mid, desc, expect, needs_abi, fn in mutations():
            if only and mid not in only:
                continue
            if needs_abi and not args.with_abi:
                rows.append((mid, desc, "-", "SKIPPED (needs --with-abi)", None))
                print(f"{mid:4} SKIPPED {desc}", flush=True)
                continue
            try:
                fn(tree)
            except Exception as exc:  # setup problem = suite bug, report loudly
                tree.restore()
                rows.append((mid, desc, "-", f"SETUP-ERROR {exc}", False))
                print(f"{mid:4} SETUP-ERROR {exc}", flush=True)
                continue
            try:
                rc, out, err = run_gate(work, args.timeout)
                crashed = "Traceback (most recent call last)" in err + out
                layers = classify(out, err)
                rejected = rc != 0 and not crashed
                verdict = "yes" if rejected else ("CRASH" if crashed and rc != 0 else "NO (ACCEPTED)")
                rows.append((mid, desc, ",".join(layers) or ("-" if rc == 0 else "unclassified rc=%d" % rc),
                             verdict, rejected))
                print(f"{mid:4} {verdict:14} {','.join(layers) or '-':40} {desc}", flush=True)
            finally:
                tree.restore()
        # confirm restoration
        rc, out, err = run_gate(work, args.timeout)
        restored = rc == 0 and "FROZEN-ANCHOR GUARD OK" in out
        print(f"after restore: gate {'passes' if restored else 'FAILS (suite bug)'}")

        print("\n| id | mutation | guard layer(s) that fired | rejected |\n|---|---|---|---|")
        for mid, desc, layers, verdict, _ in rows:
            print(f"| {mid} | {desc} | {layers} | {verdict} |")
        bad = [r for r in rows if r[4] is False]
        skipped = [r for r in rows if r[4] is None]
        print(f"\n{len(rows) - len(bad) - len(skipped)} rejected, {len(bad)} ACCEPTED/CRASH/ERROR, "
              f"{len(skipped)} skipped; elapsed {time.time() - t0:.0f}s")
        if args.json:
            Path(args.json).write_text(json.dumps(
                [dict(id=r[0], mutation=r[1], layers=r[2], verdict=r[3]) for r in rows], indent=1))
        if bad:
            print("GUARD BUGS (accepted mutations): " + ", ".join(r[0] for r in bad))
        return 1 if (bad or not restored) else 0
    finally:
        if args.keep:
            print(f"kept {work}")
        else:
            shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
