#!/usr/bin/env python3
"""Black-box regression tests for check_frozen_anchors.py.

Run from the repository root: python3 -I scripts/test_frozen_anchors.py -v
Use POSIX Python (including MSYS2's /usr/bin/python3 on Windows): the existing
guard compares manifest paths with native Path strings, so a nested definition
closure currently fails its baseline under native Windows Python.

All Lean files and manifests below are synthetic fixtures in TemporaryDirectory,
outside this checkout. No real frozen file or manifest is changed. These tests
exercise the textual guard, not Lean elaboration, ABI hashing, or kernel replay.
The deliberately dummy ABI hashes are valid schema values only. No production
guard code is imported, and fixture hashes are computed independently.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


REPO = Path(__file__).resolve().parent.parent
GUARD = REPO / "scripts" / "check_frozen_anchors.py"
DEFINITION = "Fixture/Frozen/Value.lean"
SEALED = "Fixture/Frozen/Sealed.lean"
DRAFT = "Fixture/Frozen/Draft.lean"
SEALED_PROVIDER = "Fixture/Provider/Sealed.lean"
CONSUMER = "Fixture/Consumer.lean"
BRIDGE = "Fixture/Bridge.lean"
AUDIT = "Fixture/Audit/Probe.lean"
DEFINITION_TEXT = "module\npublic def Fixture.dotℂ : Nat := 0\n"
SEALED_HEADER = "(n m : Nat) : n + m = n + m"
SEALED_BODY = "  by exact Fixture.Provider.sealed n m\n"


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


class Fixture:
    """A tiny, independently assembled manifest and its source tree."""

    def __init__(self, root: Path) -> None:
        self.root = root
        self.manifest_path = root / "manifest.json"
        self.manifest = {
            "schema_version": 1,
            "manifest_state": "AUTHOR_APPROVED",
            "seal_limits": {"max_body_lines": 3, "max_body_bytes": 200},
            "anchors": [],
        }
        self.write(DEFINITION, DEFINITION_TEXT)
        self.definition = self.common("value", "definition", DEFINITION, "Fixture.dotℂ")
        self.definition["full_file_sha256"] = digest(DEFINITION_TEXT)
        self.manifest["anchors"].append(self.definition)
        self.write(SEALED_PROVIDER, "module\n"
                   "public theorem Fixture.Provider.sealed (n m : Nat) : n + m = n + m := by rfl\n")
        self.write("Fixture/Provider/Draft.lean", "module\n"
                   "public theorem Fixture.Provider.pending : True := by trivial\n")
        self.sealed = self.theorem("sealed", SEALED, "Fixture.sealed",
                                   "Fixture.Provider.Sealed", "Fixture.Provider.sealed",
                                   SEALED_HEADER, SEALED_BODY, "SEALED")
        self.sealed["definition_closure"] = [
            {"path": DEFINITION, "sha256": digest(DEFINITION_TEXT)}]
        self.draft = self.theorem("draft", DRAFT, "Fixture.pending",
                                  "Fixture.Provider.Draft", "Fixture.Provider.pending",
                                  ": True", "  by sorry\n", "DRAFT_SORRY")

    @staticmethod
    def common(identifier: str, kind: str, path: str, export: str) -> dict:
        return {
            "id": identifier,
            "kind": kind,
            "author_approval": {
                "approved_by": "synthetic test fixture",
                "approved_at": "2026-10-28",
                "approval_ref": "test-only",
                "approval_version": "1",
            },
            "source": {"revision": "fixture", "range": "entire fixture"},
            "contract": {"id": identifier, "version": "1"},
            "path": path,
            "export": export,
            "abi_sha256": "0" * 64,  # Placeholder: this CLI does not elaborate Lean.
            "definition_closure": [],
            "state": "SEALED",
            "split_policy": {"source_group": identifier, "mode": "NOT_SPLIT",
                             "ruling_ref": "test-only"},
        }

    def theorem(self, identifier: str, path: str, export: str, provider: str,
                provider_export: str, header: str, body: str, state: str) -> dict:
        anchor = self.common(identifier, "theorem", path, export)
        anchor.update({"state": state,
                       "implementation": {"module": provider, "export": provider_export},
                       "draft_allowlist": {"frozen_paths": [], "audit_paths": []}})
        self.manifest["anchors"].append(anchor)
        self.approve_theorem_fixture(anchor, header, body)
        return anchor

    def approve_theorem_fixture(self, anchor: dict, header: str, body: str) -> None:
        """Construct another synthetic approved baseline, never a production rebaseline."""
        prefix = ("-- FROZEN_ANCHOR_PREFIX_BEGIN\nmodule\n"
                  f"import {anchor['implementation']['module']}\n"
                  f"public theorem {anchor['export']} {header} :=\n"
                  "  -- FROZEN_ANCHOR_PROOF_BEGIN\n")
        suffix = ("  -- FROZEN_ANCHOR_PROOF_END\n"
                  "-- FROZEN_ANCHOR_SUFFIX_BEGIN\n"
                  "-- FROZEN_ANCHOR_SUFFIX_END\n")
        anchor["prefix_sha256"] = digest(prefix)
        anchor["suffix_sha256"] = digest(suffix)
        self.write(anchor["path"], prefix + body + suffix)

    def write(self, relative: str, text: str) -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(text.encode("utf-8"))

    def read(self, relative: str) -> str:
        return (self.root / relative).read_bytes().decode("utf-8")

    def replace(self, relative: str, before: str, after: str) -> None:
        text = self.read(relative)
        if text.count(before) != 1:
            raise AssertionError(f"fixture replacement must identify one occurrence: {before!r}")
        self.write(relative, text.replace(before, after, 1))

    def save_manifest(self) -> None:
        self.manifest_path.write_text(json.dumps(self.manifest, ensure_ascii=False), encoding="utf-8")


class FrozenAnchorTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="kam-frozen-guard-")
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name).resolve()
        self.assertNotEqual(root, REPO, "test fixtures must be outside the actual checkout")
        self.assertNotIn(REPO, root.parents, "test fixtures must be outside the actual checkout")
        self.fixture = Fixture(root)
        # Every mutation starts from an independently accepted complete fixture.
        self.assert_accepts()

    def run_guard(self, *, save_manifest: bool = True) -> subprocess.CompletedProcess:
        if save_manifest:
            self.fixture.save_manifest()
        before = {path.relative_to(self.fixture.root): path.read_bytes()
                  for path in self.fixture.root.rglob("*") if path.is_file()}
        result = subprocess.run(
            [sys.executable, "-I", str(GUARD), "--root", str(self.fixture.root),
             "--manifest", str(self.fixture.manifest_path)],
            cwd=self.fixture.root, capture_output=True, text=True, encoding="utf-8", timeout=30)
        after = {path.relative_to(self.fixture.root): path.read_bytes()
                 for path in self.fixture.root.rglob("*") if path.is_file()}
        self.assertEqual(after, before, "the guard must not create, delete, or change fixture files")
        return result

    def assert_accepts(self) -> None:
        result = self.run_guard()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "FROZEN-ANCHOR GUARD OK\n")
        self.assertEqual(result.stderr, "")

    def assert_rejects(self, *diagnostics: str) -> None:
        result = self.run_guard()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "")
        lines = result.stderr.splitlines()
        self.assertEqual(lines[0], "FROZEN-ANCHOR GUARD FAILED:")
        # Exact diagnostic sets prevent unrelated hash failures from passing a
        # quarantine, lexical, or assembly regression test.
        self.assertEqual(sorted(lines[1:]), sorted("- " + d for d in diagnostics))

    @staticmethod
    def draft_import(path: str) -> str:
        return ("draft: DRAFT_SORRY imported directly or transitively outside explicit "
                f"frozen/audit allowlist: {Path(path)}")

    @staticmethod
    def provider_import(path: str) -> str:
        return ("draft: DRAFT provider imported directly or transitively outside its provider "
                f"and frozen anchor: {Path(path)}")

    def test_baseline_with_unicode_export_and_authorized_draft(self) -> None:
        self.assert_accepts()

    def test_simpa_assembly_with_all_explicit_binders(self) -> None:
        self.fixture.replace(SEALED, SEALED_BODY,
                             "  by simpa using Fixture.Provider.sealed n m\n")
        self.assert_accepts()

    def test_implicit_and_nested_binders_are_not_extra_arguments(self) -> None:
        header = "{α : Type} [Inhabited α] (f : (Nat → Nat)) (n : Nat) : f n = f n"
        body = "  by exact Fixture.Provider.sealed f n\n"
        self.fixture.write(SEALED_PROVIDER, "module\npublic theorem Fixture.Provider.sealed "
                           + header + " := by rfl\n")
        self.fixture.approve_theorem_fixture(self.fixture.sealed, header, body)
        self.assert_accepts()

    def test_prefix_mutation(self) -> None:
        self.fixture.replace(SEALED, "public theorem", "-- changed prefix\npublic theorem")
        self.assert_rejects("anchor[1]: frozen prefix hash drift (all bytes before proof body changed)")

    def test_suffix_mutation(self) -> None:
        self.fixture.write(SEALED, self.fixture.read(SEALED) + "-- changed suffix\n")
        self.assert_rejects("anchor[1]: frozen suffix hash drift (all bytes after proof body changed)")

    def test_definition_mutation(self) -> None:
        self.fixture.replace(DEFINITION, ":= 0", ":= 1")
        self.assert_rejects("anchor[0]: whole-file definition anchor hash drift",
                            "anchor[1].definition_closure[0]: semantic definition hash drift")

    def test_closure_pins_the_dependent_definition(self) -> None:
        self.fixture.replace(DEFINITION, ":= 0", ":= 1")
        # A consistent whole-file hash cannot replace the dependent anchor's
        # separate approval of its definition closure.
        self.fixture.definition["full_file_sha256"] = digest(self.fixture.read(DEFINITION))
        self.assert_rejects("anchor[1].definition_closure[0]: semantic definition hash drift")

    def test_sealed_binders_must_be_exactly_in_order(self) -> None:
        for arguments in ("", "n", "m n", "n m n", "n (m)"):
            with self.subTest(arguments=arguments):
                body = "  by exact Fixture.Provider.sealed" + (" " + arguments if arguments else "") + "\n"
                self.fixture.replace(SEALED, SEALED_BODY, body)
                self.assert_rejects("anchor[1]: SEALED body must be trivial assembly of exactly "
                                    "implementation.export applied to the explicit binders n m")
                self.fixture.replace(SEALED, body, SEALED_BODY)

    def test_sealed_body_must_use_designated_export(self) -> None:
        self.fixture.replace(SEALED, SEALED_BODY, "  by exact Fixture.Provider.other n m\n")
        self.assert_rejects("anchor[1]: SEALED body must be trivial assembly of exactly "
                            "implementation.export applied to the explicit binders n m")

    def test_sealed_assembly_length_limit(self) -> None:
        bodies = {
            "lines": "  by\n    exact\n      Fixture.Provider.sealed\n        n m\n",
            "bytes": "  by exact" + " " * 200 + "Fixture.Provider.sealed n m\n",
        }
        for limit, body in bodies.items():
            with self.subTest(limit=limit):
                self.fixture.replace(SEALED, SEALED_BODY, body)
                self.assert_rejects("anchor[1]: SEALED body exceeds configured short assembly limits")
                self.fixture.replace(SEALED, body, SEALED_BODY)

    def test_sealed_provider_must_declare_designated_export(self) -> None:
        self.fixture.replace(SEALED_PROVIDER, "Fixture.Provider.sealed", "Fixture.Provider.other")
        self.assert_rejects("anchor[1].implementation.export: SEALED implementation export "
                            "is not declared exactly once in implementation.module")

    def test_draft_body_cannot_add_tactics(self) -> None:
        self.fixture.replace(DRAFT, "  by sorry\n", "  by\n    sorry\n    trivial\n")
        self.assert_rejects("anchor[2]: DRAFT_SORRY body must be exactly the single authorized `by sorry`",
                            "unauthorized `sorry` outside manifest-listed DRAFT proof region: "
                            + str(Path(DRAFT)))

    def test_unauthorized_sorry_and_admit(self) -> None:
        for escape in ("sorry", "admit"):
            with self.subTest(escape=escape):
                self.fixture.write(CONSUMER, "module\npublic theorem Fixture.ok : True := by trivial\n")
                self.assert_accepts()
                self.fixture.replace(CONSUMER, "by trivial", "by " + escape)
                self.assert_rejects(f"unauthorized `{escape}` outside manifest-listed DRAFT proof region: "
                                    + str(Path(CONSUMER)))

    def test_axiom_and_constant_declarations(self) -> None:
        for command in ("axiom", "constant"):
            with self.subTest(command=command):
                self.fixture.write(CONSUMER, "module\npublic theorem Fixture.ok : True := by trivial\n")
                self.assert_accepts()
                self.fixture.write(CONSUMER, f"module\npublic {command} Fixture.escape : True\n")
                self.assert_rejects(f"project-owned `{command}` command is forbidden: "
                                    f"{Path(CONSUMER)}:Fixture.escape")

    def test_direct_draft_anchor_import(self) -> None:
        self.fixture.write(CONSUMER, "module\nimport Fixture.Frozen.Sealed\n")
        self.assert_accepts()
        self.fixture.replace(CONSUMER, "Fixture.Frozen.Sealed", "Fixture.Frozen.Draft")
        self.assert_rejects(self.draft_import(CONSUMER), self.provider_import(CONSUMER))

    def test_transitive_draft_anchor_import(self) -> None:
        self.fixture.write(BRIDGE, "module\nimport Fixture.Frozen.Sealed\n")
        self.fixture.write(CONSUMER, "module\nimport Fixture.Bridge\n")
        self.assert_accepts()
        self.fixture.replace(BRIDGE, "Fixture.Frozen.Sealed", "Fixture.Frozen.Draft")
        self.assert_rejects(self.draft_import(BRIDGE), self.provider_import(BRIDGE),
                            self.draft_import(CONSUMER), self.provider_import(CONSUMER))

    def test_direct_draft_provider_import(self) -> None:
        self.fixture.write(CONSUMER, "module\nimport Fixture.Provider.Sealed\n")
        self.assert_accepts()
        self.fixture.replace(CONSUMER, "Fixture.Provider.Sealed", "Fixture.Provider.Draft")
        self.assert_rejects(self.provider_import(CONSUMER))

    def test_transitive_draft_provider_import(self) -> None:
        self.fixture.write(BRIDGE, "module\nimport Fixture.Provider.Sealed\n")
        self.fixture.write(CONSUMER, "module\nimport Fixture.Bridge\n")
        self.assert_accepts()
        self.fixture.replace(BRIDGE, "Fixture.Provider.Sealed", "Fixture.Provider.Draft")
        self.assert_rejects(self.provider_import(BRIDGE), self.provider_import(CONSUMER))

    def test_draft_export_use_without_import(self) -> None:
        self.fixture.write(CONSUMER, "module\n#check Fixture.sealed\n")
        self.assert_accepts()
        self.fixture.replace(CONSUMER, "Fixture.sealed", "Fixture.pending")
        self.assert_rejects("draft: DRAFT_SORRY used outside explicit frozen/audit allowlist: "
                            + str(Path(CONSUMER)))

    def test_draft_provider_export_use_without_import(self) -> None:
        self.fixture.write(CONSUMER, "module\n#check Fixture.Provider.sealed\n")
        self.assert_accepts()
        self.fixture.replace(CONSUMER, "Fixture.Provider.sealed", "Fixture.Provider.pending")
        self.assert_rejects("draft: DRAFT provider export used outside its provider and frozen anchor: "
                            + str(Path(CONSUMER)))

    def test_explicit_audit_allowlist_is_not_inherited_by_other_files(self) -> None:
        self.fixture.write(AUDIT, "module\n#check Fixture.pending\n")
        self.fixture.draft["draft_allowlist"]["audit_paths"] = [AUDIT]
        self.assert_accepts()
        self.fixture.write(CONSUMER, self.fixture.read(AUDIT))
        self.assert_rejects("draft: DRAFT_SORRY used outside explicit frozen/audit allowlist: "
                            + str(Path(CONSUMER)))

    def test_comments_strings_and_character_literals_are_not_code(self) -> None:
        self.fixture.write(CONSUMER, '''module
/- outer sorry /- nested admit -/ Fixture.pending -/
-- import Fixture.Frozen.Draft
-- axiom Fixture.escape : True
public def Fixture.words : String := "sorry admit Fixture.Provider.pending"
public def Fixture.multiline : String := """sorry
import Fixture.Provider.Draft
constant Fixture.escape : True
"""
public def Fixture.escaped : String := "\\\" sorry Fixture.pending"
public def Fixture.letter : Char := 's'
public def Fixture.quote : Char := '\\''
public def Fixture.symbol : Char := '∑'
''')
        self.assert_accepts()
        self.fixture.write(CONSUMER, self.fixture.read(CONSUMER)
                           + "public theorem Fixture.bad : True := by sorry\n")
        self.assert_rejects("unauthorized `sorry` outside manifest-listed DRAFT proof region: "
                            + str(Path(CONSUMER)))

    def test_tsum_prime_does_not_hide_code_until_another_prime(self) -> None:
        # Regression for D26: the apostrophe of ∑' is not an opening character quote.
        text = ("module\npublic def Fixture.series : Nat := ∑' k : Nat, k\n"
                "public theorem Fixture.visible : True := by trivial\n"
                "public def Fixture.tail' : Nat := 0\n")
        self.fixture.write(CONSUMER, text)
        self.assert_accepts()
        self.fixture.replace(CONSUMER, "by trivial", "by sorry")
        self.assert_rejects("unauthorized `sorry` outside manifest-listed DRAFT proof region: "
                            + str(Path(CONSUMER)))

    def test_provider_cannot_reverse_import_its_anchor(self) -> None:
        self.fixture.replace(SEALED_PROVIDER, "module\n", "module\nimport Fixture.Frozen.Sealed\n")
        self.assert_rejects("sealed: implementation module reverse-imports frozen anchor")

    def test_malformed_manifest_has_distinct_cli_exit_code(self) -> None:
        self.fixture.manifest_path.write_text("{", encoding="utf-8")
        result = self.run_guard(save_manifest=False)
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertEqual(result.stdout, "")
        self.assertTrue(result.stderr.startswith("FROZEN-ANCHOR GUARD FAILED: cannot read manifest:"),
                        result.stderr)


if __name__ == "__main__":
    unittest.main()
