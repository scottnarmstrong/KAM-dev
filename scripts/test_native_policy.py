#!/usr/bin/env python3
"""Fast policy regressions; fixtures never run Lean or allocate a dependency tree."""
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
spec = importlib.util.spec_from_file_location("native_policy", ROOT / "scripts/check_native_policy.py")
policy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(policy)


class NativePolicyTests(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory(prefix="kam-native-policy-test-")
        self.addCleanup(self.scratch.cleanup)
        self.root = Path(self.scratch.name)
        (self.root / "scripts").mkdir()
        for file in ["check_lean_modules.py", "check_native_policy.py"]:
            (self.root / "scripts" / file).write_text((ROOT / "scripts" / file).read_text())
        self.write("scripts/build_roots.json", json.dumps({"core": {"root": "KAM"}, "applications": [{"lib": "NativeApp", "prefixes": ["Native", "Other", "Bridge"]}]}))
        self.write("manifest/frozen-anchors.json", '{"anchors": []}')
        self.write("NativeApp.lean", "import Native\n")
        self.write("KAM.lean", "import Kernel\n")
        self.write("Kernel.lean", "theorem kernel : True := True.intro\n")
        self.write("Native.lean", "theorem native : True := by native_decide\n")
        self.config = {"version": 1, "exceptions": [{"file": "Native.lean", "feature": "native_decide",
                       "justification": "Finite certificate; keep the kernel provider separately audited.",
                       "audit": "certificate"}],
                       "audits": [{"id": "certificate", "kernel": {"module": "Kernel", "theorem": "kernel"},
                                   "native": {"module": "Native", "theorem": "native"},
                                   "native_axioms": ["Native.native._native.native_decide.ax_1"]}]}

    def write(self, file, text):
        path = self.root / file
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def check(self):
        self.write("scripts/native-ci-exceptions.json", json.dumps(self.config))
        return policy.check_sources(self.root)

    def rejects(self, fragment):
        with self.assertRaisesRegex(ValueError, fragment):
            self.check()

    def test_valid_and_empty_registry(self):
        self.check()
        self.config["exceptions"] = []
        self.config["audits"] = []
        self.write("Native.lean", "-- native_decide in a comment is harmless\n")
        self.check()
        with self.assertRaisesRegex(ValueError, "NO ENDPOINTS CONFIGURED"):
            policy.audit_endpoints(self.root, {}, "kernel")

    def test_exact_generated_names_need_not_match_file_namespace(self):
        for root in ["Elsewhere.checked._native.native_decide.ax_1",
                     "_private.Native.0.checked._native.native_decide.ax_1",
                     "native._native.native_decide.ax_1_1"]:
            with self.subTest(root=root):
                self.config["audits"][0]["native_axioms"] = [root]
                self.check()

    def test_unlisted_native(self):
        self.write("Extra.lean", "theorem extra : True := by native_decide\n")
        self.rejects("unlisted native_decide")

    def test_paths_duplicates_and_stale_entries(self):
        for path in ["../Native.lean", "/Native.lean", "*.lean", "Missing.lean", "./Native.lean"]:
            with self.subTest(path=path):
                self.config["exceptions"][0]["file"] = path
                self.rejects("missing or excluded")
        self.config["exceptions"][0]["file"] = "Native.lean"
        self.config["exceptions"].append(dict(self.config["exceptions"][0]))
        self.rejects("duplicate exception")
        self.config["exceptions"].pop()
        self.write("Native.lean", "-- native_decide\n")
        self.rejects("stale native_decide")

    def test_unsupported_feature_missing_audit_and_stale_root(self):
        self.config["exceptions"][0]["feature"] = "unsafe"
        self.rejects("only native_decide")
        self.config["exceptions"][0]["feature"] = "native_decide"
        self.config["exceptions"][0]["audit"] = "missing"
        self.rejects("audit without exception")
        self.config["exceptions"][0]["audit"] = "certificate"
        self.config["audits"][0]["native_axioms"] = ["Native.*"]
        self.rejects("invalid Lean name")
        self.config["audits"][0]["native_axioms"] = ["sorryAx"]
        self.rejects("not an exact generated")

    def test_default_and_endpoint_transitive_imports(self):
        self.write("Bridge.lean", "public meta import all Native\n")
        self.write("KAM.lean", "import Bridge Kernel\n")
        self.rejects("default kernel closure or frozen/provider closure imports exception")
        self.write("KAM.lean", "import Kernel\n")
        self.write("Kernel.lean", "import Bridge\n")
        self.rejects("kernel endpoint imports exception")

    def test_multiline_and_quoted_imports(self):
        for text in ["module\nimport\n  Native\n", "module\nimport «Native»\n",
                     "module\npublic\nmeta import all\n Native\n"]:
            with self.subTest(text=text):
                self.write("Kernel.lean", text)
                self.rejects("kernel endpoint imports exception")

    def test_quoted_component_with_separator_fails_closed(self):
        self.write("Kernel.lean", "import «Bridge.WithDot»\n")
        self.write("Bridge.WithDot.lean", "import Native\n")
        self.rejects("unsupported quoted import component")

    def test_core_globs_and_all_frozen_provider_sources_are_protected(self):
        for path in ["KAM/CoreOutsideRoot.lean", "KAM/Frozen/OptIn.lean", "KAM/Provider/OptIn.lean"]:
            with self.subTest(path=path):
                self.write(path, "import Native\n")
                self.rejects("frozen/provider closure imports exception")
                (self.root / path).unlink()
        self.config["exceptions"][0]["file"] = "Core.lean"
        self.write("Core.lean", "theorem native : True := by native_decide\n")
        self.config["audits"][0]["native"]["module"] = "Core"
        self.write("Native.lean", "")
        self.rejects("frozen/provider closure imports exception")

    def test_native_endpoint_must_reach_exception(self):
        self.write("Other.lean", "theorem other : True := True.intro\n")
        self.config["audits"][0]["native"]["module"] = "Other"
        self.rejects("stale exception not reached")

    def test_all_other_source_guards_still_apply_to_allowed_file(self):
        # Run the existing shell guard section, with the real new source-policy call, on tiny fixtures.
        shell = (ROOT / "scripts/lint_sources.sh").read_text().split("# Count Unicode characters consistently:")[0]
        self.write("scripts/lint_sources.sh", shell + '\nexit "$status"\n')
        self.check()
        clean = subprocess.run(["sh", str(self.root / "scripts/lint_sources.sh")],
                               capture_output=True, text=True)
        self.assertEqual(clean.returncode, 0, clean.stdout + clean.stderr)
        for forbidden in ["axiom bad : True", "unsafe def bad := 0", "@[implemented_by x] def bad := 0",
                          "@[extern x] def bad := 0", "elab x : tactic => pure ()",
                          "theorem bad := Lean.ofReduceBool", "example : True := by decide +native",
                          "set_option maxHeartbeats 10000", "example : True := by sorry"]:
            with self.subTest(forbidden=forbidden):
                self.write("Native.lean", "theorem native : True := by native_decide\n" + forbidden + "\n")
                self.check()
                result = subprocess.run(["sh", str(self.root / "scripts/lint_sources.sh")],
                                        capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn("forbidden", result.stderr)

    def test_exact_axiom_sets_and_missing_reports(self):
        root = "Native.native._native.native_decide.ax_1"
        def report(*axioms):
            return "'native' depends on axioms: [" + ",\n".join(axioms) + "]"
        policy.check_axioms(report("propext"), "native", policy.STANDARD)
        policy.check_axioms(report("propext", root), "native", policy.STANDARD | {root}, [root])
        for unexpected in ["sorryAx", "customAxiom", root + "0", "Lean.ofReduceBool"]:
            with self.subTest(unexpected=unexpected), self.assertRaisesRegex(ValueError, "unexpected axioms"):
                policy.check_axioms(report(unexpected), "native", policy.STANDARD | {root})
        with self.assertRaisesRegex(ValueError, "stale native roots"):
            policy.check_axioms(report("propext"), "native", policy.STANDARD | {root}, [root])
        with self.assertRaisesRegex(ValueError, "missing or duplicate"):
            policy.check_axioms("", "native", policy.STANDARD)
        with self.assertRaisesRegex(ValueError, "missing or duplicate"):
            policy.check_axioms(report() + report(), "native", policy.STANDARD)


if __name__ == "__main__":
    unittest.main()
