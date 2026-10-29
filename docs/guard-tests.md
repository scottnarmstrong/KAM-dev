# Frozen-anchor regression tests

The campaign's [`I.GUARDS`](campaign/progress.json) work item calls for an automated mutation suite. Run it with
the Python standard library, from the repository root:

```sh
python3 -I scripts/test_frozen_anchors.py
```

`scripts/lint_sources.sh` runs the suite as part of normal source lint and returns a
failure if a regression test fails. Use the same POSIX Python environment as the source
checks (for example Linux or MSYS2 Python on Windows).

Each case constructs a small synthetic project in a fresh temporary directory and calls
the production `check_frozen_anchors.py` command. It first checks that the unmodified
fixture is accepted. Rejected mutations must produce the intended guard diagnostics;
a crash, unreadable manifest, or unrelated hash failure is not a passing negative test.
The suite does not modify the checkout's frozen files, manifest, or guard policy.

Coverage includes frozen bytes and definition closures, permitted sealed/draft bodies,
explicit binder arguments, draft import/export quarantine, and lexical handling of
comments, strings, character literals and Unicode. The D26 fixes for `∑'` and explicit
arguments to sealed providers have regression cases.

These are source-guard tests. The fixtures' ABI fields are synthetic placeholders with
the required hash shape; their values are not evidence of elaborated Lean declarations.
The suite does not invoke Lean or replace compilation, `abi_hashes.py`, axiom inspection,
or kernel replay. The real repository's frozen-source and ABI checks still run separately
in `lint_sources.sh`. Automated kernel replay remains separate work in `I.GUARDS`.
