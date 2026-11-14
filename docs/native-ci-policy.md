# Explicit native proof exceptions

`scripts/native-ci-exceptions.json` is the complete opt-in list. It starts empty: no project
source may use `native_decide` by default. `lint_sources.sh` delegates only that spelling to
`check_native_policy.py`; all existing guards still apply, including `decide +native`,
`native := true`, `ofReduceBool`/`ofReduceNat`, custom axioms, unsafe code, extern implementations,
elaborators, resource overrides and provider quarantine. An exception does not bypass those guards.

The `native-policy` PR workflow runs fast source checks and regression fixtures. With an empty
registry it explicitly reports **no endpoint proof verification**, and skips both expensive jobs.
The existing `certifier-ci` workflow remains manual. Source-policy success does not imply a full
library build, a kernel replay, a sealed provider, or verification of a numerical certificate.

## Registering an exception

Add one exact repository-relative `.lean` path per exception; directories, globs, excluded files,
symlinks, duplicate entries, missing files and stale permissions are rejected. Only `native_decide`
is supported. Supply a concrete justification and an audit ID. Each audit must identify existing,
separate kernel and native final theorem modules and declarations. For example, the schema is:

```json
{
  "version": 1,
  "exceptions": [{
    "file": "Certificate/NativeProof.lean",
    "feature": "native_decide",
    "justification": "Exact finite certificate; kernel provider remains independently checked.",
    "audit": "certificate"
  }],
  "audits": [{
    "id": "certificate",
    "kernel": {"module": "Certificate.KernelFinal", "theorem": "Certificate.kernel_final"},
    "native": {"module": "Certificate.NativeFinal", "theorem": "Certificate.native_final"},
    "native_axioms": ["Certificate.NativeProof.checked._native.native_decide.ax_1"]
  }]
}
```

This is a schema example, not a registered or verified certificate. The endpoint modules must be
real Lake targets. Normal project rules still control application ownership and provider imports.
Every core source (including quarantined modules built outside the root), every frozen/provider
source, and each configured kernel endpoint must not transitively import exception files. Core
ownership follows the application library roots/parts and source prefixes in `scripts/build_roots.json`; Lake DSL is not parsed.
Exceptions therefore belong in opt-in application modules outside frozen/provider directories. Each exception must be reached by its native endpoint. Import lists may span lines; quoted
identifier components are supported, while quoted punctuation/path separators fail closed.

List **every exact generated native axiom name** reported by the final native theorem, including
any private-name indices. Only names ending in `._native.native_decide.ax_<number>` (optionally with numeric `_` disambiguators) qualify; there is no prefix permission or private-name normalization. Unexpected
axioms fail, and unused listed roots fail as stale. Kernel endpoints permit only `propext`,
`Classical.choice` and `Quot.sound`; native endpoints permit those plus their exact listed roots.
The list is an audited increase in the trust boundary, not a claim that native evaluation was
replayed by the kernel.

Nonempty configuration automatically schedules distinct kernel and native CI jobs:

```sh
python3 -I scripts/check_native_policy.py                 # source policy only
python3 -I scripts/test_native_policy.py                  # tiny negative fixtures, no Lean
python3 -I scripts/check_native_policy.py --mode kernel   # targeted builds, leanchecker --fresh, axioms
python3 -I scripts/check_native_policy.py --mode native   # targeted builds, axioms, endpoint type check
```

The kernel job builds each kernel endpoint, replays its entire import closure with `leanchecker`,
and checks `#print axioms` of the final theorem. The native job builds both endpoints, checks the
native final theorem's axioms, and typechecks a generated Lean client:
`example : @Certificate.kernel_final = @Certificate.native_final := rfl`.
Homogeneous equality requires the same endpoint type, including the same certificate parameters;
proof irrelevance proves equality of the proofs. A missing endpoint, mismatched statement, build
failure, missing axiom report or failed replay fails the job. Neither job can stand in for the other.
Running either endpoint mode with an empty registry fails with “NO ENDPOINTS CONFIGURED”.

Review changes to the registry, checker, tests, lint integration and workflow together. Maintainers
should require protected review and both configured endpoint checks before accepting exceptions;
this patch does not configure GitHub branch protection or assert an existing CODEOWNERS policy.
Ordinary landing checks, including the existing library-wide kernel replay, remain necessary.
