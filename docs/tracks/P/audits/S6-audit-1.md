# S6 independent package audit 1

Audit date: 2026-10-28. Scope: only `KAM/Planetary/SecularBox/Rotation.lean`, as required by the S6 AUDIT FOCUS. Report destination follows the user override: `/root/code/KAM-inp-p14-s6/docs/tracks/P/audits/S6-audit-1.md`.

## Verdict

**Overall verdict: PASS WITH NOTES for S6 (`KAM.Planetary.sb_rot`).** The targeted build, exact-signature/application probes, axiom inspection and kernel replay pass. Lint exits 1 only for the explicitly permitted stale generated root; inherited comparison anomalies are retained below. No blocking mathematical, signature, completeness, or scoped hygiene defect was found. This package supplies an ordinary infrastructure theorem; it supplies no provider and seals no frozen anchor. In particular it does not prove the frozen `secularBoxSafety` or `secularBoxAtCitedMasses` roots.

## Inputs and comparison scope

Read AGENTS.md, PLAN, DECISIONS, the package audit brief, S6 handoff, P14 design row S6 and node table (235–239, 392), both P14 design audits, the signed statement, the blueprint and graph contracts, relevant frozen definitions and the secular section of the track statement. Design audit 2 closes audit 1's F1–F5; none of those findings changes the S6 contract. No external source claim requiring a new PDF audit is made: this node is marked “Ours; direct calculation from the frozen definitions”.

- HEAD: `248a8e8b23f3b9a36121b72ab0ba684b59001614`.
- Compared ref `inp`: `d343cead359c794f416340f529531719f7b449d2` at inspection.
- `git diff inp...HEAD` warns “multiple merge bases, using 824bb6c00a69ccc21f7fcff5041e654974c8df0c”. The full comparison has 64 files, 6864 insertions and 478 deletions; its out-of-scope inherited packages are not independently certified here.
- `git show --stat HEAD` and `git diff HEAD^ HEAD --name-only` isolate the S6 commit: only Rotation.lean, 188 added lines.
- The required protected-path comparison is **not empty**: inherited `KAM.lean` import additions and a line rewrap in `KAM/Frozen/Planetary/Theorems/AmdConfinement.lean`. The latter is commit `a81e8d42`; generated-root changes are earlier regeneration commits. `git diff HEAD^ HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. No S6 frozen/manifest/generated edit is attributed to this package, and no repair was made.
- `git diff --check inp...HEAD`: exit 2, inherited `docs/tracks/P/audits/P5-CH-audit-1.md:272: new blank line at EOF.` `git diff --check HEAD^ HEAD`: exit 0.
- Rotation SHA-256: `c5d877cff740f97b0b4aa4a98d1d0b8eb7ad2dfdfc6de903e601d984580c7ba7`.
- Signature input SHA-256: `24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`; design SHA-256: `04c358878699851e0e45adcccbfd06048e2474b6cffe015821df5e072f36fca3`.

## Declaration and node ledger

All Lean names below are in `KAM.Planetary`. Only `sb_rot` is public; every `sbRot_*` theorem is private. The complete five-row design assignment to Rotation is discharged. There is no unsigned public graph-node export.

| Node / obligation | Declaration and source line | Verdict | Reason |
|---|---|---|---|
| `bpP:p14:sb-rot` | `sb_rot`, 169 | PASS | Literal signed telescope, both membership and exact Hamiltonian equality. |
| `stepP:p14:sb-rot-1` | `sbRot_mem`, 39 | PASS | Gamma, fast actions and axes unchanged; all five region clauses transported. Stronger: no saturn-interval premise. |
| `stepP:p14:sb-rot-2` | `sbRot_moving`, 65 | PASS | All terms of the full moving Hamiltonian preserved by body-vector rotations. `hq`/`hp` describe the rotated input, not an assumed energy identity; constructed from covariance at use. |
| `stepP:p14:sb-rot-3` | `sbRot_explicit`, 73 | PASS | Literal integrand at rotated w equals original at F−theta in both coordinates; Jacobian product retained. Stronger: all masses, mu, w, F. |
| `stepP:p14:sb-rot-4` | `sbRot_box_shift`, 104; `sbRot_pi_shift`, 123; `sb_rot`, 174–184 | PASS | Continuity supplies genuine compact-box integrability for Fubini; periodic translations applied twice; pi-volume transported through measure-preserving finTwoArrow. |
| Fast block projection | `sbRot_fast_snd`, 34 | PASS | Literal unchanged action block. |
| Rotation linearity | `sbRot_rot_sub`, 53 | PASS | Coordinate polynomial identity. |
| Position projection | `sbRot_bodyVector_fst`, 56 | PASS | Literal frozen ellipsePhase/bodyVector indexing. |
| Momentum projection | `sbRot_bodyVector_snd`, 60 | PASS | Literal frozen ellipsePhase/bodyVector indexing. |
| Scalar periodic integral | `sbRot_interval_shift`, 90 | PASS | Exact interval substitution and periodic full-period equality, sign F−theta retained. |
| Closed-box integral bridge | `sbRot_Icc`, 97 | PASS | Icc/Ioc equality and positive interval orientation. |
| Frozen average bridge | `sbRot_exact`, 162 | PASS | Unfolds exactSecularHamiltonian/secularAverage and uses proved integrand identity; keeps `(2*pi)^(-2)` normalization and full integrand. |

The signed declaration text before `:=` is byte-identical to `/root/code/KAM-inp/.drafts/design/P14Signatures.lean:466–470` (direct extraction/comparison returned `True`). A scratch copy under a fresh name uses exactly `by exact sb_rot saturn mu hs hw theta`, and bidirectional `type_of%` assignments check elaborated telescope identity. There is no provider=frozen-type or anchor-seal-body probe to run for this ordinary helper package.

Consumer check: blueprint `stepP:p14:sb-fd-2` at p14b:243 needs theta ↦ H(w^theta) constant for each w in S. The exported equality quantifies over every real theta, with arbitrary mu and the standing saturn interval; membership is also available. No narrowing relative to the signed contract or unmet S7 source requirement was found. S7's independent derivative/chain-rule obligations are not claimed proved by S6.

## Definitions, assumptions and proof review

**New definition classification: none.** Rotation introduces no def, abbrev, structure, instance, fallback or replacement carrier. Local `let e` is the actual measurable equivalence `finTwoArrow`, not a surrogate integral or chart. Relevant imported bodies were checked: secularRotation rotates slow pairs while preserving fast data; sb_sdef uses the literal action/Gamma/axis inequalities; explicitSecularIntegrand is the full movingHamiltonian times both Jacobians. The frozen normalization, exact double average and ellipsePhase projections are preserved.

The covariance identities hold globally, including totalized division/sqrt points, and S6 only invokes continuity at w in S. No equality is obtained by silently treating the relevant integral as nonintegrable: `sbRot_box_shift` proves integrability on the compact product for both continuous functions. The scalar periodic helper is more general than needed, but the final invocation has the genuine continuous integrand. The proof neither drops indirect interactions nor substitutes a truncated Hamiltonian.

Static traversal of all project imports from Rotation visits 60 KAM modules and finds **zero frozen theorem modules and zero providers**. Thus no DRAFT_SORRY theorem import or quarantine issue arises; frozen definition imports are legitimate. No conclusion-shaped premise, hidden proof field, public helper-name reuse or root shadow is introduced.

## Independent validation

All Lean/Lake commands are serialized, under `LEAN_NUM_THREADS=1` and `nice -n 5`. The targeted build uses the required compile gate; the wait for a free slot is not treated as a failure. No resource override, clean, update, cache fetch, frozen edit or generated-root regeneration was performed.

### Targeted build

```text
env LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s6 KAM.Planetary.SecularBox.Rotation
[inp-gate] slot 3 acquired 19:58:09 for KAM.Planetary.SecularBox.Rotation
Build completed successfully (9106 jobs).
exit 0
```

### Signature, exact application and axioms

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S6Probe.lean
'KAM.Planetary.sb_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

No warnings or errors. The probe copied only the signed declaration, renamed it `s6AuditSigned`, proved it with `exact sb_rot saturn mu hs hw theta`, and checked both `example : type_of% @s6AuditSigned := @sb_rot` and its converse. It also printed the actual `sb_rot` proof body: the expected private membership, exact-integral and periodic-shift lemmas occur. No draft signature theorem was imported or admitted. This covers every new public theorem (one).

### Kernel replay

```text
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.Rotation
replaying KAM.Planetary.SecularBox.Rotation
exit 0
```

### Lint

```text
env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (905 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

This is the precise generated-root exception authorized by the audit brief. There are no other lint diagnostics. The generated file is left untouched.


Static checks: 188 lines, maximum line length 97 Unicode characters; no forbidden tokens, resource overrides or EuclideanSpace. Copyright, module declaration, public imports, module docstring and public section present. Only the namespaced `sb_rot` is newly public.

## Errata, deviations and limits

No suspected mathematical source defect or introduced mathematical deviation was found in the scoped S6 proof. The nonempty inherited protected-path diff and inherited whitespace issue are explicitly retained above. No code outside Rotation is certified by this audit. The existing untracked S6 handoff is preserved. This audit changes only this report; scratch probes are removed after validation.
