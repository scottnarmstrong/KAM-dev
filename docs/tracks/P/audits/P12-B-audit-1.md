# P12-B independent package audit

Overall verdict: **PASS WITH NOTES** for the scoped helper package `KAM.Planetary.PlanarAssembly.Boxes`. No blocking statement or proof defect found in Boxes.lean. Whole-tree hygiene does not pass: see N1 and the lint receipt. No frozen anchor is proved or seal-ready as a consequence of this package: provider/frozen-type and seal-body probes are inapplicable here because P12-B introduces no provider. P-PLANAR remains outside this audit.

Audit date: 2026-10-28. HEAD: `696f22e82dda8d20493b7c81236f2d2db096534f`; observed `inp`: `edcbb41e1257f22557319e7e7038488867953a93`. Scope follows the handoff's AUDIT FOCUS: **only Boxes.lean**. Read the package brief, AGENTS, PLAN, DECISIONS, track-P statement, relevant frozen predicate bodies and planar anchor, design revision 2, both design audits, the standalone signatures, and the relevant p7/p12 blueprint statements and proofs. The explicit user destination overrides the generic brief's MAIN-worktree destination. Only this report persists; no repairs or state-changing git operations.

## Comparison and qualifications

**N1 — Comparison contamination, nonblocking for this explicitly scoped audit.** `git diff inp...HEAD` reports two merge bases, selecting `3e1ba0afa6cce3ffdbbd50bcf58e4830557a799e`; the other is `1424468242d8358689f707ca21cc21b0f1a8c9dd`. The result has 18 files, 782 insertions and 103 deletions, including unrelated mechanical renames and 47 generated-root additions. Thus the brief's literal protected-path diff is **not empty**: `KAM.lean` differs. `KAM/Frozen`, `manifest` and `README.md` have empty diffs. The four actual P12-B commits `e7d3689`, `caa4dec`, `559b276`, `5e71a9e` collectively change only Boxes.lean (381 insertions); their protected-path diff is empty. HEAD additionally ports root-import name-clash renames. Do not interpret this report as auditing those unrelated changes or as certifying whole-branch protected-path compliance. The untracked handoff existed before the audit. Lint also reports generated-root DRAFT theorem/provider imports for AveragingMean/Most. The brief permits the stale-root line only; it does not waive these guard failures. Accordingly whole-tree hygiene is a FAIL, recorded separately from the explicitly scoped Boxes verdict. Do not use this report as unconditional branch/landing approval.

**N2 — Analytic inverse construction instruction not followed, nonblocking for the exact exported contract.** `docs/tracks/P/design/P1213-LEAN-DESIGN.md:174` says: “In P12-B, instantiate the identity/composition at this analytic order”; design audit 2 N3 expressly retains order `ω` followed by `.analyticAt`. `blueprint-P/parts/p12-planar-assembly.tex:27,60` states that the positive cube-root inverse is real analytic, hence C¹. Boxes.lean:305–310 uses `ContDiffAt.rpow_const_of_ne` directly at the order inferred from frozen `ContDiffOn ℝ 1`. It proves exactly the supplied `fast_diffeo` signature and the actual frozen `HasFastDiffeomorphism` predicate, whose inverse clause requires only C¹. There is no false analytic assertion or weakened public signature, but this proof does not implement the stronger analytic-order instruction or export inverse analyticity. Treat `bpP:p12:f-mono`'s analytic claim as a library fact used only at C¹ here, rather than as a new analytic export. If analytic inverse evidence is required for node closure, retain this qualification or provide that separate evidence. No code repair was authorized or performed.

## Declaration and node ledger

Prefix `PA = KAM.Planetary.PlanarAssembly`. PASS below concerns each listed declaration, not completion of the whole assembly.

| Node / role | Declaration (Boxes.lean line) | Verdict | Reason |
|---|---|---|---|
| `bpP:p12:data` D8 | `PA.secular_radius` (322) | PASS | Literal `min rG (sqrt (δ/2))/2`; same total real carrier and formula. |
| `bpP:p12:data` D9 | `PA.coupling_threshold` (324) | PASS | Literal `min 1 (r^6/(log(1/r))^c)`; no hidden coupling dependence. |
| `bpP:p12:data` D8–D9; arithmetic in `p12:quantifiers` | `PA.radius_choices` (326) | PASS | Exact telescope, all strict positivity and upper bounds, `2*r² ≤ δ/2`, threshold before arbitrary μ. Whole assembly witness selection remains downstream. |
| `stepP:p12:pg-h4` restriction | `PA.birkhoff_mono_radius` (362) | PASS | Exact frozen predicate, same P/P0/Ω/β and V/μ0; restricts integrability discs and epsilon-delta remainder using `min δ r`. No new jet assumption. |
| `bpP:p12:collar` | `PA.collar` (68) | PASS | Full two-sided frontier collar, Pi max-distance, exact `4*(L0+L1)*t`, all half-width guards retained. |
| `stepP:p12:co-inc` | private `collar_subset` (50), consumed by `PA.collar` | PASS | Expanded open box minus contracted closed box contains the full collar. Boundary identity is proved, not assumed. |
| `stepP:p12:co-meas` | `PA.collar` (80–93) | PASS | Finite inner volume, measurable subtraction and product interval volumes justify the exact shell-volume arithmetic. |
| `bpP:p7:product-chart` (b), design note 8 | `PA.product_chart` (181) | PASS | Complete joint signature: analytic h, exact frequency and gradient, all Hessian entries including zero cross terms and nonzero diagonal, total hProd decoupling and guarded actual chart identity. |
| `bpP:p12:fast-diffeo` | `PA.fast_diffeo` (266) | PASS | Exact frozen smooth-inverse contract, correct reversed frequency endpoints and cube-root inverse on positive frequencies. |
| `stepP:p12:fd-an` | `PA.fast_diffeo`, `PA.product_chart` | PASS | Analytic h on the positive box and actual fderiv-based frequency identification. |
| `stepP:p12:fd-open` | local `himg` (290) | PASS | Both image inclusions proved; open image is the product of `(c/u³,c/l³)`. |
| `stepP:p12:fd-inv` | local `g`, `hback`, final inverse clauses | PASS | Both inverse identities, image-to-box membership and C¹ on the image proved with positivity guards. See N2 for the stronger construction instruction. |
| `bpP:p12:f-mono` | radius log/power positivity; Mathlib real-power smoothness | PASS WITH NOTES | Positivity is proved on `0<r<1`; positive cube roots used at C¹. No standalone analytic inverse export; N2. |

All five public theorem headers and both public definition bodies were mechanically compared with `/root/code/KAM-inp/.drafts/design/P1213Signatures.lean`: **byte-identical** in every case. A fresh no-sorry probe copies the five signature statements under fresh names and closes each by the delivered theorem applied to the original explicit binders in order. No added premise, shifted quantifier, carrier, norm, normalizer, constant dependence or conclusion strength was found.

`hn : 0<n` in `product_chart` and `hc : 0<c` in `radius_choices` are literally present in the signatures. Both proofs retain them but do not need them. They do not make the results vacuous: positive dimensions, masses, κ, boxes, radii and δ have ordinary realizations. The product derivatives hold even in dimension zero; positive-base real powers remain positive for every real exponent. These unused standing assumptions conceal no conclusion-shaped premise. The Birkhoff-form input is appropriate to an explicitly named restriction lemma, not a substitute proof of the source expansion.

## Definition classification and proof review

- Public `secular_radius`: intended explicit arithmetic object on all real inputs. Square root uses the ordinary total real operation; only positive δ/rG enters its theorem.
- Public `coupling_threshold`: intended explicit total real-power/log/division formula. Zero or nonpositive inputs outside the guarded theorem are never used for positivity or smallness.
- Private `kepEnergy` (102): literal finite negative reciprocal-square sum on the whole carrier, with Lean's standard total division at zero. `kepler_h_eq` proves equality with the imported hProd restriction **globally**, not just on the analytic locus. Analytic/derivative uses require every relevant coordinate nonzero, derived from positivity. No fabricated fallback or alternative Hamiltonian.
- No new abbrev, structure, instance or choice-based definition. Local `box` and `g` are the actual box and explicit coordinate cube-root inverse; outside-image values of g are irrelevant to the frozen guarded contract.

The derivative proof differentiates the finite sum, identifies actual fderiv projections, and obtains the vector frequency derivative from an equality on an open positive neighborhood. This avoids relying on total fderiv values outside differentiability. The Hessian's off-diagonal entries and nonzero diagonal are explicitly proved. `keplerPart_poincareProd` supplies the actual product-chart physical identity. The collar proof uses measurable finite shell volumes rather than assuming collar measurability. Radius restriction preserves the exact remainder and integrability clauses of the frozen predicate.

## Hygiene and independent validation

All Lean/Lake invocations below use `LEAN_NUM_THREADS=1`; build, probe, replay and lint are serialized. The build uses the prescribed compile gate and its internal `nice -n 5 lake build`. No heartbeat/recursion/synthesis override, no cache reset or dependency mutation.

1. Targeted gate build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p12b KAM.Planetary.PlanarAssembly.Boxes
```

Exit **0**. Output includes `[inp-gate] slot 2 acquired 13:57:36 for KAM.Planetary.PlanarAssembly.Boxes` and `Build completed successfully (9116 jobs).` No Boxes warnings. Replayed upstream unused-variable warnings: `KAM/Kepler/Energy.lean:106` (hm,hκ), `KAM/Planetary/Poincare/Chart.lean:212,247` (hm,hκ), `KAM/Kepler/Mass.lean:147,157,500,524` (hκ,hκ,hw,hm/hκ). These are not package proof escapes or default-heartbeat failures.

2. Fresh exact-signature probe and axioms:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P12BAudit.lean
```

Final exit **0**. Each complete signature was compared byte-for-byte through the actual proof delimiter, then copied under a fresh theorem name with its delivered proof application. Exact axiom output:

```text
'KAM.Planetary.PlanarAssembly.collar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.product_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.fast_diffeo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.radius_choices' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.PlanarAssembly.birkhoff_mono_radius' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The initial audit-generated probe exited 1 because its extraction script stopped at `:=` inside named arguments / a let-binding. The extraction was corrected to use `:= by` / `:= sorry`, complete headers were re-compared, and the final probe above passed. This was an auditor scratch-generation error, not a package failure.

3. Kernel replay, single invocation:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarAssembly.Boxes
```

Exit **0**, exact output:

```text
replaying KAM.Planetary.PlanarAssembly.Boxes
```

There is no provider module; Boxes is the sole audited lemma module.

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**. Exact output (in order):

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (699 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD FAILED:
- nekhoroshev.d28.averaging_mean.v1: DRAFT_SORRY imported directly or transitively outside explicit frozen/audit allowlist: KAM.lean
- nekhoroshev.d28.averaging_mean.v1: DRAFT provider imported directly or transitively outside its provider and frozen anchor: KAM.lean
- nekhoroshev.d28.averaging_most.v1: DRAFT_SORRY imported directly or transitively outside explicit frozen/audit allowlist: KAM.lean
- nekhoroshev.d28.averaging_most.v1: DRAFT provider imported directly or transitively outside its provider and frozen anchor: KAM.lean
ABI HASHES OK (144 frozen declarations)
```

Only the first line is the brief's expressly permitted lint exception. The four generated-root guard failures are additional actual hygiene failures (N1); none names Boxes.lean, whose recursive import closure contains neither provider nor frozen theorem. This agrees with the handoff's reported root quarantine problem, but that receipt does not waive the guard. The generated root was not edited or regenerated.

5. `git diff --check`: exit **0**, no output. The audit-owned `.lake/abi-scratch/P12BAudit.lean` was deleted after validation. Final status contains only the new report and the pre-existing untracked handoff; tracked worktree files remain unchanged. Report whitespace and absence of pending placeholders checked at closeout.

Static source checks: 381 lines; correct copyright, `module`, public imports, module docstring, exposed public section; no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option` token. Seven new public declarations inventoried above; repository name search found other short names `collar` and `product_chart` only in different namespaces, no duplicate fully qualified name. The 70-module KAM import closure contains **no provider and no frozen theorem module**, hence no DRAFT_SORRY import or SEALED-state dependency needs exemption. Frozen definition imports are literal intended predicates.

Input SHA256:

```text
Boxes.lean b97ad9ea2547b186e1aaf0f9a719f3487e2ba7a0d75247473ac7de64672083a7
P1213Signatures.lean 1c09a31d1e920153f88136ea4e5fe8998c19e6e63e99ac711b3defd1cc53b447
P1213-LEAN-DESIGN.md da905471b106707950e1de2c433228a74a967117f81e07cd767a1c7ffea05768
```

## Errata, deviations and limits

No suspected defect in a pinned mathematical source or contradiction of the mathematical blueprint was found. N2 is a mismatch with a stronger proof-construction instruction, not a false source claim. N1 records the actual branch comparison rather than silently replacing its base. No audit-introduced implementation deviation. The stronger global hProd identity and zero cross-Hessian entries are legitimate strengthening, not different models. P12-A, other packages in the broad diff, P-G, canonical Birkhoff/jet construction, and eventual planetary anchor sealing are not independently re-audited or certified here.
