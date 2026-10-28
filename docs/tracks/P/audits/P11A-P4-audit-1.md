# P11A-P4 independent package audit 1

Overall verdict: **PASS WITH NOTES** for `KAM.Planetary.aniso_avg` (`bpP:p11:aniso-avg`). No mathematical or signature blocker found. Notes: the proof uses a valid alternative to the scheduled rectangular-flow adaptation; two new lines have trailing whitespace; the generated root is stale. This is an infrastructure package, with **no frozen theorem anchor or provider to seal**. It does not establish P-FIXED or any physical headline.

## Scope and authority

Audited only `KAM/Planetary/Preparation/RectangularAverage*.lean`, as the handoff explicitly requires. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package brief at `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the supplied handoff, the P11A design row/mapping/signature, all three prior design-audit reports, track-P statements, blueprint-P p11 L120–142, relevant existing finite-iteration interfaces, and frozen definitions used by the package. The prior audits/signature were read from `/root/code/KAM-inp` where absent locally. The user's exact report destination overrides the generic brief's main-worktree destination.

Snapshot: HEAD `9c065f8e02c204759e8d8efb8236ee776199e632`; comparison `inp` resolved to `e5df64700d49778f5a16b13c87fb6e7a5237ea4d`. `git diff inp...HEAD` warns of multiple merge bases and selects `11b7d6c7fc53ca5674e2a8439d2cdf0f54f3919c`; the other is `3049422e5f5ff56779edc93953d48ccdb9123f77`. Reviewed the requested comparison, retaining this ambiguity. Its 11 changed files include inherited C6/Affine work; those are outside this audit's four-file scope. The handoff was already untracked when work began.

Delivered signature: `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`, SHA-256 `ffc0ddcad44661d4eeffd7d5bf0900e393ae23a3217c2dfc6edcabb89245fc15`. Extracted the complete `aniso_avg` declaration through its type: it equals the implementation's declaration after removing whitespace. The signature was also independently elaborated under a fresh theorem name with body

```lean
by exact aniso_avg hr1 hr2 hs hT hk ha ha' hh hf hp hrealh hrealf hE hb hsmall hdiv
```

and the reverse check `example : type_of% @aniso_avg := @audit_aniso_signature` passed. There are no other P4 declarations in the design signature. The frozen-provider equality and seal-copy tests are inapplicable because there is no provider/frozen anchor here; this fresh-name signature test verifies the actual package contract without introducing a draft-sorry dependency.

## Proof and statement review

The output has the same joint witnesses Psi, g, fs for holomorphy, injectivity, canonicality, translation, reality, image containment, Hamiltonian identity, remainder decay, both zero-mode correction bounds, and separate block displacements. It preserves all source-local hypotheses, full-box divisor data, the period-one factors `2*pi`, the max-norm Pi carriers, and dependence on `min r1 r2`. A complex centre is allowed, stronger than the blueprint's real centre. E is a nonnegative upper bound rather than an equality with the norm; this is a valid stronger form. No output or hard analytic step was smuggled into the main hypotheses.

The replacement proof is sound: let m = min r1 r2 and D be the closed polydisc with coordinate radii r_j - m. `polyNbhd_avgBase_subset` proves V_m(D) is contained in the original box, sufficient for every input premise. `box_half_subset` uses coordinate clamping to prove the entire requested half box is contained in V_(m/2)(D). Consequently restriction of the existing arbitrary-complex-base finite iteration gives all requested output clauses. The docstrings say the full neighbourhood equals the box; only the two sufficient inclusions are formally exported, and no unproved equality is used. This works also for zero-sized blocks and does not assume the complex centre is real.

`P11AvgHyp` is a bundle of analytic, reality, periodicity, divisor and numerical input premises. `P11GoodSched` describes an intermediate schedule, but existence of that schedule is proved by `p11_goodSched_single/multi/of_avg`, never assumed by `aniso_avg`. `p11_setup_of_avg` is explicitly a conditional adapter: its numerical recurrence premise is discharged in both schedule constructors. The finite core invokes the proved `step_conc`, `inv_all`, `finite_struct`, `finite_ident`, `finite_disp`, and `gen_tail`. The latter controls the literal `g - coeff f _ 0`, not a replacement zero mode.

In Case A, `p11_step_first_quad` proves the first bound with E1 = 2(E/Q)E, Q = 2*pi*alpha2*(m/8)*(s/6). `p11Eps` retains this quadratic first remainder, then decays geometrically. The schedule proves the recurrence for this smaller sequence; it does not merely reuse a recurrence for an unrelated larger sequence. The tail sum is at most (4/3)E1 = 128 E^2/(2*pi*alpha2*m*s). `p11_nfb_core` exports 128; the facade relaxes it to 130 using E^2 >= 0 and a positive denominator. Case B has one transformation and g equal to the original zero mode, so both correction bounds follow from the empty tail sum. Splitting cases is exhaustive, including E = 0.

**Proof-plan deviation:** design L724 lists P3,C6 and blueprint p11 L140 describes R1–R3 blockwise losses. The implementation imports P3 via `RectangularAverageDomain` for `p11Box`/`p11WBound`; it does not invoke `aniso_bracket`/`aniso_field` or C6 `AffineFlow`. It reuses the general nonlinear P2/N finite iteration on D instead. This is sufficient for the exact output and avoids needing an affine generator for a general averaging function. Record the alternate route in the campaign dependency/proof-plan bookkeeping; do not claim those planned adapters were exercised. There is no `p11Affine` redefinition in the four audited files; its unique production definition remains `MaximalStep/Affine.lean:24`. P4 does not use it, so no explicit P4 affine import is needed.

## Declaration ledger

All names below are in `KAM.Planetary`. Locations are relative to `KAM/Planetary/Preparation/`. Each public named declaration has its own row; local source steps are also listed explicitly.

| Node / role | Declaration and location | Verdict | Reason |
|---|---|---|---|
| bpP:p11:aniso-avg | `aniso_avg`, RectangularAverage:28 | PASS WITH NOTES | Exact signature; proved by restriction; alternate route and whitespace notes. |
| stepP:p11:aa-same | Local construction in `aniso_avg`:77–106; `p11_nfb_core` | PASS WITH NOTES | Arbitrary complex base instead of scheduled blockwise flow adapters. |
| stepP:p11:aa-quad | Local bound transfer in `aniso_avg`:117–120 | PASS | Proved 128 bound implies 130 with positive denominator. |
| aa-same / input bundle | `P11AvgHyp`, RectangularAverageCore:33 | PASS | Source inputs only; classified below. |
| aa-same / schedule | `P11GoodSched`, Core:52 | PASS | Intermediate existential predicate, proved before use. |
| aa-quad / budget | `p11_E_le_kappa`, Core:72 | PASS | Algebraic restatement of smallness. |
| aa-quad / budget | `p11_y_le`, Core:82 | PASS | Divides by positive Q. |
| aa-same / adapter | `p11_setup_of_avg`, Core:91 | PASS | Conditional numerical adapter; all recurrence hypotheses discharged by callers. |
| aa-same / Case B | `p11_goodSched_single`, Core:113 | PASS | One step, doubled losses, empty correction tail. |
| aa-same / Case A | `p11_goodSched_multi`, Core:212 | PASS | Constructs finite schedule and proves recurrence, losses and sums. |
| aa-same / case split | `p11_goodSched_of_avg`, Core:361 | PASS | Exhaustive comparison with exponential threshold. |
| aa-same / finite core | `p11_nfb_core`, Core:369 | PASS | Joint iteration witnesses and both correction bounds. |
| aa-same / radius object | `p11Rad`, RectangularAverageDomain:26 | PASS | Literal block radii. |
| aa-same / box bridge | `p11Box_eq`, Domain:29 | PASS | Exact coordinate reformulation. |
| aa-same / radius minimum | `min_le_p11Rad`, Domain:34 | PASS | Coordinatewise minimum bound. |
| aa-same / base object | `p11AvgBase`, Domain:40 | PASS | Literal closed polydisc; no choice/default fallback. |
| aa-same / input inclusion | `polyNbhd_avgBase_subset`, Domain:43 | PASS | Triangle inequality, no extra positivity premises needed. |
| aa-same / clamp helper | `exists_clamp`, Domain:55 | PASS | Explicit radial clamp when needed; t >= 0 is typing geometry. |
| aa-same / output inclusion | `box_half_subset`, Domain:70 | PASS | Strict half-box inclusion by coordinate clamps. |
| aa-quad / first step | `p11_step_first_quad`, RectangularAverageEps:27 | PASS | Numerical first-step bound proved. |
| aa-quad / sequence | `p11Eps`, Eps:54 | PASS | Total geometric sequence with separate zeroth term. |
| aa-quad / initial term | `p11Eps_zero`, Eps:56 | PASS | Exact defining equation. |
| aa-quad / later terms | `p11Eps_succ`, Eps:58 | PASS | Exact defining equation. |
| aa-quad / positivity | `p11Eps_nonneg`, Eps:61 | PASS | From nonnegative E and E1. |
| aa-quad / comparison | `p11Eps_le`, Eps:66 | PASS | Pointwise upper comparison with existing multiEps. |
| aa-quad / weighted sum | `p11_multi_star`, Eps:73 | PASS | Nonnegative weights and head/tail estimates proved. |
| aa-quad / tail sum | `p11_multi_tail_sum`, Eps:146 | PASS | Geometric series bound for actual smaller sequence. |
| aa-same / action displacement | `p11_multi_disp_σ`, Eps:161 | PASS | Positive-denominator comparison with established displacement sum. |
| aa-same / angle displacement | `p11_multi_disp_ρ`, Eps:178 | PASS | Same comparison; no lower bound on E1 needed for this upper estimate. |

## Definition classification

Five new definitions/structures, all appropriate on their whole carriers:

- `P11AvgHyp`: source-premise Prop structure over arbitrary complex Dc. Fields assert inputs, not averaging outputs.
- `P11GoodSched`: explicit numerical/iteration schedule predicate. It is an intermediate target, with existence proved; it is not an added source assumption.
- `p11Rad`: Fin.append of the two supplied radii, including empty blocks and arbitrary real inputs.
- `p11AvgBase`: closed coordinate inequalities with radii r_j - min r1 r2; the radii are always nonnegative. No totalization trick.
- `p11Eps`: E at index zero and E1*(1/4)^(i-1) thereafter, for arbitrary real E/E1; positivity is a separate proved property under explicit guards.

No new abbrev, junk value, assumed choice specification or fallback is used.

## Independent hygiene checks

Every audit-owned Lean/Lake invocation ran serially, with `LEAN_NUM_THREADS=1` and `nice -n 5`. Lint was reserved until after kernel replay because its ABI check starts Lean internally. No clean/update/cache fetch, library-wide rebuild, provider change, frozen change or state-changing git command was run.

1. Targeted gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap4 KAM.Planetary.Preparation.RectangularAverage
```

Exit **0**. Output included `[inp-gate] slot 2 acquired 14:25:18 for KAM.Planetary.Preparation.RectangularAverage` and `Build completed successfully (9145 jobs).` One replayed upstream warning in `KAM/Planetary/Averaging/Finite.lean:160:5`: `Variable name hstrict is not explicitly referenced.` No warning in the four audited modules. The job count is the dependency graph count, not a clean rebuild.

2. Signature/axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP4Audit.lean
```

Exit **0**; both exact-type directions passed without warnings. For each of the following 22 theorems, the exact output was `'KAM.Planetary.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`:

```text
aniso_avg
p11_E_le_kappa
p11_y_le
p11_setup_of_avg
p11_goodSched_single
p11_goodSched_multi
p11_goodSched_of_avg
p11_nfb_core
p11Box_eq
min_le_p11Rad
polyNbhd_avgBase_subset
exists_clamp
box_half_subset
p11_step_first_quad
p11Eps_zero
p11Eps_succ
p11Eps_nonneg
p11Eps_le
p11_multi_star
p11_multi_tail_sum
p11_multi_disp_σ
p11_multi_disp_ρ
```

No `sorryAx`, extra axiom or unverified theorem enters these results.

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.RectangularAverage KAM.Planetary.Preparation.RectangularAverageCore KAM.Planetary.Preparation.RectangularAverageDomain KAM.Planetary.Preparation.RectangularAverageEps
```

Exit **0**. Exact verbose output:

```text
replaying KAM.Planetary.Preparation.RectangularAverageEps
replaying KAM.Planetary.Preparation.RectangularAverageDomain
replaying KAM.Planetary.Preparation.RectangularAverageCore
replaying KAM.Planetary.Preparation.RectangularAverage
```

4. Required source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the explicitly permitted stale generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (711 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Module checks, frozen-anchor guard and ABI hashes all passed. The generated file was not regenerated.

5. Static and import checks: no forbidden sorry/admit/axiom/unsafe/opaque/EuclideanSpace or resource options in the four files; correct copyright, module, public imports, module docstrings, exposed public noncomputable sections. Total file lengths: facade 133, Core 435, Domain 97, Eps 198, all below 1500. Scanned all 27 new named declarations against other production KAM files: no existing declaration-name collision.

Transitive production KAM import closure has 99 modules. It contains no provider or frozen theorem module; its 12 frozen imports are definitions, each manifest state SEALED: ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm, Planetary/Defs/Fast, Phase, Slow. No DRAFT_SORRY import or quarantine violation.

6. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty (apart from the multiple-merge-base warning), exit **0**. `git diff --check inp...HEAD`: exit **2**, exactly:

```text
KAM/Planetary/Preparation/RectangularAverage.lean:62: trailing whitespace.
+        (fun z : P11Phase (a+b)
KAM/Planetary/Preparation/RectangularAverage.lean:67: trailing whitespace.
+        2*Real.pi*alpha1*s*‖(fun i : Fin a
```

This is a minor formatting note; the read-only audit leaves it to the prover/orchestrator. It does not alter signature equality.

## Errata, deviations and limits

No new suspected pinned-source or blueprint mathematical defect found. Prior design audits' F1/F4 concerns are not reopened: periodicity is domain-local and the accepted P3 field theorem remains available, although this alternate proof does not need it. The main result's complex centre is stronger than p11 L131's real centre. The R1–R3 proof route at p11 L140 and design L724 is replaced as described above; this is an implementation deviation to report, not a source contradiction. The handoff's claim of no deviations should be read with this explicit proof-plan note.

No frozen statement was altered or refuted. Kernel/axiom evidence concerns the audited package and its imported proofs, not closure of the planetary campaign. The generated-root note and the two whitespace lines remain for integration cleanup. Only this report persists as an audit-authored repository artifact; temporary probes/logs are deleted after checks.
