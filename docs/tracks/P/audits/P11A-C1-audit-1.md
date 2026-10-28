# P11A-C1 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the scoped Fourier-cutoff package. No mathematical defect, added source premise, changed constant, or design-signature mismatch was found. The notes concern the public interface, the declared module split, and the permitted stale generated root. This package does not seal a frozen anchor.

## Scope and authority

Audit date: 2026-10-28. Worktree and report destination: `/root/code/KAM-inp-p11ac1`. The user's exact destination overrides the generic brief's main-worktree output instruction.

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/P/audits/P11A-C1-handoff.md`. Audited only `KAM/Planetary/MaximalStep/FourierCutoff*.lean`, as the handoff requires. Read the C1 row and proof obligations in `docs/tracks/P/design/P11A-LEAN-DESIGN.md`, all three design-audit reports (the accepted R3 disposition supersedes earlier design findings), `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` L229–238, `blueprint-P/parts/p11a2-cutoff-step.tex` L22–67, and the track-P statement conventions. Inspected C0 definitions and the exact existing analytic/lattice inputs used here.

Snapshot:

```text
HEAD       15178250343ac8650db4995cd6aaa29f55a612e5
inp        05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2
merge-base 05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2
inp-p11ac0 75c5ae1e02ad39f69589ff5acbaebb6c2c9cf4d8
```

`git diff inp...HEAD` contains exactly the three scoped new Lean files: FourierCutoff 243 lines, FourierCutoffCoeff 125 lines, FourierCutoffTail 269 lines (637 total). Also compared `git diff inp-p11ac0...HEAD -- KAM/Planetary/MaximalStep/FourierCutoff*.lean`; all three are new there as well. The unrestricted comparison with the older C0 branch includes unrelated campaign changes, which are outside this audit. The handoff file was already untracked at entry.

The supplied design-signature SHA-256 is `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092`, matching the accepted R3 signature snapshot.

## Anchor disposition

| Anchor / package export | Verdict | Meaning |
|---|---|---|
| P11A-C1 / `KAM.Planetary.fourier_cutoff` | PASS WITH NOTES | Exact C1 design type; proofs and helper declarations checked below. Infrastructure acceptance only. |
| Downstream P-FIXED / `KAM.Planetary.fixedSunPlanetaryKAM` | FROZEN_UNPROVED; no seal-ready verdict | Manifest state remains `DRAFT_SORRY`; frozen body is `by sorry`. C1 neither claims nor supplies this provider. |

Provider/frozen ABI matching and an actual frozen seal-body probe are **not applicable**: no provider is introduced. Instead, the exact C1 signature was copied under a fresh name and proved by applying the export to every explicit binder in order; the corresponding exact-type probe passed.

## Node and declaration ledger

Names below are in `KAM.Planetary`; private names are identified by their source spelling. T = FourierCutoffTail, C = FourierCutoffCoeff, F = FourierCutoff.

| Node / role | Declaration and location | Verdict | Reason |
|---|---|---|---|
| fc-const | `p11C_ge_one`, T:28 | PASS | Same explicit constant; handles n=1, n=2, n≥3 without changing the base or exponent. |
| fc-poly / geometric series | private `tsum_geom_tail`, T:54 | PASS | Proves summability and exact tail q^j0/(1−q), with 0≤q<1. |
| fc-assemble / algebra | private `assemble_ineq`, T:76 | PASS | Positive d, n≥1; pays d powers and replaces n−1 by n only in the upper constant. |
| fc-count, fc-poly, fc-assemble | private `sum_tail_finset_le`, T:134 | PASS | Finite shell decomposition and uniform finite-sum bound; correct strict tail j>T. |
| fc-assemble | `p11_tail_le`, T:260 | PASS | Same c_n(1+d^(−n))exp(−πTd); no integrality restriction on T or d≤1 premise. |
| Joint parameter transport | `p11ParamEquiv`, C:29 | PASS | Genuine complex continuous linear equivalence between two n-blocks and an (n+n)-vector. |
| Integration carrier | private `cube`, C:34 | PASS | Literal closed unit cube [0,1]^n with existing Lebesgue measure. |
| Real-angle inclusion | private `continuous_realPt`, C:36 | PASS | Coordinatewise real-to-complex inclusion is continuous. |
| Parameter embedding | private `lin`, C:41 | PASS | Inserts the two parameter blocks as action and family parameter, with zero angle component. |
| Slice embedding | private `emb`, C:46 | PASS | Adds the fixed real-angle point to that linear embedding. |
| Transport identity | private `emb_E`, C:49 | PASS | Exact block identity, no norm identification or rescaling. |
| Integrand | private `cG`, C:54 | PASS | Character at −k times the actual family slice. |
| Joint coefficient holomorphy | `coeff_joint_differentiableOn`, C:58 | PASS | Requires only open B, positive angular radius and joint holomorphy; does not assume the desired coefficient regularity. |
| Fourier coefficient | private `cf`, F:33 | PASS | Existing torus coefficient at fixed action and parameter, independent of the supplied angle. |
| fc-decay / finite support | private `p11Cut_eq_sum`, F:37 | PASS | Exact finite sum over cutoff box, filtered by l1 modeSize≤T; holds for arbitrary total F and T. |
| Domain identification | private `norm_lt_of_mem_polyNbhd`, F:50 | PASS | polyNbhd {0} s implies actual Pi norm bound. |
| Domain identification | private `mem_polyNbhd_of_norm_lt`, F:56 | PASS | Reverse implication uses the literal center 0. |
| fc-decay / reality | private `modeSize_neg`, F:59 | PASS | l1 cutoff invariant under k↦−k. |
| fc-decay / slice hypotheses | private `slice_facts`, F:64 | PASS | Derives holomorphy, local periodicity and M bound from the family hypotheses on its domain. |
| fc-decay, fc-tail | private `cutoff_tail`, F:78 | PASS | Full-radius decay, actual Fourier reconstruction, explicit summable tail and the proved lattice bound. |
| fourier-cutoff | `fourier_cutoff`, F:143 | PASS WITH NOTES | Verbatim design signature; all conjunctions proved, including joint holomorphy, real slice and entire angle slices. See interface note below. |

## Statement and proof audit

A text extraction of the complete theorem header through its conclusion, excluding the proof body, returned `EXACT SIGNATURE TEXT MATCH: True` against the supplied signature L229–238. No binder, order, guard, bound, norm, or constant dependence changes.

The explicit source premises are n≥1, r>0, s>0, T≥0, 0<d<r, open B, admissibility, M≥0, and the pointwise M bound. The remaining binders supply types and data. Admissibility unfolds to joint holomorphy and on-domain angle periodicity. No field or instance conceals a cutoff, reconstruction, convergence, coefficient estimate, or output regularity assumption. M is an arbitrary certified bound; no unguarded supremum is substituted. The unused `hs` is retained from the exact signature.

Independent proof reconstruction:

- `slice_facts` restricts the joint family to fixed action/parameter. `KAM.decay_boundary_radius` (Bridges:401) gives decay at r with exactly exp(−2πr|k|₁), and `KAM.eq_fourierSumVec_torusCoeffW` (FourierSeriesVector:348) reconstructs the actual function at the interior point. Both existing statements require precisely the established slice premises.
- `norm_character_le` pays exp(2π(r−d)|k|₁). Their product is exp(−2πd|k|₁). Summability is supplied by `exp_sums`; the proof uses a legitimate summable series subtraction and a separately summable nonnegative tail, rather than exploiting the totalized value of a divergent tsum.
- `sum_tail_finset_le` groups any finite set by the integer l1 size. T≥0 excludes the zero shell. `card_l1Sphere_le` (Lattice:124) is the direct finset corollary of `lattice_count` (Lattice:109), not a replacement counting hypothesis. `exp_sums` bounds j^(n−1)exp(−πdj), including n=1 with natural exponent zero. j0=floor(T)+1 handles T=0 and noninteger T correctly.
- The geometric factor is bounded by exp(−πTd)(1+1/(πd)); `assemble_ineq` absorbs the inverse powers into c_n(1+d^(−n)). There is no restriction d≤1. `p11_tail_le` follows from bounds on every finite sum, with the nonnegative bound proved explicitly.
- The finite cutoff proves holomorphy jointly through the parametric-integral helper. That helper checks compact integration carrier, open parameter domain, joint continuity, actual derivatives and derivative continuity using finite-dimensional holomorphic regularity. The transport equivalence need not be an isometry: no norm bound is transported through it.
- Periodicity uses the period-one characters. Reality uses conjugate coefficient symmetry and the bijection k↦−k of the symmetric finite cutoff. Entire angle dependence follows from an actual finite character sum, including at angles outside the original strip. The cutoff bound is the original bound plus the tail bound.

## Definitions and whole-carrier behavior

All six new definitions/abbreviations are literal constructions; there are no new structures or output-choice definitions.

| Definition | Classification and whole-carrier conclusion |
|---|---|
| `p11ParamEquiv` | Literal block-concatenation equivalence, defined for every n including zero; no fallback. |
| private `cube` | Literal unit cube, including the standard empty-coordinate product for n=0. |
| private `lin` | Literal continuous linear map, selecting both inverse-equivalence blocks into the intended family coordinates. |
| private `emb` | Literal affine embedding with real angles and actual action/parameter blocks. |
| private `cG` | Literal Fourier integrand for every F, k, x and parameter vector. |
| private `cf` | Literal existing torus coefficient on all total inputs. Its integral has Lean's usual total semantics, but every analytic use is on a continuous real-angle slice; no nonintegrable fallback is used to prove a conclusion. |

For all six: BODY_MATCH=OK; PUBLIC_CARRIER=OK; DEFINITION_VERDICT=PASS. No characterization, choice-independence, or default-branch obligation arises. The private finite-sum identity itself works for arbitrary coefficients without an integrability premise; subsequent analytic coefficient facts use their actual regularity guards.

## Notes and suspected defects

1. **Public interface limitation, inherited from accepted design.** Blueprint p11a2:45 says the cutoff is “a trigonometric polynomial of degree ≤T”; p11a2:26 defines that as F=cut_T F. The accepted signature exports estimates, admissibility, reality and entire slices, but no separate `p11Cut T (p11Cut T F)=p11Cut T F` conclusion. F:37–47 proves a private finite sum with exactly the right support, so the underlying mathematical finite-support claim is implemented. A downstream caller needing polynomial idempotence must still obtain a public companion; this audit does not certify such a companion exists. No claim that the exact design type was fully strengthened to the vector-valued blueprint statement is made: the accepted export is scalar and may be applied componentwise.
2. **Declared implementation split.** The single planned module is split into three focused modules, with the main module publicly importing the helpers. This is sound and under the hard size cap; proof-step names in the design map correspond to the actual helpers/blocks in the ledger rather than literal local names `fc_const`, etc. No import cycle or forbidden preparation dependency is introduced. C0's inherited WeakMeasure/Basic carrier dependency remains outside this delta, as recorded in its earlier audit.
3. **Lint exception and routine warnings.** The generated root is stale, expressly allowed by the audit brief. The build reports deprecated `if_pos`/`if_neg` uses and the unused source binder `hs`. These do not change the theorem or use a resource override.

Suspected new mathematical blueprint/source errata: **none** in the scoped proof. The interface omission in note 1 is an exact locator/quote for the orchestrator, not an assertion that the Fourier-cutoff theorem is false. No source repair was introduced. Deviation: the handoff-declared Tail/Coeff module split only.

## Independent checks

All completed Lean/Lake checks below were run serially with `LEAN_NUM_THREADS=1` and `nice -n 5`. No heartbeat, recursion-depth or synthesis-budget override was used. The targeted build waited for the prescribed compile gate; no clean, update, cache fetch or full-library build was requested.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ac1 KAM.Planetary.MaximalStep.FourierCutoff
```

Exit **0**. Receipt: `[inp-gate] slot 2 acquired 11:03:49 for KAM.Planetary.MaximalStep.FourierCutoff`; `Build completed successfully (9095 jobs).` The output replayed cached scoped targets. Warnings: deprecated `if_pos`/`if_neg` in Tail L71,177,179,206,207 and FourierCutoff L136,169,181,224,229,238,240; unused `hs` at FourierCutoff L144. No errors or sorry warnings.

### Exact-type/application probe and axioms

The disposable `.lake/abi-scratch/P11AC1Audit.lean` imports the main module, copies the delivered `fourier_cutoff` type under `audit_fourier_cutoff`, and closes it with:

```lean
exact fourier_cutoff hn hr hs hT hd hdr hB hF hM hb
```

It also elaborates:

```lean
example : type_of% @audit_fourier_cutoff := @fourier_cutoff
```

Command: `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AC1Audit.lean`; exit **0**, no warnings. The extracted source header was byte-identical to the delivered design header. Axiom output for every new public theorem and the public definition:

```text
'KAM.Planetary.p11C_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.coeff_joint_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fourier_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11ParamEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.MaximalStep.FourierCutoff KAM.Planetary.MaximalStep.FourierCutoffTail KAM.Planetary.MaximalStep.FourierCutoffCoeff
```

Exit **0**, one invocation covering all three scoped modules. Complete output:

```text
replaying KAM.Planetary.MaximalStep.FourierCutoffCoeff
replaying KAM.Planetary.MaximalStep.FourierCutoffTail
replaying KAM.Planetary.MaximalStep.FourierCutoff
```

### Hygiene and imports

Code-mask scan of the three files: no forbidden proof escapes, `EuclideanSpace`, or resource overrides. All files have copyright/license/authors, `module`, public imports, module docstring, and `@[expose] public noncomputable section`; lengths are 243/125/269. No file reaches 1500 lines.

Traversed all 49 transitive KAM modules from the main module: **no provider imports and no frozen theorem-module imports**, hence no imported `DRAFT_SORRY` theorem anchor or manifest-state exception. Frozen definitions, including the actual `Phase`, are used. `MaximalStep` introduces no `Preparation` import.

Command: `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh`; exit **1**, exclusively the brief-permitted generated-root staleness. Complete diagnostic output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (554 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No generated root was regenerated. An earlier lint attempt was stopped during its static guard phase, before ABI elaboration, to keep subsequent Lean checks serial; the complete receipt above is the fresh run after kernel replay.

## Integrity and closeout

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. `git diff --check` exits **0**. The report also passes an explicit trailing-whitespace and balanced-fence check, since it is untracked.

The scoped source hashes remained unchanged across the audit:

```text
abfd25b761c654710e2f92a4501b32a40ecc9df4bcc63812147a0cbf62a69b5d  FourierCutoff.lean
3d9873760ef33824b507c738478abb3231fad07edb272ab3778ac9005679adee  FourierCutoffCoeff.lean
dd180f325c7693b9eb7e80a9352f264a6318ddcf2433c062b6eede6de66d0670  FourierCutoffTail.lean
```

The audit probe and replay log were deleted from `.lake/abi-scratch/` after recording their results. No production module, frozen file, manifest, generated file, handoff, or git state was edited. Final status adds only this report alongside the pre-existing untracked handoff. No state-changing git command was run.

Closeout: **PASS WITH NOTES for C1**; no open mathematical refutation in scope. The public polynomial-idempotence companion remains the interface limitation identified above. No frozen root/provider closure is claimed.
