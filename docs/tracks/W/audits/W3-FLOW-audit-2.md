# W3-FLOW independent package audit — round 2

Date: 2026-10-31. Target: `inp-w3flow` at **550bc8698736753e78b107ac7bc841bf23876af2**.

**Verdict: PASS WITH NOTES for the requested tight delta. F1, F2 and F3 are closed.**
No frozen anchor is sealed here; seal-readiness is inapplicable. Unchanged round-1 results were not
re-audited, and this report does not independently renew their checks.

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the round-1 report (F1–F3),
and the handoff's audit focus and Round 2 section. Applied the lean-statement-audit skill to
source fidelity, definition semantics, premises and concrete consumption. User D53 resource and
lint instructions supersede the generic brief's invocation details.

Inspected `git diff inp...HEAD` and the complete implementation delta
`git diff 686a1f84 550bc869 -- KAM/Wave/Birkhoff`: seven new modules and the refactoring of
`LieFlow2` (16 inserted / 4 removed lines). At inspection, `inp` resolved to
`710c4ce062bcf01918b77c4ccbe4c7a4fa06d824`; the target remains the exact commit above.
The handoff's `840a38c7` identifies the producer fix commit; target commit `550bc869` explicitly
records its transfer. This is provenance, not a second target.

Source: `blueprint-W/parts/w3-birkhoff.tex`, SHA256
`1e09a1eb1b06815116809f1f45e996b1ba79962ebfb755e3c75b797e5a19b161`;
lie-coeff lines 461–466, leibniz (iii) line 477, flow (i) lines 504–514.
Read the applicable `docs/tracks/W/W-STATEMENTS.md`; the generic brief's
`docs/tracks/W/statement.md` does not exist. These are off-frontier infrastructure results,
not manifested providers. Provider/type/seal probes are therefore inapplicable.

Only this report was edited in the tracked repository. Temporary probes were confined to
`.lake/abi-scratch/` and removed. No state-changing git command was used.

## Findings re-check

### F1 — CLOSED: all ordered inputs, literal slot recurrence

`LieSlot4:35–40` defines `lieContractFin` exactly: preserve entries before position i, replace
position i with T of the three consecutive entries, then read entry j+2 after i. The sum ranges
over all `Fin (2*k+1)` slots, and the input has `2*(k+1)+1` entries. This is the source's
one-based formula with zero-based indices, without permutation or symmetrization.

`lieMulti_slot` (`LieSlot4:42`) proves the source formula for every such input and every k,
with coefficient `1 / ((k : ℂ)+1)`. The existing base definition is evaluation of the unique
input at k=0. `lieMulti_unique` (`:63`) proves uniqueness among arbitrary families satisfying
this base case and recurrence; it does not assume symmetry or agreement only on a diagonal.

The bridge is substantive: `lieMulti_eq_lieMb` (`LieSlot1:92`) identifies the block coefficients
on every finite tuple with a sequence construction; `lieMb_congr` proves its locality.
`lieMb_slot` (`LieSlot3:145`) proves the sequence recurrence by strong induction. Its three
block contributions (`lieSlot_term`) retain ordered inputs; the antidiagonal reindexing weights
sum to j+1, and cancellation is only by a proved nonzero positive integer scalar.
The induction hypothesis is constructed inside the proof, not left as a source premise.
No symmetry of T is assumed. `birkLieMulti_slot` (`LieBirkC1:45`) applies this directly to
`birkT = ι ∘ S`, the source S read in W.

This pays the exact F1 invoice and removes the F1 qualification on identification of the
already constructed coefficients. It does not re-audit their unchanged norm or analyticity proofs.

### F2 — CLOSED: all-input multilinear reality

`lieMulti_rho` (`LieRealMulti:31`) quantifies over every ordered tuple of length `2*k+1`.
It assumes only compatibility of the trilinear map with the conjugate-linear isometry ρ.
The induction carries ρ through each ordered block, the finite sum and the scalar coefficient;
that coefficient is explicitly proved conjugation-invariant. There is no diagonal restriction.
`birkLieMulti_rho` (`LieBirkC1:37`) supplies compatibility using the existing `birkT_rho`.
Together with F1, this is reality for the source coefficients, not merely another family.

### F3 — CLOSED: joint C¹ on the source domain

`contDiffOn_lieGamma` (`LieFlow5:59`) concludes exactly
`ContDiffOn ℝ 1 (fun z : ℝ × E => lieGamma T z.1 z.2)` on
`{z | |z.1| < 2 ∧ 40*C*‖z.2‖^2 < 1}`.

The changed `LieFlow2` extracts the old local majorant proof as
`exists_lieTermD_majorant`; the public type of `hasFDerivAt_lieGamma` is unchanged and its
proof consumes that proved majorant. The open neighborhood, summability and uniform bound
are conclusions, not hypotheses. The construction keeps positive τ, radius and q0 even at
(t,w)=(0,0), and proves q0<1/10, so divisions and geometric summability remain justified.

`contDiff_lieSeq` proves smoothness from the multilinear diagonal representation;
`contDiff_lieTerm` gives real C¹ of each joint term, and `continuous_lieTermD` identifies its
actual Fréchet derivative. `continuousOn_tsum` gives operator-norm continuity of the derivative
sum on the local neighborhood. Intersecting with the open source domain, the proof supplies
both this continuity and `HasFDerivAt` at every point, using Mathlib's `contDiffAt_one_iff`.
This establishes joint C¹, including continuity of the derivative, rather than pointwise
joint differentiability or fixed-time spatial analyticity.

`birkGamma_contDiffOn` (`LieBirkC1:30`) supplies `norm_birkT_le` and proved positivity
`birkCF_pos`, without a new analytic premise. Since C_F>0, the radius condition is exactly
`‖w‖ < (40*C_F)^(-1/2)` from the source.

## Declaration verdicts

All declarations below are in `KAM.Wave`. Grouped rows enumerate auxiliary exports with the
same role; each is covered by the axiom probe.

| Node / role | Declaration(s) | Verdict | Reason |
|---|---|---|---|
| F1, sequence bridge | `lieMb_succ`, `lieMb_zero`, `lieMb_congr`, `lieMulti_eq_lieMb` | PASS | Finite ordered coefficient identification and locality. |
| F1, contraction indexing | `lieShift_contract_lt`, `lieShift_contract_ge`, `lieContract_apply_lt` | PASS | Literal before/at/after slot behavior. |
| F1, multilinear algebra | `lieMb_succ_G`, `T_sum_slot`, `T_smul_slot`, `T_sum0`, `T_sum1`, `T_sum2`, `T_smul0`, `T_smul1`, `T_smul2` | PASS | Explicit conditional algebra on continuous trilinear T. |
| F1, induction | `sum_antidiagonalTuple_succ`, `lieSlot_term`, `lieMb_slot` | PASS | Correct reindexing and internally discharged strong induction. |
| lie-coeff / F1 | `lieMulti_slot`, `lieMulti_unique`, `birkLieMulti_slot` | PASS | Source recurrence and uniqueness on all ordered inputs. |
| leibniz (iii) / F2 | `lieMulti_rho`, `birkLieMulti_rho` | PASS | All-input reality with actual concrete supplier. |
| flow (i) / F3, majorant extraction | `exists_lieTermD_majorant`, `hasFDerivAt_lieGamma` | PASS | Proved uniform majorant; derivative theorem's type preserved. |
| flow (i) / F3, term regularity | `contDiff_lieSeq`, `contDiff_lieTerm`, `continuous_lieTermD` | PASS | Continuity of the actual joint derivative of each term. |
| flow (i) / F3 | `contDiffOn_lieGamma`, `birkGamma_contDiffOn` | PASS | Joint real C¹ on the full source domain. |

## Expanded premise classification

Concrete source exports share the following typing and standing binders. No project-owned
assumption bundle hides further inputs. Counts describe distinct binder roles in this table.

| Binder | Bin | Authority / role |
|---|---|---|
| `m : ℝ` | TYPING | Source mass parameter. |
| `hm : 0 < m` | STANDING | w3 standing assumptions lines 22–26. |
| `a : ℝ` | TYPING | Weight parameter. |
| `ha : 0 ≤ a` | STANDING | Source weight convention. |
| `p : ℝ` | TYPING | Weight exponent. |
| `hp : 1/2 ≤ p` | STANDING | Source weight convention. |
| `k : ℕ` (slot/reality) | TYPING | Coefficient index, lie-coeff and leibniz. |
| `w : Fin (2*(k+1)+1) → BirkSpace` (slot) | TYPING | Arbitrary ordered source inputs. |
| `w : Fin (2*k+1) → BirkSpace` (reality) | TYPING | Arbitrary ordered source inputs. |

Counts: TYPING 6, STANDING 3, SOURCE 0, RULED 0, EXCESS 0. The C¹ theorem binds its time,
point and radius conditions inside the conclusion's domain, not as extra premises.

Abstract helpers additionally bind E, its normed additive group/complex normed space structure,
and, for the series, completeness (TYPING, source Banach carrier); T and the conjugate-linear
isometry ρ are TYPING data. The bounds `hC`, `hCp`, `hT` and reality compatibility are
conditional helper premises, concretely discharged by `birkCF_pos`, `norm_birkT_le` and
`birkT_rho`. No symmetry premise is required for the new slot result.
The parameters `j,a,b,c,v`, tuple index i, finite summation type/set/function, scalar c and
fixed slot entries in the algebraic helpers are TYPING; index equations and locality hypotheses
are internal reindexing/locality conditions. `LieSlotIH` expands to the recurrence strictly below
j+1; `lieMb_slot` constructs it by strong induction. The family Ψ and `h0,hs` in
`lieMulti_unique` are precisely the two defining premises of the uniqueness claim, not premises
of `lieMulti_slot` or a source conclusion.

## Definition classification

| New definition | Body / whole-carrier behavior | Verdict |
|---|---|---|
| `lieShift` | Literal shift of an arbitrary infinite sequence. | PASS |
| `lieContract` | Literal consecutive triple contraction for any natural slot. | PASS |
| `lieMb` | Well-founded finite block recursion reading a finite prefix; locality and equality with `lieMulti` proved. | PASS |
| `lieExt` | Auxiliary zero-extension of a finite tuple. Out-of-range entries never affect the equality: `lieMb_congr` proves locality. | PASS |
| `lieG` | Literal ordered trilinear block contribution. | PASS |
| `LieSlotIH` | Explicit internal induction predicate; discharged at the unconditional recurrence. | PASS as internal predicate |
| `lieContractFin` | Literal source contraction on every finite tuple and every admissible slot. | PASS |

For the source coefficient semantic unit `lieMulti` + `lieMulti_slot` + `lieMulti_unique`:
BODY_MATCH: OK (proved equivalence of the block construction to the literal source recursion);
PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: OK (existing finite continuous multilinear construction);
CHARACTERIZATION: OK (base identity, full recurrence and uniqueness);
CHOICE_INDEPENDENCE: N/A (no choice construction); DEFINITION_VERDICT: PASS.
No changed definition body in `LieFlow2`; no new choice, junk source value or deferred
source characterization. The unchanged totalized series remains certified only on its source domain.

## Verification

Every Lean/Lake invocation, including children of lint/build scripts, was enclosed in:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

Checks were serialized. No heartbeat override, clean build, application build, library rebuild,
cache fetch, or kernel replay was requested by this auditor. Kernel replay and name checks were
launcher-run according to the user; their output is unavailable here, so no exit code is invented.

1. Prescribed lint, under the prefix above:

   ```sh
   /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpfa
   ```

   Exit **0**, output:

   ```text
   check_lean_modules: PASS (3615 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
   ```

2. Targeted build, under the same prefix:

   ```sh
   /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpfa KAM.Wave.Birkhoff.LieBirkC1
   ```

   Exit **0**. Gate output:
   `[inp-gate] slot 1 acquired 22:43:10 for KAM.Wave.Birkhoff.LieBirkC1`.
   Final output: `Build completed successfully (3385 jobs).`
   Cached diagnostics included deprecated names and unused tactic/simp arguments; no build errors.
   Lake's “Replayed” messages refer to cached diagnostics, not a fresh leanchecker replay.
   This target imports all new modules and the changed `LieFlow2`; no broader build was run.

3. Scratch probe, under the same prefix:

   ```sh
   lake env lean .lake/abi-scratch/W3FlowAudit2.lean
   ```

   Exit **0**, no warnings or errors. Imported `KAM.Wave.Birkhoff.LieBirkC1` and printed
   axioms of all **31** theorem exports listed in the declaration table (29 new and the two
   `LieFlow2` exports). Every line had exactly:

   ```text
   'KAM.Wave.<declaration>' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   This includes `lieMulti_slot`, `lieMulti_unique`, `lieMulti_rho`, `contDiffOn_lieGamma`,
   all three concrete exports, `exists_lieTermD_majorant` and `hasFDerivAt_lieGamma`.
   The probe also elaborated the k=0 identity and exact independently written types of the
   concrete all-input recurrence, all-input reality and joint C¹ results, using the public
   exports directly. Hence concrete specialization has no hidden proof obligation.
   Probe removed after completion.

4. Read-only hygiene:

   - `git diff --check 686a1f84 550bc869`: exit **0**, no output.
   - `git diff --check`: exit **0**, no output.
   - `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty.
   - The generated `KAM/Root/Wave.lean` change adds the Lie imports; no audit edit to it.
   - No forbidden proof escape or option override in the eight inspected modules.
   - All have copyright, `module`, public imports, module documentation and public sections;
     new definitions are exposed. Largest delta module is `LieSlot3`, **230 total lines**.

## Notes, uncertainty and errata

No new mathematical source defect, excess concrete premise or implementation deviation was found.
The new F1 bridge is stronger than the minimum needed: it requires neither symmetry of T nor
multilinearity of the competing family in the uniqueness theorem. These strengthenings are sound.
`lieExt`'s auxiliary zero branch is insulated by proved finite-prefix locality and is not a fallback
for a source object. No new source characterization is deferred.

The handoff's earlier third-pass description and round-1 failure remain historical evidence;
the new recurrence/uniqueness theorems discharge the previous full-input identification gap.
The new C¹ proof uses only C¹ of the joint terms, which is sufficient, despite introductory prose
also describing their smoothness. No claim about unchanged results beyond round-1 scope is added.

The PASS WITH NOTES qualification records the deliberately narrow acceptance scope and the
launcher-only kernel replay/name-check evidence. It does not indicate an unpaid F1, F2 or F3 clause.
Only `docs/tracks/W/audits/W3-FLOW-audit-2.md` is handed off; no code repair or source change was made.
