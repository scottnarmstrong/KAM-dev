# T3 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the scoped T3 infrastructure package. All five required declarations are present with the exact design signatures (including the definition body). No frozen anchor is sealed or certified by this package. Kernel/build/probe results are recorded below after independent execution.

Audited 2026-10-28 in `/root/code/KAM-inp-p11c-t3`. HEAD `6a35ee34a69bd61b4a2019b2d908ddb977567768`; comparison ref `inp` = `7ec42a1dd0f6154a1f6a357ba53d92080b367082`. `git diff inp...HEAD` adds only `KAM/Planetary/PlanarTorsion/LaplaceReduction.lean` (498 lines). Initial untracked `docs/tracks/P/audits/T3-handoff.md` belongs to the supplied audit inputs and was preserved. Only this report is a lasting audit edit; probes are confined to `.lake/abi-scratch/` and removed. The user's explicit absolute report destination overrides the generic brief's main-worktree destination.

Read authority: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, T3-handoff.md including AUDIT FOCUS, P11C-LEAN-DESIGN.md (T3 row, node rows, Appendix A), DESIGN-P11C-design-audit-1.md, track P statement (especially P-PLANAR), blueprint-P/parts/p11b-planar-torsion.tex L43–62 and p8-secular-form.tex L110–113. Applied the lean-statement-audit skill to exact-type, binder and definition checks; this is an infrastructure audit, so frozen provider/seal-body checks and frozen premise closure are N/A. The module imports only Mathlib; no frozen definitions, theorem anchors, DRAFT_SORRY anchors or providers occur in its dependency surface. No unrelated frozen anchor is claimed proved.

Snapshot SHA-256:

| Input | Hash |
|---|---|
| Audited Lean file | `cb6f6178d4c43c7fd42084d8129eb41dea325214e274efa51151fc0243cc7682` |
| `/root/code/KAM-inp/.drafts/design/P11CSignatures.lean` | `34bb5ddd0dbe6862b9cd0fcf6996805e0953bb8c0d774fa10d14986075f64079` |
| P11C-LEAN-DESIGN.md | `51533142c3d8aa6611dd280f64f7ee06b54513cf2578684547fd393b53abfd36` |

The design and standalone signature hashes equal the independent design audit's recorded inputs. The standalone signatures are absent from this worktree's .drafts; the supplied main-worktree copy was read, without modifying it.

## Declaration coverage

All names below have prefix `KAM.Planetary.`. Every new public declaration is listed. `bpP:p11b:laplace-red` and its steps lr-1/lr-2/lr-3/lr-red are covered; the denominator theorem covers the explicit pole envelope at blueprint L50. There are 30 declarations: 24 theorems, five definitions and one abbreviation.

| Node / role | Declaration (Lean line) | Verdict | Reason |
|---|---|---|---|
| local support / adapter | `p11c_laplace` L25 | PASS | Literal normalized radian integral; exact signature body; Part 8 L110–113. |
| local support / adapter | `p11cKer` L31 | PASS | Literal polynomial/trigonometric denominator; no fallback. |
| local support / adapter | `p11cKer_pos` L33 | PASS | Strict positivity for all real t from 0<a<1. |
| local support / adapter | `p11cKer_contDiff` L37 | PASS | Proves Continuous, as used; name overstates smoothness but type is honest. |
| local support / adapter | `p11c_cont_div` L40 | PASS | Continuous numerator and positive kernel imply continuous quotient for every real s. |
| local support / adapter | `p11cI` L47 | PASS | Literal unnormalized interval integral. |
| local support / adapter | `p11c_laplace_eq` L50 | PASS | Definitional equality restoring normalization. |
| local support / adapter | `p11cI_cont` L53 | PASS | Specialization to continuous cosine numerator. |
| local support / adapter | `p11cI_red1` L59 | PASS | lr-1: product-to-sum and justified linearity of integrals; all integer k. |
| local support / adapter | `p11cI_red2` L91 | PASS | lr-2: FTC with explicit derivative, integrability and zero endpoint terms; all integer k. |
| local support / adapter | `p11c_laplace_red1` L153 | PASS | lr-1 normalized by the same factor on both sides. |
| local support / adapter | `p11c_laplace_red2` L159 | PASS | lr-2 normalized; no division by s-1. |
| local support / adapter | `p11c_laplace_red3` L166 | PASS | lr-3 by elimination; stronger integer-k version without k>=1. |
| laplace-red | `laplace_red` L174 | PASS | All R1–R3, exact signature, every real s; k=0 retained. |
| laplace-red | `laplace_up` L187 | PASS | Exact upward identities; s>=1/2 guards s; 0<a<1 guards a and Delta. |
| local support / adapter | `p11cEv` L238 | PASS | Literal rational-polynomial evaluation in R. |
| local support / adapter | `p11cRep` L242 | PASS | Internal existential representation predicate; global polynomials, nonzero q on (0,1). |
| local support / adapter | `p11cRep_comb` L248 | PASS | Generic conditional algebra helper; its representation and identity premises are discharged in base/all inductions. |
| local support / adapter | `p11cRep_zero` L266 | PASS | Explicit numerator witnesses 1,0 and denominator 1. |
| local support / adapter | `p11cRep_one` L269 | PASS | Explicit numerator witnesses 0,1 and denominator 1. |
| local support / adapter | `p11c_one_sub_sq_ne` L272 | PASS | Delta nonzero from the source interval. |
| local support / adapter | `p11cRep_base` L276 | PASS | Induction in j with upward identities; rational constants depend only on j. |
| local support / adapter | `p11c_laplace_step` L307 | PASS | Solved R3 with explicit divisor guard; guard proved for every later half-integer use. |
| local support / adapter | `p11cRep_all` L314 | PASS | Induction in k; half-integer divisor cannot vanish by integer parity. |
| laplace-red | `laplace_rational_reduction` L361 | PASS | Exact global polynomial witnesses before a; pole-free q on all (0,1). |
| local support / adapter | `p11cRepD` L374 | PASS | Internal representation predicate with the literal a^m Delta^(2j) denominator. |
| local support / adapter | `p11cRepD_mono` L379 | PASS | Multiply numerator by X^n; a nonzero on the entire admissible interval. |
| local support / adapter | `p11cRepD_base` L390 | PASS | Induction in j adds exactly Delta^2 per level, no a denominator. |
| local support / adapter | `p11cRepD_all` L434 | PASS | Adjacent k induction gives exponents k,k+1; rational scalar reciprocals absorbed in numerators. |
| laplace-red | `laplace_reduction_denominator` L487 | PASS | Exact required envelope, with explicit nonvanishing conjunct; completes T3b obligation. |

## Binder fidelity and hypotheses

Exact design locators: standalone signatures L338–349 (definition and red), L680–686 (up), L689–695 (rational reduction), L794–802 (denominator); corresponding Appendix A at design L654–663, L996–1011, L1110–1116. Whitespace-normalized theorem header comparisons all returned True; a fresh-name declaration with each verbatim design header and the explicit application below checks elaboration and explicit binder order. Whole-function `type_of%` probes additionally check binder implicitness/order.

| Required declaration | Expanded outer binder | Bin | Source / reason |
|---|---|---|---|
| laplace_red | s : R | TYPING | Blueprint L44 arbitrary real exponent |
| laplace_red | a : R | TYPING | Blueprint L44 real ratio |
| laplace_red | ha : a in (0,1) | SOURCE | Blueprint L44 |
| laplace_red | k : N | TYPING | Blueprint L44, k>=0 |
| laplace_up | s : R | TYPING | Blueprint L50–55 |
| laplace_up | a : R | TYPING | Blueprint L44 |
| laplace_up | hs : 1/2 <= s | SOURCE | Blueprint L50 |
| laplace_up | ha : a in (0,1) | SOURCE | Blueprint L44 |
| laplace_rational_reduction | j : N | TYPING | Blueprint L50, s=1/2+j |
| laplace_rational_reduction | k : N | TYPING | Blueprint L50 |
| laplace_reduction_denominator | j : N | TYPING | Blueprint L50 |
| laplace_reduction_denominator | k : N | TYPING | Blueprint L50 |

Outer-input counts: SOURCE=3, STANDING=0, TYPING=9, RULED=0, EXCESS=0. There are no implicit or instance binders on these four results. Within conclusions, red's implication `1<=k` is precisely blueprint L48; up's universally quantified `k:N` and `1<=k` are precisely L55. Both reductions have `exists polynomials, forall a in (0,1)` in that order: witnesses depend only on j,k, never on a. No physical data, chart, regularity, representation or recurrence premise has been added.

The helper inputs were also expanded: kernel/continuity and recurrence lemmas use only real/integer typing data, `ha`, and (for the generic continuity helper) an arbitrary continuous numerator. The solved recurrence's `hk` is a distinct conditional algebra helper, not an unproved source result. `p11cRep_comb` assumes two representations, nonvanishing W and its displayed combination identity; `p11cRepD_mono` assumes the representation it transports. These are openly conditional closure lemmas with distinct names. Their actual uses supply the representations by induction, the combination equations by proved red/up recurrences, and the nonvanishing guards by positivity or the half-integer parity argument. No helper premise escapes into a source-facing export.

## Definition classification

For each definition/abbreviation: BODY_MATCH=OK; PUBLIC_CARRIER=OK; WELL_DEFINEDNESS=N/A_LITERAL; CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS.

| Declaration | Classification and full-carrier meaning |
|---|---|
| p11c_laplace | Literal integral adapter, exactly the signature formula for every real s,a and integer k. Uses Mathlib's total interval integral and real power; has no branch or selected witness. The source-facing analytic domain 0<a<1 is retained in all recurrence conclusions. |
| p11cKer | Literal kernel for every real a,t; the positivity theorem correctly restricts a, rather than asserting positivity everywhere. |
| p11cI | Literal raw integral for every s,k,a. The normalization equation is rfl. |
| p11cEv | Literal evaluation of any rational polynomial at any real a using algebraMap Q R. |
| p11cRep | Internal existential predicate, not a chosen function or asserted physical object. Expands to three rational polynomials and a uniform pole-free representation on precisely (0,1). Its assumptions in conditional helpers are discharged before export. |
| p11cRepD | Internal existential predicate with two rational polynomials and exact a^m(1-a^2)^(2j) denominator on (0,1). Nonvanishing is derived in the exported theorem. |

No structure, instance, choice-defined object, junk branch, arbitrary witness selection or replacement physical model is introduced. Representation predicates do not replace the blueprint's integral; the public reductions expand them to explicit polynomial witnesses.

## Independent proof review

At L33–35 strict positivity follows from cos(t)<=1 and 0<a<1, so real-power manipulations and integrability for every real s are justified. L59–87 proves R1 by an equality of continuous integrands and product-to-sum. L91–149 constructs the derivative of sin(kt) times kernel^(1-s), proves it integrable, and applies FTC. Both endpoint terms vanish because k is integer; this also handles k=0. L166–172 eliminates the lower-order coefficient without dividing by s-1 or s-1-k.

L187–232 solves the two-by-two system using symmetry at k=-1, with determinant (1-a^2)^2 and s nonzero. L276–359 constructs rational polynomial representations by j induction at k=0,1, then k induction at fixed j; the potentially dangerous factor j-1/2-(k+1) cannot vanish, proved by integer parity. L390–484 repeats the induction while tracking the exact pole envelope: j increments add Delta^2; k increments consume one a, and aligning the k-1 term requires X^2 in its numerator. Rational scalar reciprocals are polynomial constants and are guarded by the same parity proof. L487–496 supplies nonvanishing of both factors of a^k Delta^(2j). No pole-free assertion is inferred merely from a rational-function type.

## Notes, source defects and scope

N1 (integration boundary): no U8a module is imported and no equality with `SecularForm.laplace_def` is exported. The latter's literal definition (LaplaceCoeff.lean L28–30) uses multiplication by kernel^(-s), while this adapter uses division by kernel^s. They have the same normalization and intended positive-kernel meaning. This matches the explicitly authorized adapter design (design L52, standalone signature comment L337). A downstream consumer needing the U8a API must prove/use that bridge; this audit does not certify its consumption. It does not block the complete T3 signature slice.

N2 (documentation): handoff's opening line count 363 is stale after T3b; actual file has 498 lines. Its `p11cKer_contDiff` name denotes only a continuity theorem, correctly acknowledged by the handoff. Neither affects theorem strength.

No suspected mathematical defect in the scoped blueprint statements was confirmed. No new source erratum or implementation deviation is proposed. Blueprint L50's text “times a product of linear factors” consists of nonzero rational constants at each fixed half-integer level, so absorbing their reciprocals into Q-polynomial numerators in the stronger exact envelope is valid. General campaign/design provenance and DAG notes from the earlier design audit do not change T3's statement or import requirements. P-PLANAR, torsion nondegeneracy, physical averaging bridges and the campaign theorem remain outside this package audit.

## Validation receipts

All Lean/Lake stages were serial, with `LEAN_NUM_THREADS=1` and `nice -n 5`. The gate wrapper waited for a slot, then acquired slot 2 at 15:45:27 UTC. No clean/update/cache operation or full-library rebuild was requested.

Targeted build (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11c-t3 KAM.Planetary.PlanarTorsion.LaplaceReduction
```

```text
[inp-gate] slot 2 acquired 15:45:27 for KAM.Planetary.PlanarTorsion.LaplaceReduction
Build completed successfully (9047 jobs).
```

Exact-type/definition/axiom probe (exit 0, no warnings or errors):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/T3Audit.lean
```

The four fresh-name proofs apply, in explicit binder order: `laplace_red s a ha k`, `laplace_up s a hs ha`, `laplace_rational_reduction j k`, and `laplace_reduction_denominator j k`. The `type_of%` examples and the definition-equality `rfl` all elaborate. Initial scratch-only execution exited 1 because the copied integral definition lacked `noncomputable`; marking only that scratch definition noncomputable fixed the probe. No package code was changed. The successful run printed exactly these 30 axiom results:

```text
'KAM.Planetary.p11c_laplace' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cKer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cKer_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cKer_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_cont_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cI' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_laplace_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cI_cont' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cI_red1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cI_red2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_laplace_red1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_laplace_red2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_laplace_red3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.laplace_red' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.laplace_up' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cEv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cRep' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cRep_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cRep_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cRep_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_one_sub_sq_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cRep_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11c_laplace_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cRep_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.laplace_rational_reduction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cRepD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cRepD_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cRepD_base' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11cRepD_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.laplace_reduction_denominator' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay (one invocation, exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PlanarTorsion.LaplaceReduction
```

```text
replaying KAM.Planetary.PlanarTorsion.LaplaceReduction
```

Lint (exit 1 solely for the expressly permitted generated-root exception):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (766 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

A preliminary lint run was stopped before its ABI Lean stage so that the complete lint could be run serially after kernel replay with the required environment and priority. That interrupted run is not used as a validation receipt.

Other checks:

- `git diff --check inp...HEAD`: exit 0, empty output.
- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty output.
- Forbidden-token scan `rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option' KAM/Planetary/PlanarTorsion/LaplaceReduction.lean`: exit 1, no matches.
- All 30 declaration names were searched as declaration identifiers in every other KAM Lean file: no collisions. Mathlib is the only direct import; provider and DRAFT_SORRY quarantine checks are vacuous for project imports.
- File length 498, below 1500; module header, copyright, `public import`, module docstring, and `@[expose] public noncomputable section` present. No resource override.
- Successful axiom set for every new public theorem (and all six definitions/abbreviations) is exactly `[propext, Classical.choice, Quot.sound]`; no sorryAx or project axiom.
- Final audit changes are this report only; pre-existing untracked handoff retained. Disposable T3 probe and validation logs were removed after copying the exact receipts into this report.

Final scope decision: **T3 COMPLETE / PASS WITH NOTES**, independently validated at this HEAD. `p11c_laplace` and all four design theorem exports pass. No frozen anchor/provider exists in this slice, so “seal-ready” is N/A; no campaign theorem closure is inferred. The U8a consumer bridge remains the explicit downstream boundary described in N1.


## Reproducible disposable probe

The following was generated from the pinned signature file (no sorry declaration was imported). Each expected theorem copies its corresponding complete signature, with only its fresh name and proof changed. The probe is removed after execution.

```lean
import KAM.Planetary.PlanarTorsion.LaplaceReduction

open Set Metric Real MeasureTheory Function

open KAM.Planetary

namespace T3Audit

theorem expected_laplace_red (s a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    p11c_laplace (s - 1) k a = (1 + a ^ 2) * p11c_laplace s k a -
      a * (p11c_laplace s ((k : ℤ) + 1) a + p11c_laplace s ((k : ℤ) - 1) a) ∧
    (k : ℝ) * p11c_laplace (s - 1) k a = (s - 1) * a *
      (p11c_laplace s ((k : ℤ) - 1) a - p11c_laplace s ((k : ℤ) + 1) a) ∧
    (1 ≤ k → (s - 1 - k) * a * p11c_laplace s ((k : ℤ) + 1) a =
      (k + s - 1) * a * p11c_laplace s ((k : ℤ) - 1) a - k * (1 + a ^ 2) * p11c_laplace s k a) := by
  exact KAM.Planetary.laplace_red s a ha k

example : type_of% @expected_laplace_red := @KAM.Planetary.laplace_red

theorem expected_laplace_up (s a : ℝ) (hs : 1 / 2 ≤ s) (ha : a ∈ Ioo (0 : ℝ) 1) :
    p11c_laplace (s + 1) 0 a = ((1 + a ^ 2) * p11c_laplace s 0 a +
      2 * a * (1 - 1 / s) * p11c_laplace s 1 a) / (1 - a ^ 2) ^ 2 ∧
    p11c_laplace (s + 1) 1 a = ((1 + a ^ 2) * (1 - 1 / s) * p11c_laplace s 1 a +
      2 * a * p11c_laplace s 0 a) / (1 - a ^ 2) ^ 2 ∧
    ∀ k : ℕ, 1 ≤ k → p11c_laplace (s + 1) ((k : ℤ) + 1) a =
      p11c_laplace (s + 1) ((k : ℤ) - 1) a - k * p11c_laplace s k a / (s * a) := by
  exact KAM.Planetary.laplace_up s a hs ha

example : type_of% @expected_laplace_up := @KAM.Planetary.laplace_up

theorem expected_laplace_rational_reduction (j k : ℕ) :
    ∃ p0 p1 q : Polynomial ℚ, ∀ a ∈ Ioo (0 : ℝ) 1,
      Polynomial.eval₂ (algebraMap ℚ ℝ) a q ≠ 0 ∧
      p11c_laplace (1 / 2 + (j : ℝ)) k a =
        (Polynomial.eval₂ (algebraMap ℚ ℝ) a p0 * p11c_laplace (1 / 2) 0 a +
         Polynomial.eval₂ (algebraMap ℚ ℝ) a p1 * p11c_laplace (1 / 2) 1 a) /
          Polynomial.eval₂ (algebraMap ℚ ℝ) a q := by
  exact KAM.Planetary.laplace_rational_reduction j k

example : type_of% @expected_laplace_rational_reduction := @KAM.Planetary.laplace_rational_reduction

theorem expected_laplace_reduction_denominator (j k : ℕ) :
    ∃ p0 p1 : Polynomial ℚ, ∀ a ∈ Ioo (0 : ℝ) 1,
      a ^ k * (1 - a ^ 2) ^ (2 * j) ≠ 0 ∧
      p11c_laplace (1 / 2 + (j : ℝ)) k a =
        (Polynomial.eval₂ (algebraMap ℚ ℝ) a p0 * p11c_laplace (1 / 2) 0 a +
         Polynomial.eval₂ (algebraMap ℚ ℝ) a p1 * p11c_laplace (1 / 2) 1 a) /
          (a ^ k * (1 - a ^ 2) ^ (2 * j)) := by
  exact KAM.Planetary.laplace_reduction_denominator j k

example : type_of% @expected_laplace_reduction_denominator := @KAM.Planetary.laplace_reduction_denominator

noncomputable def expected_laplace (s : ℝ) (k : ℤ) (a : ℝ) : ℝ :=
  (2 * π)⁻¹ * ∫ t in (0 : ℝ)..(2 * π), cos ((k : ℝ) * t) / (1 + a ^ 2 - 2 * a * cos t) ^ s

example : expected_laplace = KAM.Planetary.p11c_laplace := rfl

end T3Audit

#print axioms KAM.Planetary.p11c_laplace

#print axioms KAM.Planetary.p11cKer

#print axioms KAM.Planetary.p11cKer_pos

#print axioms KAM.Planetary.p11cKer_contDiff

#print axioms KAM.Planetary.p11c_cont_div

#print axioms KAM.Planetary.p11cI

#print axioms KAM.Planetary.p11c_laplace_eq

#print axioms KAM.Planetary.p11cI_cont

#print axioms KAM.Planetary.p11cI_red1

#print axioms KAM.Planetary.p11cI_red2

#print axioms KAM.Planetary.p11c_laplace_red1

#print axioms KAM.Planetary.p11c_laplace_red2

#print axioms KAM.Planetary.p11c_laplace_red3

#print axioms KAM.Planetary.laplace_red

#print axioms KAM.Planetary.laplace_up

#print axioms KAM.Planetary.p11cEv

#print axioms KAM.Planetary.p11cRep

#print axioms KAM.Planetary.p11cRep_comb

#print axioms KAM.Planetary.p11cRep_zero

#print axioms KAM.Planetary.p11cRep_one

#print axioms KAM.Planetary.p11c_one_sub_sq_ne

#print axioms KAM.Planetary.p11cRep_base

#print axioms KAM.Planetary.p11c_laplace_step

#print axioms KAM.Planetary.p11cRep_all

#print axioms KAM.Planetary.laplace_rational_reduction

#print axioms KAM.Planetary.p11cRepD

#print axioms KAM.Planetary.p11cRepD_mono

#print axioms KAM.Planetary.p11cRepD_base

#print axioms KAM.Planetary.p11cRepD_all

#print axioms KAM.Planetary.laplace_reduction_denominator
```
