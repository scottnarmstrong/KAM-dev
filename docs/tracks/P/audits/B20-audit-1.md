# B20 independent package audit

**Verdict: PASS WITH NOTES for B20.** No blocking mathematical, signature, or axiom
finding in `KAM/Planetary/WeakKAM/PolynomialBudget.lean`. The signed uniform budget
and displacement results are proved. Notes concern the inherited comparison-root
delta, permitted stale generated root, and the exact P11a5 consumer boundary.
No frozen anchor is implemented or made seal-ready by this infrastructure package.

Audited 2026-10-29 in `/root/code/KAM-inp-p11b-b20`. Report destination follows the
user's explicit worktree path, overriding the generic brief's main-worktree clause.
Only this report is a repository deliverable; temporary probes are removed.

## Snapshot, authority, and scope

- HEAD: `c3296afb40a1279f679848a94071b4e640aa8780`.
- Comparison `inp`: `7e77845396885b8f953f902df45903b7c9a7f20a` at inspection.
- `git diff inp...HEAD` warns `multiple merge bases, using
  bd587502d193103a0ad6239cb442a76b003487ae`. The other merge base is
  `3fcfb654e1e10a82cc4ab57401156fc446225ce1`. The requested comparison was used,
  not silently replaced by a parent-only comparison.
- B20 file SHA256:
  `21169ea2396d3d411c844fc0b5a9c2a1afda06835f4e9342d73619c6d16a0ea4`.
- Canonical `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean` SHA256:
  `e5ae0f3f6c134280acd184e6130e2c39bac49485097647cd36f52f7dbf87ef63`.
- P11B design SHA256:
  `b39ec4a5b9b976b355d6afe26047680ea2b1fbb1c86dd4073aa4428528961ea1`.

Read AGENTS.md, PLAN, DECISIONS, the package brief and B20 handoff; checked the
P11B node table, B20 package row (design L246), instructions L309, revision-2
F2 ruling L330, and both P11B design audits. Source checks use
`blueprint-P/parts/p11a3-iteration-selection.tex` L374–410,
`p11a4-limit-family.tex` L157–187, and
`p11a5-quantitative-theorem.tex` L70–109, together with the track statement and
frozen Phase/frequency/dynamics interfaces. The lean-statement-audit method is
applied to definitions, binders, constants and consumer composition; these are
signed infrastructure declarations, not new manifest-owned anchors.

The full comparison has 18 paths: the B20 module, three inherited PlanarTorsion
modules, KAM.lean, three graph files, and ten prior audit/handoff documents.
The Lean and graph diffs were inspected for scope/provenance; the inherited
packages are not re-certified. B20's two commits are `a2e25ec5` and `c3296afb`;
`git diff --stat a2e25ec5^ HEAD -- KAM/Planetary/WeakKAM/PolynomialBudget.lean
KAM.lean KAM/Frozen manifest README.md` reports only the 321-line B20 module.
The pre-existing untracked `B20-handoff.md` is preserved.

## Declaration and node verdicts

All names below are in `KAM.Planetary`. Mechanical comparison removed comments
and whitespace only: all **14 signed declarations** have exactly the canonical
headers, and all signed definitions/structure have exactly their canonical
bodies/fields. Proof bodies alone differ from the signature placeholders.
Fresh declarations copied from all three canonical theorem headers elaborate
using the corresponding production theorem. There are 21 explicit declarations:
10 definitions, one structure, and ten theorems.

| Node / role | Declaration (module line) | Verdict | Evidence |
|---|---|---|---|
| Fixed-data uniformity, F2 | `selectionFixedKey` (34) | PASS | Actual M₀ replaces h; no beta, epsilon or perturbation in key. |
| Beta exponent | `selectionBetaExponent` (36) | PASS | Exactly 2 max(2G₀,1+μG₀). |
| Eight nonnegative rates | `SelectionRates` (41) | PASS | Eight actual input rates; no output field. |
| adm-budget, D | `selectionBudgetD` (53) | PASS | n a_d+a_M+a_theta+(1+1/μ)a_beta. |
| adm-budget, G | `selectionBudgetG` (55) | PASS | Both gamma branches retained. |
| adm-budget, L | `selectionBudgetL` (57) | PASS | L=0 at zero strip rate, otherwise a_s+1. |
| adm-budget, J | `selectionBudgetJ` (58) | PASS | Includes C₁ rate. |
| adm-budget, X | `selectionBudgetX` (60) | PASS | max(J,L). |
| adm-budget, H | `selectionBudgetH` (62) | PASS | All three branch exponents present. |
| adm-budget, B | `selectionBudgetExponent` (66) | PASS | 2H+a_C. |
| adm-budget input family | `selectionFamilyBounds` (70) | PASS | Four lower and four upper input bounds only. |
| Actual-M₀ comparison | `polyBudget_thetaMax_le` (78) | PASS | Valid even when actual M₀=0; positive denominator from beta. |
| Three threshold branches | `polyBudget_threshold_le` (95) | PASS | Monotone branch comparison to original admissibility, no positive-actual-M₀ premise. |
| Exponent reconciliation | `polyBudget_exponent_eq` (128) | PASS | Exact Q3 exponent; strip dichotomy uses nonnegative rate. |
| `bpP:p11a:adm-budget` | `adm_budget` (140) | PASS | Uniform coefficient precedes seven other rates and every family datum. |
| Same-key projections | `polyBudget_key` (187) | PASS | Ten exact key component equalities. |
| `stepP:p11a:abb-spec`, exponent | `polyBudget_exponent_beta` (192) | PASS | Beta-only rates yield B₀ with no tau restriction needed by this identity. |
| `bpP:p11a:adm-budget-beta` | `adm_budget_beta` (224) | PASS | Uniform over h/beta at fixed numerical/geometric key. |
| Uniform cDelta | `polyBudget_CDelta` (272) | PASS | Explicit coefficient invariant on key classes. |
| Uniform cGamma | `polyBudget_CGamma` (278) | PASS | Explicit coefficient invariant on key classes. |
| `bpP:p11a:displacement-power` | `displacement_power` (286) | PASS | Both positive constants first; budget and one complete evaluation witness with exact power. |
| `stepP:p11a:ab-gamma` | `adm_budget` via `qb_poly` | PASS | Q3 `qbPoly_cDio_bound` / `qbPoly_gamma_lower` retain explicit sublevel/power-law formulas. |
| `stepP:p11a:ab-T0` | `adm_budget` via `qb_poly` | PASS | Q3 `qbPoly_tbar_bound`; zero and positive strip rates separated. |
| `stepP:p11a:ab-t0` | `adm_budget` via `qb_poly` | PASS | Q3 `qbPoly_collar`, `qbPoly_xibar_upper`; stronger flat quantities transfer to original threshold. |
| `stepP:p11a:ab-lam` | `qbPoly_lambda_lower`, `polyBudget_threshold_le` | PASS | All three branches, including C₁≥1 first-branch comparison. |
| `stepP:p11a:ab-concl` | `qb_poly`, `adm_budget` L180–183 | PASS | Square/divide and exact exponent, then transfer threshold. |
| `stepP:p11a:abb-spec` | `adm_budget_beta` L232–268 | PASS | All eight family inequalities constructed, not assumed. |
| `stepP:p11a:dpc-comb` | `displacement_power` L316–317; B17 `selectionDelta_le_power` | PASS | Original displacement and inverse-gamma estimates composed. |
| `stepP:p11a:qt-k6` positive-epsilon input | Signed export plus uniform Delta composition below | PASS WITH NOTES | Full Delta intermediate is recoverable; final P11a5 minorant/zero-case assembly remains separate. |

Reusing Q3 instead of repeating its numerical estimates is sound and introduces
no new premise. Its target is the stronger flat threshold, which B20 proves
is below the original threshold. The ab-* steps occur in the consumed Q3
proof rather than local blocks with the design's suggested names. There is no
missing B20 proof obligation from this relocation.

## Definitions and hypothesis expansion

All ten definitions are literal tuple/formula/predicate definitions; the
structure is a rate-data record. There is no choice construction, arbitrary
witness, output-shaped hypothesis, or junk fallback. The branch in
`selectionBudgetL` is the source's genuine strip-rate case split. Natural
parameters zero are handled by the literal Lean arithmetic formulas; their
analytic use is restricted by the source n, mu, rho hypotheses. No theorem
relies on an off-source zero division value.

For each of the ten definitions and `SelectionRates`:
`BODY_MATCH: OK; PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: N/A_LITERAL;
CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS`.

The following binder ledger expands the source-facing logical inputs.
T=typing, S=source, A=standing, R=ruled, E=excess. Rows for d apply to each
occurrence of d or d₀, without hiding its fields. Unused section variables
mu,t,C₁ do not become theorem assumptions.

| Binder / field | Bin | Source / reason |
|---|---|---|
| n | T | Dimension parameter. |
| adm_budget: mu | T | Natural order parameter, a3:376. |
| adm_budget: rho | T | Natural degree parameter, a3:376. |
| adm_budget: tau | T | Real exponent parameter, a3:376. |
| adm_budget: c | T | Real coefficient parameter. |
| adm_budget: as_ | T | Strip-rate parameter. |
| hn | S | n≥1, a3:376. |
| hmu | S | mu≥1, a3:376. |
| hrho | S | rho in {1,2}, a3:376. |
| htau | A | Selection standing nonnegative tau; exact signed assumption. |
| hgap | S | Lattice gap, a3:376. |
| hc | S | c>0, a3:376. |
| hc1 | S | c≤1, a3:376. |
| has | S | Nonnegative strip rate, a3:376. |
| r | T | Eight-rate record. |
| r.theta≥0 | S | Nonnegative rates, a3:376. |
| r.strip≥0 | S | Same. |
| r.beta≥0 | S | Same. |
| r.loss≥0 | S | Same. |
| r.M≥0 | S | Same. |
| r.M₀≥0 | S | Same. |
| r.C₁≥0 | S | Same. |
| r.diam≥0 | S | Same. |
| r.strip=as_ | S | Fix only strip rate before coefficient. |
| u | T | Family parameter. |
| 0<u | S | a3:376–382. |
| u≤1 | S | Same. |
| d or d₀ | T | Standing SelectionData carrier. |
| d.mu | T | Order. |
| d.rho | T | Degree. |
| d.tau | T | Exponent. |
| d.theta | T | Collar. |
| d.strip | T | Strip width. |
| d.C₁ | T | Hessian bound. |
| d.beta | T | Finite-type amount. |
| d.M | T | Jet bound. |
| d.loss | T | Measure-loss parameter. |
| d.K | T | Real Pi carrier. |
| d.h | T | Complex Hamiltonian function. |
| d.n_pos | A | sel-data, Data.lean:76. |
| d.mu_pos | A | Data.lean:77. |
| d.rho_mem | A | Data.lean:78. |
| d.tau_nonneg | A | Data.lean:79. |
| d.tau_gap | A | Data.lean:80. |
| d.compact | A | Data.lean:81. |
| d.positive_measure | A | Data.lean:82. |
| d.theta_pos | A | Data.lean:83. |
| d.theta_le | A | Data.lean:84. |
| d.strip_pos | A | Data.lean:85. |
| d.strip_le | A | Data.lean:86. |
| d.hessian_normalized | A | Data.lean:87; C₁≥1 explicitly in source. |
| d.beta_pos | A | Data.lean:88. |
| d.beta_le | A | Data.lean:89; supplies beta≤M. |
| d.loss_pos | A | Data.lean:90. |
| d.loss_lt | A | Data.lean:91. |
| d.holo | A | Data.lean:92. |
| d.real | A | Data.lean:93–94. |
| d.hessian | A | Data.lean:95–96. |
| d.finite_type | A | Data.lean:97–98, source scalar jet amount. |
| d.top_bounds | A | Data.lean:99–102, source multilinear jet bound. |
| d.mu=mu | S | Fixed family order. |
| d.rho=rho | S | Fixed family degree. |
| d.tau=tau | S | Fixed family exponent. |
| c u^a_theta≤d.theta | S | a3:377 lower bound. |
| c u^a_strip≤d.strip | S | a3:377 lower bound. |
| c u^a_beta≤d.beta | S | a3:377 lower bound. |
| c u^a_loss≤d.loss | S | a3:377 lower bound. |
| d.M≤c⁻¹u^-a_M | S | a3:377 upper bound. |
| actual M₀≤c⁻¹u^-a_M₀ | S | a3:377 upper bound. |
| d.C₁≤c⁻¹u^-a_C₁ | S | a3:377 upper bound. |
| diam K≤c⁻¹u^-a_diam | S | a3:377 upper bound. |
| same-key equality | S | a3:402–407 / a4:181; expands to ten component equalities, no h equality. |
| d.beta≤1 | S | a3:402 and a4:181; beta≤M already standing. |
| epsilon | T | Perturbation-size parameter. |
| epsilon>0 | S | a4:181. |
| epsilon≤selectionAdmissible d | S | a4:181. |
| f | T | Complex phase function. |
| hf.holo | S | SelectionPerturbation/Data.lean:107; source sel-data perturbation. |
| hf.periodic | S | Data.lean:108–109; period one. |
| hf.real | S | Data.lean:110–111. |
| hf.bound | S | Data.lean:112; sup bound by epsilon. |

Ledger schema counts (one copy of each displayed row, not multiplicities across
three theorems): T=22, S=37, A=22, R=0, E=0. Same-key equality is the ten
equalities mu,rho,tau,theta,strip,C₁,M,loss,K,actual M₀. Its individual components
are all S; replacing its one aggregate row by ten rows gives S=46.

For the seven unsigned helper theorems, n/mu/rho/tau/d/d₀/m0/r are typing or
the same standing data above. `hm`/`hM` are the explicitly named comparison
premises; `hd` is NumericalValid, namely n≥1, mu≥1, rho∈{1,2}, gap, tau≥0,
0<theta≤1, 0<strip≤1, C₁≥1, m0>0, 0<beta≤M, compact K, and
0<loss with ofReal(loss)<volume K. They are conditional comparison helpers,
not source exports; B20 constructs every such premise at L168–181.
`polyBudget_exponent_beta` uses only mu≥1 and rho∈{1,2}; key helpers use only
key equality. No helper imports an unproved step through an instance or record.

## Refutation checks and consumer boundary

**M₀+1 and threshold comparison.** Let m=actual M₀≥0. Then m+1>0 without
assuming m>0. With e=a_M₀≥0 and 0<u≤1, u^-e≥1 and c⁻¹≥1, so
m+1≤c⁻¹u^-e+1≤2c⁻¹u^-e=(c/2)⁻¹u^-e. All other rate bounds weaken
correctly at c/2. The selected coefficient still depends only on the permitted
fixed numerical data and strip rate.

The copy of `qb_comp` changes the sole problematic step to
`polyBudget_thetaMax_le`: at rho=1 thetaMax is unchanged, and at rho=2 the
denominator `2^(mu+1)*(2m+beta)` stays strictly positive even at m=0. Increasing
m decreases this branch. The inherited bounds give Tbar≥T₀, tflat≤t₀,
Xibar≥Xi. `qbcLam_mono` compares every min branch with correct direction;
the first uses tflat≤t₀≤C₁t₀. Squaring uses lambdaFlat>0, so the transfer to
`selectionAdmissible` does not reverse an inequality or replace the threshold.
The exact mollifier/sublevel constants pass through `qbcOfSelection` and
`qbc_oldThreshold_eq_selectionAdmissible`; no numerical surrogate is introduced.

**Beta specialization.** The positive c0 is chosen from fixed key data as
min(theta,strip,loss,1/(1+M+M₀+C₁+diam K)), grouped as in L234. This avoids
requiring strict positivity of actual M₀. The rates are (0,0,1,0,0,0,0,0).
The eight family bounds and B=B₀ identity are discharged in the proof.

**Uniform displacement and literal consumers.** The explicit cD is
`selectionCDelta d₀ * selectionCGamma d₀`; both factors are positive and
proved key-invariant. cstar comes from `adm_budget_beta`. Both precede the
varying h,beta,epsilon,f. The output `o` is constructed by
`evaluation_bilipschitz`; its inherited displacement field and B17
`selectionDelta_le_power` give the requested bound for all b∈Kinf and all
real theta, with exponent -(mu+1)/rho and sqrt(epsilon). Neither a torus nor
an iteration is assumed as input.

The signed `displacement_power` states the uniform defect bound plus simultaneous
budget, exactly as approved. It does not separately return the intermediate
Delta bound mentioned in `qt-k6`. Consumer sufficiency was checked by compiling:

```lean
theorem auditB20_uniformDelta (d₀ : SelectionData n) :
    ∀ d : SelectionData n, selectionFixedKey d = selectionFixedKey d₀ → d.β ≤ 1 →
      ∀ ε : ℝ, 0 < ε → ε ≤ selectionAdmissible d →
        selectionDelta d ε ≤
          (selectionCDelta d₀ * selectionCGamma d₀) * Real.sqrt ε *
            d.β ^ (-((d.μ : ℝ) + 1) / d.ρ) := by
  intro d hk hb ε he hs
  have h := selectionDelta_le_power d ε he hs hb
  rwa [polyBudget_CDelta hk, polyBudget_CGamma hk] at h
```

Together with `o.displacement`, this gives the full positive-epsilon
sup-defect≤Delta≤cD sqrt(epsilon) beta^-G₀ chain for the same output; the
production proof L316 already uses exactly that chain. Pointwise inequalities
for all b,theta express the source uniform supremum bound without requiring
an additional supremum-existence hypothesis. `qt-k6`'s use on Hinf follows by
the inherited Hinf⊆Kinf field.

This is the File-11a4 positive-epsilon, actual-M₀ result. It does not alone
prove File-11a5's data-only flat threshold, bounded-M₀ reduction, monotonicity,
or zero-perturbation case. Those remain P11C/Q assembly obligations, as the
revised design explicitly states. In particular no lower bound on a larger
threshold is asserted for a smaller minorant. There is no current production
import of PolynomialBudget by a later module in this checkout, hence no claim
of completed downstream assembly or P-FIXED theorem closure.

## Independent verification receipts

All Lean/Lake/checker calls initiated by this audit are sequential and use
`LEAN_NUM_THREADS=1` and `nice -n 5`. The required compile-gate wrapper itself
runs `nice -n 5 lake build`. No clean, update, cache fetch, library rebuild,
provider edit, frozen edit, manifest edit, or generated-file rewrite was done.

1. Targeted build, exit **0**:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
     /root/code/KAM-inp-p11b-b20 KAM.Planetary.WeakKAM.PolynomialBudget
   [inp-gate] slot 1 acquired 00:44:06 for KAM.Planetary.WeakKAM.PolynomialBudget
   Build completed successfully (9226 jobs).
   ```

   Existing dependency jobs replay unused-variable/simp and deprecation warnings;
   no warning was reported in PolynomialBudget. This is the targeted overlay
   build, not a clean rebuild.

2. Signature/definition/axiom probe, exit **0**, both before and after adding
   the uniform Delta consumer probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B20Audit.lean
   ```

   It copies all three signed theorem headers under fresh names and applies
   production exports with their original explicit arguments. Defining-equation
   examples for the key and beta exponent close by rfl. Mechanical source
   comparison verifies the remaining literal definitions and structure fields.
   Each of the following exact `#print axioms KAM.Planetary.<name>` outputs is
   `'<qualified name>' depends on axioms: [propext, Classical.choice, Quot.sound]`:

   ```text
   polyBudget_thetaMax_le
   polyBudget_threshold_le
   polyBudget_exponent_eq
   adm_budget
   polyBudget_key
   polyBudget_exponent_beta
   adm_budget_beta
   polyBudget_CDelta
   polyBudget_CGamma
   displacement_power
   ```

   No sorryAx or project axiom. These checks certify the package exports,
   not the still-draft P-FIXED frozen export.

3. Kernel replay, exit **0**, one invocation:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
     KAM.Planetary.WeakKAM.PolynomialBudget
   replaying KAM.Planetary.WeakKAM.PolynomialBudget
   ```

4. Source lint, exit **1**, solely the expressly permitted generated-root
   exception:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1160 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No substantive lint failure. The generated file is left untouched as required.

5. Additional mechanical checks: **PASS**. 321 physical lines, maximum width
   99 Unicode characters; copyright/module/public imports/docstring/exposed
   public noncomputable section present. No forbidden token or resource
   override in the audited module; no EuclideanSpace, norm instance, root
   shadow or reused public helper short name. Each of the ten theorem short
   names has exactly one declaration in KAM. `git diff --check inp...HEAD`
   exits 0 (with the recorded merge-base warning).

6. Import closure: 180 project modules, no provider. All 14 transitively imported
   frozen modules are definition modules and have their exact-path manifest
   owner in state SEALED: ActionNbhd, ComplexStrip, FrequencyMap,
   HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine,
   IsPrimaryOnStrip, IsRealOnReals, OmegaZero, RealHamiltonian, SymplecticForm,
   Planetary.CircularPoint, Planetary.CircularTube, Planetary.Phase. No
   DRAFT_SORRY theorem is imported. Definition meaning at the Phase/frequency
   interface is unchanged.

## Notes, defects, and limits

- **N1, inherited protected-path delta:** the literal command
  `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is **not empty**:
  it adds four generated imports in KAM.lean (BirkhoffClauses, Generic, Patch,
  ParameterLipschitz). KAM/Frozen, manifest and README.md have no delta.
  Generated-root history includes `3fcfb654`, `62205e2c`, and `6a70a8ed`;
  the two B20 commits change only PolynomialBudget. Thus the branch-wide
  empty-protected-diff condition is not met literally; this inherited integration
  note is not attributed to B20 and is not reported as a clean global check.
- **N2, documentation locator:** PolynomialBudget L16 calls the general-budget
  result `bpP:p11a:budget`; its actual source node is
  `bpP:p11a:adm-budget` (a3:375). The former labels the later P11a5 minorant
  budget. This is a local documentation mismatch, not a theorem-type defect;
  no source or code was repaired.
- The use of Q2/Q3 adds existing numerical infrastructure imports beyond the
  design's B07/B17/B19 shorthand. BudgetAdmissible imports WeakKAM.Admissible,
  not PolynomialBudget; no cycle is introduced. Future Q assembly must retain
  that direction.
- No new suspected mathematical defect in the pinned sources was found.
  No deviation from a signed declaration, no added premise, and no default-
  heartbeat design failure was found. The audit does not independently re-audit
  every inherited proof or certify the full quantitative/physical theorem.
