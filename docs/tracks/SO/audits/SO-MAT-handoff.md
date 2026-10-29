# SO-MAT prover handoff (branch inp-somat, beafc9c9; track SO package run by the main orchestrator)


Branch `inp-somat` (off `inp-soemb`, base `d69ba137`), worktree `/root/code/KAM-inp-somat`. Last code commit `beafc9c9`.
Every edit is committed. There is no `sorry`, `axiom`, `native_decide`, `EuclideanSpace`, or heartbeat or recursion
override. I made no edits to frozen or shared files, `README.md` or `KAM.lean`.

## Files (both new; 715 lines in total)

- **`KAM/Certificate/Gram.lean`** (585 lines)
  - Signed, verbatim (checked textually against `SOSignatures.lean` §F): `ModelMatrix`, `ModelMatrix.Encloses`,
    `polyMatrix`, `gramModels`, `gramModels_sound`, `gramCheck`, `gramCheck_sound`.
    - `ModelMatrix` (abbrev) and `ModelMatrix.Encloses` were not landed yet; they now live here.
  - Definitions:
    - `CertModel.addMixed` and `modelSumPairs`, `modelSumRounds`, `modelSum` (a balanced model sum);
    - `realCompPoly`, `compDerivModel`, `dkAngleModel`, `dkActionModel`;
    - `gramEntryModel`, `modelMatrixEntry`, `gramInvPoly`, `gramBGModel`, `gramDefectUp`, `maxCandidate`;
    - `gramDefectRows`, `gramInvRows`, `gramInvShapeOk`, `gramBoundsOk`.
  - Lemmas:
    - `CertModel.Encloses.of_eq_fun`, `encloses_add_of_eval`, `CertModel.Encloses.addMixed`;
    - `modelSumPairs_spec`, `modelSumRounds_spec`, `foldl_addMixed_spec`, `modelSum_encloses`, and the abbrev
      `EnclosedList`;
    - `realComp_eq_realCompPoly`, `fderiv_realComp_apply`, `compDerivModel_encloses`, `compDerivModel_deg`;
    - `CertEmbedding.fderiv_eval_fst`, `CertEmbedding.fderiv_eval_snd`;
    - `dkAngleModel_encloses`, `dkActionModel_encloses`;
    - `gramMatrix_comm`, `gramEntryModel_encloses`;
    - `polyMatrix_apply`, `exactModel_encloses`, `gramBGModel_encloses`, `norm_sub_le_gramDefectUp`,
      `gramBoundsOk_spec`.
  - The DK models and their contracts are public, for SO-TORS to reuse.
- **`KAM/Certificate/Tests/Gram.lean`** (130 lines): ℚ tests, `decide +kernel`, plus two contract instances.
- Not committed, because `.drafts` is git-ignored: `.drafts/SO-MAT-probe.lean` (the CertFixed timing probe),
  `.drafts/SO-MAT-eval.lean` and `.drafts/SO-MAT-axioms.lean`.

## Approach

### DK

- **Angle entries.** `∂_j K_{1,i} = δ_ij + ∂_j((2π)^{dU_i} U_i)`.
  - The derivative is `CertModel.ofDeriv` (exact multipliers `i k_j`) of `toSortedPoly` of the data. A missing
    component is `⟨[]⟩`.
  - It is then taken to degree 0 with `toDeg 0`.
  - On the diagonal, `constModel n 1 0 0` is added (`CertModel.add`; both summands have degree 0).
- **Action entries.** `∂_j K_{2,i}`, built the same way, with no constant.
- **Analytic step.** `(fderiv K θ v).1 i = v i + D U_i v` and `(fderiv K θ v).2 i = D A_i v`. Both are proved by
  composing `HasFDerivAt` with the projection CLMs and using `HasFDerivAt.unique`.
- **Why degree 0.** Every DK entry has degree 0, so all Gram and `B·G` models have degree 0. The diagonal defect can
  then use the landed `oneSubSupUp`, and the `toDeg 0` calls downstream are no-ops (one `Int` comparison).

### Gram

- **Entries.** `G_ab = Σ_r DK_ra DK_rb` is built for `a ≤ b` only. The `2n` rows are the angles, then the actions.
  - Product keys are `[3, 0, a, b, r]`, with `r < n` for angle rows and `r = n + k` for action row `k`.
  - The products go through `CertModel.mul`, so a constant factor takes the scalar route.
  - The products are summed by `modelSum`, a balanced tree of pairwise `addMixed` (64 rounds).
- **Lower triangle.** Entry `(a, b)` with `a > b` is the same `gramEntryModel n K W cfg pe b a` term. The proof
  uses `gramMatrix_comm`, since `dotℂ` is symmetric. In the kernel probe, forcing `G₀₁` and `G₁₀` together costs no
  more than forcing `G₀₁` alone (about 4.5 s each), so the shared term is evaluated once.
- **`addMixed`.** It computes `add a (toDeg a.deg b)`. If either summand has no terms, it adds only the radius:
  there is no merge, and no weighted `errRadius` pass over the other summand.
  - This covers the products with an identically zero DK entry. In the lunar data that is the constant row
    `(0, 1)`.
  - Soundness: `encloses_add_of_eval`.

### Check

`gramCheck n K Binv W cfg pe σBμ` runs these steps, failing closed at each:

1. **Shape.** It checks the exact `n × n` shape of `Binv`.
2. **`B·G` models.** `(B G)_ij = Σ_k B_ik G_kj`, with keys `[3, 1, i, j, k]`. `B_ik` is the exact model
   `⟨0, B_ik, 0⟩` (`⟨[]⟩` if missing, as in `polyMatrix`). A constant `B_ik` is a scalar product. The result is
   taken through `toDeg 0`, a no-op that gives the degree fact for free.
3. **Defect bounds.** On the diagonal it uses `oneSubSupUp` (zero-mode ball `1 − Σ c₀`, plus the other terms
   weighted, plus the radius). Off the diagonal it uses `|P|_w + rad`.
4. **Row sums and `(δ, β)`.**
   - `δ_i = sumUp_j(defect)` and `β_i = sumUp_j |B_ij|_w`; both are balanced.
   - `δ` and `β` are `maxCandidate` folds that use `ble`. Since `ble` is one-sided, every row is re-checked with
     `ble r δ` and `ble r β`.
5. **Final tests.** `blt δ 1`, `ble 0 δ`, `0 ≤ σBμ`, and `ble (upAdd β (upMul (ofRatUp σ) δ)) (ofRatDown σ)`.
   The last one gives `β + σδ ≤ σ`, which is `β/(1 − δ) ≤ σ`.

Soundness, at each `θ` in the strip:

- `‖1 − B(θ)G(θ)‖ ≤ δ` and `‖B(θ)‖ ≤ β`, from the row-sum characterization `KAM.norm_le_iff_forall_rowSum`.
  `β ≥ 0` comes from row 0, using `1 ≤ n`.
- The landed `matrix_inv_of_approx_inverse` (with `Nonempty (Fin n)` from `hn`) then gives:
  - `IsUnit det`;
  - `‖G⁻¹‖ ≤ β/(1 − δ) ≤ σ`, hence the row sums, through `KAM.rowSum_le_norm`;
  - `‖G⁻¹ − B‖ ≤ δβ/(1 − δ)`.

### Kernel lessons applied

- Balanced sums: `modelSum`, and `sumUp` for the row sums.
- Constant operands use the scalar route (identity and constant `B`, constant DK entries).
- No per-term zero tests. There is one emptiness test per summand in `addMixed`.
- No accumulator chains.
- The Gram matrix computes only its upper triangle (SO-ADVCOUNT item 6).

## Checks and their exact output

- **Gate build.**
  `inp_lake_build.sh /root/code/KAM-inp-somat KAM.Certificate.Gram KAM.Certificate.Tests.Gram`, last run after the
  final code commit:
  ```
  ✔ [2961/2962] Built KAM.Certificate.Gram (6.5s)
  ✔ [2962/2962] Built KAM.Certificate.Tests.Gram (7.4s)
  ```
  - Neither of my files emits a warning.
  - The only warnings in the build are pre-existing ones in `Arith/PiHigh.lean` and `Expr/Basic.lean`.
- **Lint.** `sh scripts/lint_sources.sh`:
  ```
  check_lean_modules: PASS (1356 Lean files, 0 comparator configurations)
  FROZEN-ANCHOR GUARD OK
  ABI HASHES OK (144 frozen declarations)
  ```
  - The only failure is `KAM.lean is out of date; run scripts/gen_root_imports.py`. This was already failing at the
    base, as SO-EMB reported. `KAM.lean` is generated, so the orchestrator must regenerate it to add the two new
    modules.
  - No line in my files is over 100 characters.
- **Short names.**
  `main_shortname_check.py /root/code/KAM-inp-somat KAM.Certificate.Gram KAM.Certificate.Tests.Gram` gives
  `short-name check OK (no reused public short name)`. `CertModel.Encloses.of_eq` collided with a Mathlib short name
  and was renamed `of_eq_fun`.
- **Axioms.** `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each of:
  - `gramModels_sound`, `gramCheck_sound`;
  - `dkAngleModel_encloses`, `dkActionModel_encloses`, `modelSum_encloses`;
  - `gramTest_sound`, `gramTest_models_sound`, `gramTest_refined`, `gramTest_n2_models`.

## Tests (`Tests/Gram`, ℚ, `decide +kernel`; the whole file elaborates in about 5 s)

The weight is `W = ⟨1/100, 11/10⟩` and the π enclosure is `⟨314159/100000, 1/10000, 5, 2⟩`. Every key
`[3, 0|1, i, j, k]` is advised `direct`.

**The `n = 1` toy.** `U = 0.1 cos 2πθ` at degree −1 and `A = 1 + 0.01 cos 2πθ`, so
`G = (1 − 0.1 sin)² + (0.02π sin)²`.

| Test | Result |
|---|---|
| `gramTest_one`, `B = 1` | `δ ∈ (0.2, 0.3)` and `β = 1`; `#eval` gives `δ = 0.235412` (hand estimate ≈ 0.237) |
| `gramTest_refined`, `B = 1 + 0.2 sin` (genuine `B·G` products) | `δ < 0.1` and `β ∈ (1.2, 1.25)`; `#eval` gives `δ = 0.032017`, `β = 1.22` |
| `gramTest_sigmaFail`, `σ = 1` | `none` (`β/(1 − δ) ≈ 1.31`) |
| `gramTest_negSigma`, `σ = −1` | `none` |
| `gramTest_zero`, `B = 0` | `none` (`δ = 1`) |
| `gramTest_shape`, `B = []` and a `1 × 2` witness | `none` |

**The `n = 2` toy.** `U = (0.1 cos 2πθ₁, 0)` and `A = (1 + 0.01 cos 2πθ₁, 1)`.

| Test | Result |
|---|---|
| `gramTest_n2_models` | The shape is `2 × 2`. `G₀₁` and `G₁₀` are exactly zero: no terms, radius 0. `G₁₁` has radius 0. |
| `gramTest_n2`, `B = I` | `δ ∈ (0.2, 0.3)` and `β = 1` |

**Contract instances.** `gramTest_models_sound` and `gramTest_sound`.

## Kernel timings (`.drafts/SO-MAT-probe.lean`, `CertFixed 128`)

**Setup.**
- `n = 2`, and the cutoff is 1000.
- The embedding is `U₀`, `p` with real cosine data on the keys `|k|₁ ≤ D` (half keys lexicographically positive),
  coefficients `2^{−|k|₁}/800`; `U₁ = 0`, `J = 0`.
- Every Gram product key is advised `direct`, and `B = I`.
- The profiler's "type checking took" lines are cumulative over the file; the figures below are the increments.
- The machine load was about 13 on 8 cores, so the figures are noisy at about ±20 %.

| Check | Data terms | Kernel |
|---|---:|---:|
| `gramCheck … isSome`, `D = 2` | 13 | 3.0 s |
| `gramCheck … isSome`, `D = 3` | 25 | 8.2 s |
| all 8 DK models, `D = 5` | 61 | 0.4 s |
| all `gramModels` radii, `D = 5` | 61 | 32.6 s |
| `gramCheck … isSome`, `D = 5` | 61 | 39.7 s |

**Reading.**
- The cost is almost entirely SO-MALG's `direct` products. These are 61 × 61 = 3721 unmerged items each; their
  merges and the weighted `errRadius` passes over them are the expensive part.
- The SO-MAT-specific work is small:
  - DK models: 0.4 s;
  - the `B·G` stage with scalar `B`, the defect rows and the bounds: about 7 s, which is proportional to the size of
    the unmerged G entries.
- The production `cfgLow` uses packed advice, which returns dense, merged products. So these figures overstate the
  production cost. **SO-DATA should measure the real stage once the packed advice exists.** I could not build
  packed advice here.

## Uncertainties, design signals, deviations

1. **No heartbeat problem.** Each file builds in under 8 s at default settings.
2. **Deviations from the TOYGEN Python mirror (`toy_check.py`).** All are implementation choices inside unsigned
   bodies. The SO-DATA mirror must follow the Lean.
   - **Degree of DK entries.** Every DK entry is taken to degree 0. The mirror converts only the diagonal angle
     entries (through `m_add` with the constant) and leaves the off-diagonal and action entries at degree
     `d + 1`. With degree-0 action data, the Lean polynomials of those entries are therefore the mirror's times
     `2π` (upper Machin bound), with the Machin gap paid in the radius.
   - **Gram keys.** `[3, 0, a, b, r]` exists only for `a ≤ b` (the upper triangle). The mirror's full `mat_mul`
     also issues the keys `a > b`; those keys are simply never looked up here. `[3, 1, i, j, k]` is unchanged.
   - **Summation order.** Sums are balanced (`((t₀ + t₁) + (t₂ + t₃))`); the mirror folds left. The advice does not
     depend on the order, but the rounded CertFixed radii differ in the last bits.
   - **Zero summand.** `addMixed` with a summand that has no terms adds only the radii. The mirror's `m_add`
     returns the other summand when one is zero.
   - **Diagonal defect.** It uses `oneSubSupUp` (the zero-mode ball) instead of `supBound(const − BG)`. This is
     never weaker, and equal in exact arithmetic.
   - **Fail-closed checks beyond the mirror.** `0 ≤ δ`, `0 ≤ σBμ`, and every row sum `≤` the returned max (`ble` is
     one-sided). They are exact in ℚ and pass whenever the mirror passes with `σBμ ≥ 0`.
3. **`ModelMatrix` and `ModelMatrix.Encloses`** are defined here, verbatim from §F, because they had not landed.
   SO-TORS imports them from `KAM.Certificate.Gram`.
4. **SO-GEN2's weighted-ℓ¹ Gram inverse bound (1.98).**
   - The certified `β/(1 − δ)` is exactly the "row sums of `|B_ij|_w`" bound over `1 − δ`. That is the
     weighted-ℓ¹ bound SO-GEN2 measured; no grid sup check is involved.
   - `|c|` enters through `CC.normUp`, an upper bound, so the margin `σB − μ = 1.987` versus 1.97994 must absorb that
     rounding. At 318 bits this is negligible.
5. **No pinned-source errata.** Every signed statement was proved exactly as signed, with no added hypotheses.

CONTEXT: the accepted design /root/code/KAM/docs/tracks/SO/design/SO-LEAN-DESIGN.md (Revision 7), §7 row SO-MAT; signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean §F lines ~705-760 (ModelMatrix, ModelMatrix.Encloses, gramModels, gramModels_sound, gramCheck, gramCheck_sound). Built on SO-EMB, SO-MALG, SO-MINV (landed).

AUDIT FOCUS: (1) signed declarations verbatim; (2) gramModels_sound: the Gram models enclose the EXACT Gram matrix of the embedding's derivative on the strip, every entry present (no default model); (3) gramCheck_sound gives exactly the invertibility and inverse-norm bound IG1Body consumes, through matrix_inv_of_approx_inverse and ModelMatrix.HasShape, for every certificate-supplied approximate inverse, with no added premise; (4) tests reduce by decide +kernel with false controls; (5) hygiene. Audit ONLY KAM/Certificate/Gram.lean and KAM/Certificate/Tests/Gram.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.
