# SO-TORS prover handoff (branch inp-sotors, 46694661; track SO package run by the main orchestrator)


Branch `inp-sotors` (worktree `/root/code/KAM-inp-sotors`), base `bc4e6f24` (SO-MAT audit request).
Head `46694661`. All work is committed. No frozen file, `manifest/`, `README.md` or `KAM.lean` was touched.

## Files (all new)

| File | Lines | Content |
|---|---|---|
| `KAM/Certificate/Torsion/Frame.lean` | 382 | `torsionIdx` (signed), `torsionIdx_lt`; frame calculus: `fderiv_tangentMat_eq_sum_partials`, `fderiv_normalMat_apply` (`DN[v] = Ω₀(DL[v] G⁻¹ + L D(G⁻¹)[v])`, `D(G⁻¹)[v] = -G⁻¹(DL[v]ᵀL + LᵀDL[v])G⁻¹`), `differentiableOn_torsion_of_frame`, `fderiv_apply_normalFrame` (last row), `sqMat_apply_eq_phaseBasis`, `linMat_apply_eq` (`(DX_H∘K)_{ab} = hamSign a · ∂²H(K)[a.swap, b]`), `continuousOn_extendedTorsion`; embedding second derivatives (`hasFDerivAt_charSum`, `CertPoly.fderiv_fderiv_eval_single`, `CertPoly.differentiable_fderiv_eval_single`, `tangentMat_eval_inl/inr`, `fderiv_tangentMat_eval_inl/inr`); the second-derivative model `CertModel.ofDeriv2` (`deriv2Mult/Coeff/Err/Item`) with contract `CertModel.Encloses.ofDeriv2` |
| `KAM/Certificate/Torsion/Average.lean` | 362 | `torsionAvgCheck` (signed), `torsionAvgCheck_shape` (signed), `torsionAvgCheck_sound` (signed); helpers `listShapeOk`, `isZeroKeyN`, `zeroModeBall`, `ccEntry`, `avgCentre`, `avgRadius`, `avgDefectUp`, `avg{Defect,Inv,Rad}Rows`, `avgDegOk`, `avgBoundsOk` and their lemmas |
| `KAM/Certificate/Torsion/Models.lean` | 633 | `torsionModels` (signed), `torsionModels_sound` (signed); model matrices `buildMat`, `CertModel.negM`, `modelMat{Mul,Add,Neg,Transpose,Omega}`, `ModelMatrix.EntryEncloses` and its `model{Mul,Add,Neg,Transpose,Omega}` rules; base models `ballModel`, `freqModel`, `dkModels`, `d2kModel`, `dkwModels`, `gramInvRadius`, `gramInvModels`, `torsionSlots`, `swapNat`, `dxhModels`, `d1Models` with contracts; `torsion_eq_models`. Publicly imports `Torsion/Average` (so `Frame` + `Models` is the whole interface) |
| `KAM/Certificate/Tests/Torsion.lean` | 163 | kernel tests (below) |

## Signed declarations (design §F, SOSignatures lines ~754-800): proved exactly as signed

`#check` of all six was compared against `/root/code/KAM-inp/.drafts/design/SOSignatures.lean`; binders,
order and conclusions are identical (including `hn : 1 ≤ n`, `{sw Nw}`, `(s : ℚ)`, `(s : ℝ) • ω`, the
`HasShape ∧ Encloses ∧ ContinuousOn` conclusion, `hρ`, `hT`, `hcont`, `(S σTμ h)`).

- `torsionIdx`, `torsionModels`, `torsionModels_sound`, `torsionAvgCheck`, `torsionAvgCheck_shape`,
  `torsionAvgCheck_sound`.

## Approach

**Producer (`torsionModels`).** Matrices of models as lists (`buildMat`), entries read by `modelMatrixEntry`.
`L = DK` (`2n × n`, the Gram check's `dkAngleModel`/`dkActionModel`), `G⁻¹ = ⟨0, B_kj, eps⟩` with
`eps ≥ δβ/(1-δ)` (`gramInvRadius`: requires `0 ≤ δ`, `0 ≤ β`, `δ < 1`, then `upMul (upMul δ β) t`,
`t ≥ 1/(1-δ)` from `recipOneSubUp`; fail closed otherwise), `D_{sω} L = Σ_l (sω)_l ∂_l L` (second
derivatives `ofDeriv2`, the coordinate balls `freqModel` = centre `s c_l`, radius `|s| r_l`),
`N = Ω₀(L G⁻¹)`, `DG = DLᵀL + LᵀDL`, `DGi = -((G⁻¹ DG) G⁻¹)`, `DN = Ω₀(DL G⁻¹ + L DGi)`, one `Slp.compose`
on the slots `d1 ++ d2` (row-major, `torsionSlots`), `DX_H = ±d2[a.swap][b]`, `X_N = DX_H N + (-DN)`,
`T = Nᵀ(Ω₀ X_N)`, last row `[d1] N`, border column `freqModel`, corner `zeroModel`. Every product entry
is `toDeg 0 (modelSum (mul …))` at key `[4, t, i, j, k]`. Soundness: generic enclosure rules for each
matrix operation (`EntryEncloses.model*`, with an index equivalence `Fin m ≃ μ` for the inner sum:
`Equiv.refl` for `Fin n`, `finSumFinEquiv.symm` for `Fin n ⊕ Fin n`), base contracts, then on the strip
`torsion = Nᵀ Ω₀ X_N` (`torsion_eq_mat`) with `DN` from `fderiv_normalMat_apply` (`fderiv_matrix_inv_apply`)
(`torsion_eq_models`), `DH(K)N_b = Σ_a ∂_aH N_{ab}`, `linMat` via `sumVec_fderiv_hamiltonianVectorFieldℂ`,
`IsSymmSndFDerivAt` and `jet_d2`. Gram invertibility on the strip, the bound `‖G⁻¹ - B‖` and continuity
inputs come from `gramCheck_sound`; continuity (`continuousOn_extendedTorsion`) from holomorphy of `K`,
`G⁻¹`, `X_H` on the open `D` and `differentiableOn_torsion_of_frame`. Nothing is assumed beyond the signed
premises (no conclusion-shaped hypothesis).

**Consumer (`torsionAvgCheck`).** Exact shapes first (`listShapeOk (n+1)` for `T` and `S`), then every
entry of degree `0`, centre `C_lj` = ball of the zero-key coefficients (`isZeroKeyN n k ↔ certKeyFun n k = 0`),
`R_lj` = that ball's radius + model radius, entries of `I - S C` as balls (`CertBall.times`, `listSum`,
`plus`), row sums, `δ_T = a + b·r`, and `gramBoundsOk [δ_T] rows(S) δ_T b σ` (`δ_T < 1`, `0 ≤ δ_T`,
`0 ≤ σ`, `b + σ δ_T ≤ σ`). Soundness: `CertModel.Encloses.average` per entry,
`‖1 - S A‖ ≤ ‖1 - S C‖ + ‖S‖ ‖C - A‖`, then `matrix_inv_of_approx_inverse` on the full
`(n+1) × (n+1)` average indexed by `Fin n ⊕ Unit` (`sum_torsionIdx`, `torsionIdx_injective`).

## Checks (exact commands and output)

- Gate build:
  `/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sotors KAM.Certificate.Torsion.Frame KAM.Certificate.Torsion.Average KAM.Certificate.Torsion.Models KAM.Certificate.Tests.Torsion`
  → `✔ Built KAM.Certificate.Torsion.Average (2.7s)`, `✔ Built KAM.Certificate.Torsion.Models (3.1s)`,
  `✔ Built KAM.Certificate.Tests.Torsion (11s)`, `Build completed successfully (2984 jobs).` (Frame built
  earlier in the same state, 3.7 s; a rebuild is a no-op.) No warning and no `sorry` in my files.
- `sh scripts/lint_sources.sh` → exit 1 ONLY for `KAM.lean is out of date; run scripts/gen_root_imports.py`,
  which is PRE-EXISTING: `KAM.lean` is byte-identical to the base commit `bc4e6f24`, which already lacks
  `KAM.Certificate.Gram`, `Embedding`, … (rule 10: I did not regenerate it). All other lines:
  `check_lean_modules: PASS (1360 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`,
  `ABI HASHES OK (144 frozen declarations)`; no line over 100 columns.
- `python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sotors KAM.Certificate.Torsion.Frame KAM.Certificate.Torsion.Average KAM.Certificate.Torsion.Models KAM.Certificate.Tests.Torsion`
  → `short-name check OK (no reused public short name)`, exit 0 (after renaming
  `EntryEncloses.{mul,add,neg,omega,transpose}` → `model*`, `fderiv_tangentMat_apply` →
  `fderiv_tangentMat_eq_sum_partials`, `differentiableOn_torsion_of` → `differentiableOn_torsion_of_frame`).
- Forbidden tokens (`native_decide`, `ofReduceBool`, `elab`, `macro`, `run_cmd`, `addDecl`, `sorry`,
  `implemented_by`, `extern`, heartbeat/recursion overrides, `EuclideanSpace`, `axiom`, `opaque`, `unsafe`):
  none in the four files (grep).

## `#print axioms`

```
'KAM.Certificate.torsionModels_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsionAvgCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsionAvgCheck_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.continuousOn_extendedTorsion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_endToEnd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_pipeline' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_F7' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Tests and kernel timings (`decide +kernel`, `ℚ` backend, `LEAN_NUM_THREADS=1`, profiler)

| Test | What | Kernel |
|---|---|---|
| `torsTest_border` | bordered `[[0,1],[1,0]]` (zero torsion block, invertible only through the border: the lunar pattern), radii `10⁻³`, self-inverse witness passes | < 0.1 s |
| `torsTest_failClosed` | witness `0`; `σ` too small; an entry of degree `1`; radii `1/2` → all `false` | 0.23 s |
| `torsTest_F7` (design §8 negative test 9) | audit's `A = [1 0 0; 0 0 1; 0 1 0]`: valid pair passes `torsionAvgCheck 2`, fails `torsionAvgCheck 1` (as models, as witness, and mixed) | 0.22 s |
| `torsTest_pipeline` | `n = 1`, `H = I²/2`, `K = (θ + 0.1cos/2π, 1 + 0.01cos)`, Gram witness `1 + 0.2 sin`, box `1 ± 10⁻³`, `s = 1`: `gramCheck`, `torsionModels`, shape, `torsionAvgCheck 1 T S 4` | 4.55 s |
| `torsTest_pipelineFail` | same at `σ = 3` → `false` | 3.86 s |
| `torsTest_sound`, `torsTest_endToEnd` | both contracts instantiated; END TO END: the bordered torsion average of the toy is invertible with inverse row sums `≤ 4` for EVERY `ω` in the box | 0.79 s |

Toy numbers (from `#eval`, for orientation): average ≈ `[[0.98515, 1], [0.99, 0]]`, radii
`[[0.1805, 0.001], [0.0466, 0]]`; `‖I - SC‖ = 0.00485`, `‖S‖ = 2`, `max rows R = 0.1815`.

## Deviations from the Python mirror (`scripts/spin_orbit/toy_check.py`: `torsion_models`, `torsion_avg_check`; the Lean is authoritative)

1. **Module split**: three modules (`Frame`, `Average`, `Models`) instead of two; `Models` re-exports
   `Average`, so importing `Frame`/`Models` as in the design gives the whole interface.
2. **Second derivatives**: Python builds `Model(d + 2, ∂_m∂_j P)` exactly; Lean `ofDeriv2` forms
   `-k_j k_l c_k` with backend products (rounding in the radius) and immediately `toDeg 0`.
3. **`D_{sω} DK`**: Python `m_scale_ball` (radius `(|c|+r)·rad + r·|a|_w`); Lean `CertModel.mul` with the
   constant model `freqModel` (scalar route `directItems`, never an advice lookup; nominal key
   `[4, 10, i, j, l]`), radius from the generic product bound. Same enclosure up to rounding.
4. **Frequency radius `|s|·r`** (Python `s·r`, assumes `s > 0`).
5. **Sums**: every matrix-product entry is a balanced `modelSum` (pairwise `addMixed`) followed by
   `toDeg 0`; Python folds left with `m_add` and keeps mixed degrees. All model entries handed to the
   averaging check are therefore of degree `0`.
6. **`gramInvRadius`** fails closed unless `0 ≤ δ`, `0 ≤ β`, `δ < 1` (checked again in the backend), and
   bounds `1/(1-δ)` by `recipOneSubUp`; Python uses exact `δβ/(1-δ)`.
7. **Averaging check**: Lean has no `π` enclosure there (the signed `torsionAvgCheck n T S σTμ` has no
   `W`/`pe`), so an entry of nonzero degree FAILS CLOSED (Python applies `toDeg 0`); the producer only
   emits degree-`0` entries. The zero mode is a ball (`coeffSumBall` of the keys with
   `certKeyFun n k = 0`, i.e. the first `n` key entries zero), its radius is added to `R`; the entries of
   `I - S C` are balls (rounded products); Python computes `C` and `I - SC` exactly in `ℚ`. The final test
   is `‖S‖ + σ δ_T ≤ σ` with `0 ≤ σ` (Python `‖S‖/(1-δ_T) ≤ σ`).
8. Product keys, `DX_H = ±d2[swap a][b]`, the slot layout `d1 ++ d2` (row-major), `Ω₀` row action,
   `X_N = DX_H N - DN`, `T = Nᵀ Ω₀ X_N`, last row `[d1] N` and the border column all match the mirror.

## Uncertainties / design signals

- No heartbeat or recursion problem anywhere; every file elaborates in a few seconds.
- **Kernel cost at lunar scale is unmeasured.** For `n = 2` the producer makes about 170 model products
  (16 `[4,0]`, 32 `[4,1|2]`, 16 `[4,3|4]`, 32 `[4,5|6]`, 32 `[4,7]`, 16 `[4,8]`, 8 `[4,9]`, 16 scalar
  `[4,10]`) plus one `Slp.compose` of `d1` and all `d2` slots. Intermediate matrices are `let`-bound lists
  read by `modelMatrixEntry` (the `gramCheck` pattern); sharing relies on the kernel's whnf cache. SO-DATA
  should profile `decide +kernel` on `checkTorsion` early.
- `G⁻¹` enters `N` and `D(G⁻¹)` (three factors), so the Gram radius `δβ/(1-δ)` is amplified in the
  torsion radii (toy: Gram `δ ≈ 0.032` gives a `T` radius `0.18`). This matches the mirror's model.
- The lint's `KAM.lean is out of date` is pre-existing (see Checks); the orchestrator's regeneration should
  add the three `Torsion` modules and `Tests/Torsion`.

## Suspected errata

None. No pinned-source or frozen-declaration defect was found; the signed statements were provable as
written (no premise added, none substituted).

CONTEXT: the accepted design /root/code/KAM/docs/tracks/SO/design/SO-LEAN-DESIGN.md (Revision 7), §7 row SO-TORS; signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean §F lines ~754-800 (torsionIdx, torsionModels, torsionModels_sound, torsionAvgCheck, torsionAvgCheck_shape, torsionAvgCheck_sound; design audit 2 F7: exact (n+1)x(n+1) shapes). Built on SO-MAT, SO-EMB, SO-MALG, SO-FREQ, SO-NORM (landed).

AUDIT FOCUS: (1) signed declarations verbatim; (2) torsionModels_sound: exact shape HasShape (n+1), enclosure of the EXACT bordered torsion matrix of the embedding and Hamiltonian, continuity, as the consumer needs; (3) torsionAvgCheck_sound gives exactly the invertibility and inverse-norm bound of the averaged bordered torsion matrix that IG1Body consumes, through matrix_inv_of_approx_inverse, for every certificate-supplied witness, with no added premise; fail-closed on wrong shapes or witnesses; (4) tests reduce by decide +kernel with false controls; (5) hygiene. Audit ONLY KAM/Certificate/Torsion/{Frame,Models,Average}.lean and KAM/Certificate/Tests/Torsion.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no public short name reused from KAM or Mathlib, no harmful root shadow, lines <= 100, no native_decide or axiom.
