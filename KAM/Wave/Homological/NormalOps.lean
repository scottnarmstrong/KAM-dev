/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.Schur
public import KAM.Wave.Homological.Index
public import KAM.Wave.Seq.Multiplier
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Normal operators and their norms (blueprint-W `bpW:w4:ops`, `bpW:w4:schur` (ii))

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

Representative model (see `Schur.lean`): `HomL2 = ℓ²_ℂ` is the common model of every `ℓ^N_{a,q}`
(`ẑ_j = ω_{a,q}(j+2) z_j`), and `HomOp` the model of `𝓛` (weighted matrices).

* the unweighted pairing of a vector `c ∈ ℓ^N_{a,p+1}` (representative `ĉ`) with `z ∈ ℓ^N_{a,p}`
  (representative `ẑ`) is `⟨c,z⟩₀ = ∑ (D ĉ)_j ẑ_j` with the diagonal `D = homLamD a p`,
  `D_j = 1/(ω_{a,p}(j+2) ω_{a,p+1}(j+2)) ∈ (0,1]` (`homPairRep`);
* the dual norm `‖c‖_* = ‖D ĉ‖` (`homDualNorm`), `‖c‖_* ≤ ‖ĉ‖`;
* `Λ : 𝓛 → 𝓑`, `ΛM = D M̂` (`homLamCLM`): the weighted matrix of the bilinear form
  `(z,z') ↦ ⟨Mz,z'⟩₀` on the representatives; `‖M‖_bil = ‖D M̂‖ ≤ ‖M̂‖` (`norm_homLamCLM_le`).
  The space `𝓑` is thus modelled by the operators `D M̂` on `ℓ²` and the Hadamard map on `𝓑`
  (`bpW:w4:schur` (ii)) is `homHadamardOp` itself, which commutes with `Λ`
  (`homHadamardOp_lam`);
* `norm_le_of_pairing_le`: a vector `v ∈ ℓ²` with `|∑ v_j y_j| ≤ K` for all `‖y‖ ≤ 1` has `‖v‖ ≤ K`
  (the norm formula of W4-E5 for the pairing without conjugation).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

/-- `0 ≤ p ≤ p_+` gives the weight condition `0 ≤ p + p_+` of the pairings. -/
theorem homPP {p pb : ℝ} (hp : 0 ≤ p) (hpb : p ≤ pb) : 0 ≤ p + pb := by linarith

/-- The diagonal `D_j = 1/(ω_{a,p}(j+2) ω_{a,p+1}(j+2))`. -/
def homLamD (a p pb : ℝ) (j : ℕ+) : ℂ := ((homWt a p j * homWt a pb j)⁻¹ : ℝ)

theorem norm_homLamD_le {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p + pb) (j : ℕ+) : ‖homLamD a p pb j‖ ≤
    1 := by
  unfold homLamD
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h1 := one_le_homWt_mul (a := a) (q := p) (q' := pb) ha hp j
  have h0 : 0 < homWt a p j * homWt a pb j := lt_of_lt_of_le one_pos h1
  rw [abs_of_pos (inv_pos.mpr h0)]
  exact inv_le_one_of_one_le₀ h1

/-- The diagonal multiplier `D` on `ℓ²`. -/
def homLamDiag {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p + pb) : HomOp :=
  weightedDiagCLM (homLamD a p pb) (norm_homLamD_le ha hp)

theorem norm_homLamDiag_le {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p + pb) : ‖homLamDiag ha hp‖ ≤ 1 :=
  norm_diagCLM_le _ _

theorem homLamDiag_apply {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p + pb) (y : HomL2) (j : ℕ+) :
    homLamDiag ha hp y j = homLamD a p pb j * y j := rfl

/-- **`Λ : 𝓛 → 𝓑`** in the representative model: `ΛM = D M̂`. -/
def homLamCLM {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p + pb) : HomOp →L[ℂ] HomOp :=
  ContinuousLinearMap.compL ℂ HomL2 HomL2 HomL2 (homLamDiag ha hp)

theorem homLamCLM_apply {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p + pb) (A : HomOp) :
    homLamCLM ha hp A = (homLamDiag ha hp).comp A := rfl

/-- The bilinear norm `‖M‖_bil = ‖ΛM‖`; it is at most `‖M‖`. -/
theorem norm_homLamCLM_apply_le {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p + pb) (A : HomOp) :
    ‖homLamCLM ha hp A‖ ≤ ‖A‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right (norm_homLamDiag_le ha hp) (norm_nonneg A))

theorem kamEntry_homLamCLM {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p + pb) (A : HomOp) (i j : ℕ+) :
    kamEntry (homLamCLM ha hp A) i j = homLamD a p pb i * kamEntry A i j := rfl

/-- `Λ` commutes with the Hadamard map (`bpW:w4:schur` (ii), in the representative model). -/
theorem homHadamardOp_lam {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p + pb) {d : ℕ+ → ℕ+ → ℂ} {c : ℝ}
    (h : HomHadamardBound d c) (A : HomOp) :
    homHadamardOp h (homLamCLM ha hp A) = homLamCLM ha hp (homHadamardOp h A) := by
  refine homOp_ext_entries fun i j => ?_
  rw [homHadamard_entry, kamEntry_homLamCLM, kamEntry_homLamCLM, homHadamard_entry]
  ring

/-- **`Λ` of the Hadamard image: the `𝓑`-bound** (`bpW:w4:schur` (ii)):
`‖Λ H_d M‖ ≤ c K_S ‖ΛM‖`. -/
theorem norm_homLam_hadamard_le {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p + pb) {d : ℕ+ → ℕ+ → ℂ} {c :
    ℝ}
    (h : HomHadamardBound d c) (A : HomOp) :
    ‖homLamCLM ha hp (homHadamardOp h A)‖ ≤ c * homKS * ‖homLamCLM ha hp A‖ := by
  rw [← homHadamardOp_lam]
  exact norm_homHadamardOp_le h _

/-- The pairing `⟨c, z⟩₀` of representatives: `∑ (D ĉ)_j ẑ_j`. -/
def homPairRep {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p + pb) (c z : HomL2) : ℂ :=
  ∑' j, homLamDiag ha hp c j * z j

/-- The dual norm `‖c‖_* = ‖D ĉ‖ ≤ ‖ĉ‖`. -/
def homDualNorm {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p + pb) (c : HomL2) : ℝ := ‖homLamDiag ha hp c‖

theorem homDualNorm_le {a p pb : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p + pb) (c : HomL2) :
    homDualNorm ha hp c ≤ ‖c‖ :=
  ((homLamDiag ha hp).le_opNorm c).trans
    (by simpa using mul_le_mul_of_nonneg_right (norm_homLamDiag_le ha hp) (norm_nonneg c))

/-- Cauchy–Schwarz for the unconjugated pairing on `ℓ²`. -/
theorem homL2_pair_le (v w : HomL2) :
    Summable (fun j : ℕ+ => ‖(v j : ℂ) * (w j : ℂ)‖) ∧
      ‖∑' j : ℕ+, (v j : ℂ) * (w j : ℂ)‖ ≤ ‖v‖ * ‖w‖ := by
  have hv : HasSum (fun j : ℕ+ => ‖(v j : ℂ)‖ ^ 2) (‖v‖ ^ 2) := lp_two_hasSum_sq v
  have hw : HasSum (fun j : ℕ+ => ‖(w j : ℂ)‖ ^ 2) (‖w‖ ^ 2) := lp_two_hasSum_sq w
  obtain ⟨hs, hle⟩ := summable_tsum_mul_le (A := fun j : ℕ+ => ‖(v j : ℂ)‖)
    (B := fun j : ℕ+ => ‖(w j : ℂ)‖) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (norm_nonneg v) (norm_nonneg w) hv hw
  have e : ∀ j : ℕ+, ‖(v j : ℂ) * (w j : ℂ)‖ = ‖(v j : ℂ)‖ * ‖(w j : ℂ)‖ := fun j => norm_mul _ _
  simp only [e]
  exact ⟨hs, (norm_tsum_le_tsum_norm (by simpa only [e] using hs)).trans (by simpa only [e] using
      hle)⟩

theorem memℓp_homConj (v : HomL2) : Memℓp (fun j => starRingEnd ℂ (v j)) 2 := by
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  refine (memℓp_gen_iff h2).mpr ?_
  have h := (memℓp_gen_iff h2).mp v.2
  simpa using h

/-- Coordinatewise conjugation on `ℓ²`. -/
def homConjL2 (v : HomL2) : HomL2 := ⟨fun j => starRingEnd ℂ (v j), memℓp_homConj v⟩

theorem norm_homConjL2 (v : HomL2) : ‖homConjL2 v‖ = ‖v‖ := by
  have h1 := lp_two_hasSum_sq (homConjL2 v)
  have h2 := lp_two_hasSum_sq v
  have : (fun j => ‖homConjL2 v j‖ ^ 2) = fun j => ‖v j‖ ^ 2 := by
    funext j; simp [homConjL2]
  rw [this] at h1
  have := h1.unique h2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp this

theorem tsum_mul_homConjL2 (v : HomL2) : ∑' j, v j * homConjL2 v j = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  have h2 := lp_two_hasSum_sq v
  have h3 := (Complex.hasSum_ofReal.mpr h2)
  refine HasSum.tsum_eq ?_
  convert h3 using 1
  funext j
  simp [homConjL2, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Norm formula** (W4-E5, for the unconjugated pairing): if `|∑ v_j y_j| ≤ K` for all
`‖y‖ ≤ 1` then `‖v‖ ≤ K`. -/
theorem norm_le_of_pairing_le {v : HomL2} {K : ℝ}
    (h : ∀ y : HomL2, ‖y‖ ≤ 1 → ‖∑' j, v j * y j‖ ≤ K) : ‖v‖ ≤ K := by
  by_cases hv : v = 0
  · subst hv
    have := h 0 (by simp)
    simpa using this
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set y : HomL2 := (‖v‖⁻¹ : ℂ) • homConjL2 v with hy
  have hy1 : ‖y‖ ≤ 1 := by
    rw [hy, norm_smul, norm_homConjL2]
    simp [inv_mul_cancel₀ hn.ne']
  have := h y hy1
  have e : ∑' j, v j * y j = ((‖v‖ : ℝ) : ℂ) := by
    have : ∑' j, v j * y j = (‖v‖⁻¹ : ℂ) * ∑' j, v j * homConjL2 v j := by
      rw [← tsum_mul_left]
      exact tsum_congr fun j => by simp [hy]; ring
    rw [this, tsum_mul_homConjL2]
    push_cast
    field_simp
  rw [e] at this
  simpa [abs_of_pos hn] using this

end KAM.Wave
