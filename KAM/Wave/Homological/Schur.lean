/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.KamSupport.HilbertMatrix
public import KAM.Wave.Seq.Transport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Hadamard division of operators (blueprint-W `bpW:w4:schur`, parts (i) and (iii))

Off-frontier, source-faithful infrastructure (W4-HOMOLOGICAL); the dependency graph is still
being built.

Model. By `bpW:w4:schur`, step *Representatives*, an element `M ∈ 𝓛` (a bounded map
`ℓ^N_{a,p} → ℓ^N_{a,p̄}`) is the same thing, with the same norm, as its weighted matrix
`(μ_i M_ij ν_j)`, `μ_i = ω_{a,p̄}(i+2)`, `ν_j = ω_{a,p}(j+2)⁻¹`, viewed as a bounded operator on
`ℓ²_ℂ`. Here `HomOp := ℓ²_ℂ →L ℓ²_ℂ` is that representative model of `𝓛`, with matrix entries
`kamEntry`. `homNormalEntry_gen a p A i j` is the matrix entry `M_ij` of the operator `M ∈ 𝓛`
represented by `A`.

* `homHadamardCLM hd`: the Hadamard map `A ↦ (d_ij A_ij)` as a continuous linear map `HomOp → HomOp`
  of norm `≤ c K_S`, `K_S = 1 + π/√3` (`norm_homHadamardCLM_le`), entries `homHadamard_entry`,
  and the transposition identity in entry form `homHadamard_transpose_entry` (part (i));
* `homDiagonal_bound_gen`: `(i+2) |M_ii| ≤ ‖M‖` (part (iii)).
-/

@[expose] public section

namespace KAM.Wave

open KAM

/-- `ℓ²_ℂ` indexed by the P96-K index `j ≥ 1`. -/
abbrev HomL2 : Type := lp (fun _ : ℕ+ => ℂ) 2

/-- The representative model of `𝓛` (weighted matrices as bounded operators on `ℓ²_ℂ`). -/
abbrev HomOp : Type := HomL2 →L[ℂ] HomL2

/-- The constant `K_S = 1 + π/√3` of `bpW:w4:schur`. -/
noncomputable def homKS : ℝ := 1 + Real.pi / Real.sqrt 3

theorem homKS_lt : homKS < 3 := by
  have := kamHilbertConst_lt_two
  unfold kamHilbertConst at this
  unfold homKS
  linarith

theorem one_le_homKS : 1 ≤ homKS := by
  unfold homKS
  have : 0 ≤ Real.pi / Real.sqrt 3 := by positivity
  linarith

/-- The hypothesis `|d_ij| ≤ c/|i-j|` (`i ≠ j`), `|d_ii| ≤ c`. -/
structure HomHadamardBound (d : ℕ+ → ℕ+ → ℂ) (c : ℝ) : Prop where
  off : ∀ i j : ℕ+, i ≠ j → ‖d i j‖ ≤ c / |(i : ℝ) - (j : ℝ)|
  diag : ∀ i : ℕ+, ‖d i i‖ ≤ c

theorem HomHadamardBound.nonneg {d : ℕ+ → ℕ+ → ℂ} {c : ℝ} (h : HomHadamardBound d c) : 0 ≤ c :=
  (norm_nonneg _).trans (h.diag 1)

theorem HomHadamardBound.dominated {d : ℕ+ → ℕ+ → ℂ} {c : ℝ} (h : HomHadamardBound d c)
    (A : HomOp) : KamDominated (fun i j => d i j * kamEntry A i j) (kamEntry A) c := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [norm_mul]
    calc ‖d i j‖ * ‖kamEntry A i j‖ ≤ c / |(i : ℝ) - (j : ℝ)| * ‖kamEntry A i j‖ :=
          mul_le_mul_of_nonneg_right (h.off i j hij) (norm_nonneg _)
      _ = c * ‖kamEntry A i j‖ / |(i : ℝ) - (j : ℝ)| := by ring
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (h.diag i) (norm_nonneg _)

theorem HomHadamardBound.schur {d : ℕ+ → ℕ+ → ℂ} {c : ℝ} (h : HomHadamardBound d c) (A : HomOp) :
    KamSchurBound (fun i j => d i j * kamEntry A i j) (c * homKS * ‖A‖) := by
  have := kamSchurBound_of_dominated A (h.dominated A)
  rwa [max_eq_left h.nonneg] at this

/-- The Hadamard image `(d_ij A_ij)` of one operator. -/
noncomputable def homHadamardOp {d : ℕ+ → ℕ+ → ℂ} {c : ℝ} (h : HomHadamardBound d c)
    (A : HomOp) : HomOp :=
  kamSchurCLM (fun i j => d i j * kamEntry A i j) (h.schur A)

theorem homHadamardOp_hasSum {d : ℕ+ → ℕ+ → ℂ} {c : ℝ} (h : HomHadamardBound d c) (A : HomOp)
    (v : HomL2) (i : ℕ+) :
    HasSum (fun j => d i j * kamEntry A i j * v j) (homHadamardOp h A v i) :=
  kamSchurCLM_hasSum _ v i

theorem norm_homHadamardOp_le {d : ℕ+ → ℕ+ → ℂ} {c : ℝ} (h : HomHadamardBound d c) (A : HomOp) :
    ‖homHadamardOp h A‖ ≤ c * homKS * ‖A‖ :=
  norm_kamSchurCLM_le _

/-- **Entries of the Hadamard image**: `(H_d A)_ij = d_ij A_ij`. -/
theorem homHadamard_entry {d : ℕ+ → ℕ+ → ℂ} {c : ℝ} (h : HomHadamardBound d c) (A : HomOp)
    (i j : ℕ+) : kamEntry (homHadamardOp h A) i j = d i j * kamEntry A i j := by
  unfold kamEntry
  have h1 := homHadamardOp_hasSum h A (kamBasis ℂ j) i
  have h2 : HasSum (fun k => d i k * kamEntry A i k * kamBasis ℂ j k)
      (d i j * kamEntry A i j) := by
    convert hasSum_ite_eq j (d i j * kamEntry A i j) using 1
    funext k
    by_cases hk : k = j
    · subst hk; simp [kamBasis]
    · simp [kamBasis, hk]
  exact h1.unique h2

/-- `(A v)_i = ∑_j A_ij v_j` for every bounded operator on `ℓ²_ℂ`. -/
theorem homOp_hasSum (A : HomOp) (v : HomL2) (i : ℕ+) :
    HasSum (fun j => kamEntry A i j * v j) (A v i) := by
  have hs := lp.hasSum_single (p := 2) (by norm_num) v
  have h1 := (hs.mapL A).mapL (lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 i)
  have hev : ∀ w : HomL2, lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 i w = w i := fun w => rfl
  simp only [hev] at h1
  convert h1 using 1
  funext j
  have : lp.single 2 j (v j) = v j • kamBasis ℂ j := by
    ext k
    by_cases hk : k = j
    · subst hk; simp [kamBasis]
    · simp [kamBasis, hk]
  rw [this, map_smul]
  simp [kamEntry, mul_comm]

/-- An operator is determined by its entries. -/
theorem homOp_ext_entries {A B : HomOp} (h : ∀ i j, kamEntry A i j = kamEntry B i j) : A = B := by
  refine ContinuousLinearMap.ext fun v => ?_
  ext i
  exact (homOp_hasSum A v i).unique (by simpa only [h] using homOp_hasSum B v i)


@[simp] theorem kamEntry_add (A B : HomOp) (i j : ℕ+) :
    kamEntry (A + B) i j = kamEntry A i j + kamEntry B i j := by
  simp [kamEntry]

@[simp] theorem kamEntry_smul (c : ℂ) (A : HomOp) (i j : ℕ+) :
    kamEntry (c • A) i j = c * kamEntry A i j := by
  simp [kamEntry]

/-- **The Hadamard map** `H_d : 𝓛 → 𝓛` (blueprint `bpW:w4:schur` (i)), a continuous linear map of
norm `≤ c K_S`. -/
noncomputable def homHadamardCLM {d : ℕ+ → ℕ+ → ℂ} {c : ℝ} (h : HomHadamardBound d c) :
    HomOp →L[ℂ] HomOp :=
  LinearMap.mkContinuous
    { toFun := homHadamardOp h
      map_add' := fun A B => homOp_ext_entries fun i j => by
        simp only [homHadamard_entry, kamEntry_add]; ring
      map_smul' := fun a A => homOp_ext_entries fun i j => by
        simp only [homHadamard_entry, kamEntry_smul, RingHom.id_apply]; ring }
    (c * homKS) (fun A => norm_homHadamardOp_le h A)

@[simp] theorem homHadamardCLM_apply {d : ℕ+ → ℕ+ → ℂ} {c : ℝ} (h : HomHadamardBound d c)
    (A : HomOp) : homHadamardCLM h A = homHadamardOp h A := rfl

/-- **Hadamard division, (i)** (blueprint `bpW:w4:schur` (i)): `‖H_d‖ ≤ c K_S`. -/
theorem norm_homHadamardCLM_le {d : ℕ+ → ℕ+ → ℂ} {c : ℝ} (h : HomHadamardBound d c) :
    ‖homHadamardCLM h‖ ≤ c * homKS :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg h.nonneg (zero_le_one.trans one_le_homKS)) _

/-- **Hadamard division, (i), transposition** (blueprint `bpW:w4:schur` (i)): if `N` has the
transposed entries of `M`, then `H_{dᵀ}(N)` has the transposed entries of `H_d(M)`. -/
theorem homHadamard_transpose_entry {d : ℕ+ → ℕ+ → ℂ} {c : ℝ} (h : HomHadamardBound d c)
    (hT : HomHadamardBound (fun i j => d j i) c) (M N : HomOp)
    (hMN : ∀ i j, kamEntry N i j = kamEntry M j i) (i j : ℕ+) :
    kamEntry (homHadamardOp hT N) i j = kamEntry (homHadamardOp h M) j i := by
  rw [homHadamard_entry, homHadamard_entry, hMN]

/-- **Hadamard division, (iii)** (blueprint `bpW:w4:schur` (iii)): for diagonal `d`
(`d_ij = 0` for `i ≠ j`) with `|d_ii| ≤ c` the bound improves to `c`. -/
theorem norm_homHadamardOp_diag_le {d : ℕ+ → ℕ+ → ℂ} {c : ℝ} (h : HomHadamardBound d c)
    (hd : ∀ i j, i ≠ j → d i j = 0) (A : HomOp) : ‖homHadamardOp h A‖ ≤ c * ‖A‖ := by
  have hμ : ∀ i, ‖d i i * kamEntry A i i‖ ≤ c * ‖A‖ := fun i => by
    rw [norm_mul]
    exact mul_le_mul (h.diag i) (norm_kamEntry_diag_le A i) (norm_nonneg _) h.nonneg
  have hD : homHadamardOp h A = weightedDiagCLM (fun i => d i i * kamEntry A i i) hμ := by
    refine homOp_ext_entries fun i j => ?_
    rw [homHadamard_entry]
    by_cases hij : i = j
    · subst hij
      simp [kamEntry, weightedDiagCLM, kamBasis]
    · simp [hd i j hij, kamEntry, weightedDiagCLM, kamBasis, hij]
  rw [hD]
  exact norm_diagCLM_le _ hμ


/-- The matrix entry `M_ij` of the operator `M ∈ 𝓛` (`ℓ^N_{a,p} → ℓ^N_{a,p_+}`, `p_+ = pb`) whose
weighted matrix is `A`: `A_ij = μ_i M_ij ν_j` with `μ_i = ω_{a,p_+}(i+2)`, `ν_j = ω_{a,p}(j+2)⁻¹`.
    -/
noncomputable def homNormalEntry_gen (a p pb : ℝ) (A : HomOp) (i j : ℕ+) : ℂ :=
  ((ellWeight a p (j + 2) / ellWeight a pb (i + 2) : ℝ) : ℂ) * kamEntry A i j

/-- The Hadamard map acts entrywise on the matrix entries of `M`. -/
theorem homNormalEntry_hadamard_gen (a p pb : ℝ) {d : ℕ+ → ℕ+ → ℂ} {c : ℝ}
    (h : HomHadamardBound d c) (A : HomOp) (i j : ℕ+) :
    homNormalEntry_gen a p pb (homHadamardOp h A) i j = d i j * homNormalEntry_gen a p pb A i j :=
        by
  unfold homNormalEntry_gen
  rw [homHadamard_entry]
  ring

theorem ellWeight_succ_exponent (a p : ℝ) (J : ℕ+) :
    ellWeight a (p + 1) J = (J : ℝ) * ellWeight a p J := by
  unfold ellWeight
  rw [Real.rpow_add_one (by exact_mod_cast J.ne_zero)]
  ring

/-- The ratio of two weights with the same exponential factor is a power. -/
theorem ellWeight_div_ellWeight (a p pb : ℝ) (J : ℕ+) :
    ellWeight a p J / ellWeight a pb J = (J : ℝ) ^ (p - pb) := by
  unfold ellWeight
  have h : (0 : ℝ) < (J : ℝ) := by exact_mod_cast J.pos
  rw [Real.rpow_sub h]
  field_simp [(Real.exp_pos (a * J)).ne']

/-- **Diagonal bound** (blueprint `bpW:w4:schur` (iii), general `p_+`):
`(i+2)^{p_+-p} |M_ii| ≤ ‖M‖`. -/
theorem homDiagonal_bound_gen (a p pb : ℝ) (A : HomOp) (i : ℕ+) :
    ((i : ℝ) + 2) ^ (pb - p) * ‖homNormalEntry_gen a p pb A i i‖ ≤ ‖A‖ := by
  have hJ : (((i + 2 : ℕ+) : ℕ+) : ℝ) = (i : ℝ) + 2 := by push_cast; ring
  have hq : ellWeight a p (i + 2) / ellWeight a pb (i + 2) = ((i : ℝ) + 2) ^ (-(pb - p)) := by
    rw [ellWeight_div_ellWeight, hJ]
    congr 1
    ring
  have hpos : (0 : ℝ) < (i : ℝ) + 2 := by positivity
  unfold homNormalEntry_gen
  rw [norm_mul, hq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _)]
  have : ((i : ℝ) + 2) ^ (pb - p) * (((i : ℝ) + 2) ^ (-(pb - p)) * ‖kamEntry A i i‖) =
      ‖kamEntry A i i‖ := by
    rw [← mul_assoc, ← Real.rpow_add hpos]
    simp
  rw [this]
  exact norm_kamEntry_diag_le A i

end KAM.Wave
