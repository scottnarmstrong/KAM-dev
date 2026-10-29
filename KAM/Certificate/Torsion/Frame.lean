/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Gram
public import KAM.Certificate.NormBridge
public import KAM.Torus.FrozenAgreement
public import KAM.Frozen.Iso.Defs.ExtendedTorsionAverage

/-!
# The bordered torsion of a certified embedding: frame calculus

The analytic identities behind the torsion models (SO design §1.9), for an embedding `K`
holomorphic on `ℂⁿ` whose Gram matrix is invertible on the open strip `T_ρ`:

* `fderiv_tangentMat_eq_sum_partials`: `(D L[v])_{sj} = Σ_l v_l ∂_l L_{sj}` (`L = DK`);
* `fderiv_normalMat_apply`: `D N[v] = Ω₀ (D L[v] G⁻¹ + L D(G⁻¹)[v])` with
  `D(G⁻¹)[v] = -G⁻¹ (D L[v]ᵀ L + Lᵀ D L[v]) G⁻¹`;
* `linMat_apply_eq`: `(DX_H ∘ K)_{ab} = ± ∂_{a'} ∂_b H (K)` (`a' = a.swap`, sign `hamSign a`);
* `fderiv_apply_normalFrame`: the last row `DH(K) N_b = Σ_a ∂_a H(K) N_{ab}`;
* `continuousOn_extendedTorsion`: every entry of the frozen `extendedTorsion` is continuous
  on `T_ρ` when `H` is holomorphic on an open set containing `K(T_ρ)`;
* the second derivatives of a certified embedding (`CertModel.ofDeriv2` and its contract
  `CertModel.Encloses.ofDeriv2`, `fderiv_tangentMat_eval_inl`, `fderiv_tangentMat_eval_inr`).

`torsionIdx n` is the list index of the bordered rows and columns: `inl i ↦ i`, `inr () ↦ n`.
-/

@[expose] public noncomputable section

open scoped Matrix Matrix.Norms.Operator

namespace KAM.Certificate

open KAM KAM.Torus CertArith

/-- Row/column index of the bordered torsion: `inl i ↦ i`, `inr () ↦ n`. -/
def torsionIdx (n : ℕ) : Fin n ⊕ Unit → ℕ := Sum.elim (fun i => i.val) (fun _ => n)

theorem torsionIdx_lt (n : ℕ) (a : Fin n ⊕ Unit) : torsionIdx n a < n + 1 := by
  rcases a with a | _
  · exact Nat.lt_succ_of_lt a.isLt
  · exact Nat.lt_succ_self n

/-! ### Generic frame calculus -/

section Generic

variable {n : ℕ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ρ : ℝ}

/-- The directional derivative of `L = DK` as the sum of its partials. -/
theorem fderiv_tangentMat_eq_sum_partials {θ : Fin n → ℂ} (hL : DifferentiableAt ℂ (tangentMat K) θ)
    (v : Fin n → ℂ) (s : Fin n ⊕ Fin n) (j : Fin n) :
    fderiv ℂ (tangentMat K) θ v s j =
      ∑ l, v l * fderiv ℂ (fun y => tangentMat K y s j) θ (Pi.single l 1) := by
  have hv : v = ∑ l, v l • (Pi.single l (1 : ℂ) : Fin n → ℂ) := by
    ext i; simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    fderiv_matrix_apply hL]

/-- The derivative of the normal frame `N = Ω₀ L G⁻¹` on the strip where `G` is invertible:
`D N[v] = Ω₀ (D L[v] G⁻¹ + L D(G⁻¹)[v])`, `D(G⁻¹)[v] = -G⁻¹ (D L[v]ᵀ L + Lᵀ D L[v]) G⁻¹`. -/
theorem fderiv_normalMat_apply (hK : Differentiable ℂ K)
    (hG : ∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det) {θ : Fin n → ℂ}
    (hθ : θ ∈ complexStrip n ρ) (v : Fin n → ℂ) :
    fderiv ℂ (normalMat K) θ v = omegaZeroMatrix n *
      (fderiv ℂ (tangentMat K) θ v * (gramMatrix K θ)⁻¹ + tangentMat K θ *
        -((gramMatrix K θ)⁻¹ * ((fderiv ℂ (tangentMat K) θ v)ᵀ * tangentMat K θ +
          (tangentMat K θ)ᵀ * fderiv ℂ (tangentMat K) θ v) * (gramMatrix K θ)⁻¹)) := by
  have hS := isOpen_complexStrip n ρ
  have hL := differentiableOn_tangentMat (r := ρ) hK.differentiableOn
  have hLa : DifferentiableAt ℂ (tangentMat K) θ := hL.differentiableAt (hS.mem_nhds hθ)
  have hinv := holomorphic_inverse hS (differentiableOn_gramMatrix (r := ρ) hK.differentiableOn)
    fun z hz => (hG z hz).ne_zero
  have hIa : DifferentiableAt ℂ (fun z => (gramMatrix K z)⁻¹) θ :=
    hinv.1.differentiableAt (hS.mem_nhds hθ)
  have hDG : fderiv ℂ (gramMatrix K) θ v = (fderiv ℂ (tangentMat K) θ v)ᵀ * tangentMat K θ +
      (tangentMat K θ)ᵀ * fderiv ℂ (tangentMat K) θ v := by
    have hGf : gramMatrix K = fun y => (tangentMat K y)ᵀ * tangentMat K y :=
      funext (gramMatrix_eq_tangentMat_transpose_mul K)
    rw [hGf, fderiv_matrix_mul_apply hLa.matrix_transpose hLa, fderiv_matrix_transpose_apply]
  have hN : normalMat K = fun y => (omegaZeroMatrix n * tangentMat K y) * (gramMatrix K y)⁻¹ :=
    rfl
  rw [hN, fderiv_matrix_mul_apply ((differentiableAt_const _).matrix_mul hLa) hIa,
    fderiv_matrix_const_mul_apply _ hLa, hinv.2 θ hθ v, hDG]
  simp only [Matrix.mul_add, Matrix.mul_assoc]

/-- The torsion is holomorphic on the strip when `N` and `X_N` are. -/
theorem differentiableOn_torsion_of_frame {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ}
    (hN : DifferentiableOn ℂ (normalMat K) (complexStrip n ρ))
    (hX : DifferentiableOn ℂ (normalFieldMat H K ω) (complexStrip n ρ)) :
    DifferentiableOn ℂ (torsion H K ω) (complexStrip n ρ) :=
  ((hN.matrix_transpose.matrix_mul (differentiableOn_const _)).matrix_mul hX).congr fun _ hθ =>
    torsion_eq_mat H K ω (hN.differentiableAt ((isOpen_complexStrip n ρ).mem_nhds hθ))

/-- The last row: `DH(z) N_b = Σ_a ∂_a H(z) N_{ab}`. -/
theorem fderiv_apply_normalFrame (H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ)
    (z : (Fin n → ℂ) × (Fin n → ℂ)) (θ : Fin n → ℂ) (b : Fin n) :
    fderiv ℂ H z (normalFrame K θ b) =
      ∑ a, fderiv ℂ H z (phaseBasis a) * normalMat K θ a b := by
  conv_lhs => rw [← sum_sumVec_smul_phaseBasis (normalFrame K θ b)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, sumVec_normalFrame]

/-- Entries of `sqMat`: column `b` is the image of the phase basis vector `b`. -/
theorem sqMat_apply_eq_phaseBasis
    (U : ((Fin n → ℂ) × (Fin n → ℂ)) →L[ℂ] (Fin n → ℂ) × (Fin n → ℂ)) (a b : Fin n ⊕ Fin n) :
    sqMat U a b = sumVec n (U (phaseBasis b)) a := by
  have h := congrFun (sqMat_mulVec U (phaseBasis b)) a
  simpa [phaseBasis, Matrix.mulVec_single_one] using h

/-- `(DX_H ∘ K)_{ab} = hamSign a · ∂_{a.swap} ∂_b H (K)` for `C²` `H`. -/
theorem linMat_apply_eq {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {θ : Fin n → ℂ}
    (hH : ContDiffAt ℂ 2 H (K θ)) (a b : Fin n ⊕ Fin n) :
    linMat H K θ a b =
      hamSign a * iteratedFDeriv ℂ 2 H (K θ) ![phaseBasis a.swap, phaseBasis b] := by
  have hsym := hH.isSymmSndFDerivAt (by simp)
  rw [linMat, sqMat_apply_eq_phaseBasis, sumVec_fderiv_hamiltonianVectorFieldℂ hH,
    iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  rw [hsym]

/-- Every entry of the frozen bordered torsion is continuous on the strip, for `K` holomorphic
with invertible Gram matrix on `T_ρ` and `H` holomorphic on an open `D ⊇ K(T_ρ)`. -/
theorem continuousOn_extendedTorsion {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {D : Set ((Fin n → ℂ) × (Fin n → ℂ))} (hD : IsOpen D) (hH : DifferentiableOn ℂ H D)
    (hK : Differentiable ℂ K) (hKD : ∀ θ ∈ complexStrip n ρ, K θ ∈ D)
    (hG : ∀ θ ∈ complexStrip n ρ, IsUnit (gramMatrix K θ).det) (ω : Fin n → ℝ)
    (a b : Fin n ⊕ Unit) :
    ContinuousOn (fun θ => KAM.Iso.extendedTorsion H K ω θ a b) (complexStrip n ρ) := by
  have hS := isOpen_complexStrip n ρ
  have hKd : DifferentiableOn ℂ K (complexStrip n ρ) := hK.differentiableOn
  have hN := differentiableOn_normalMat hKd hG
  have hdH : DifferentiableOn ℂ (fderiv ℂ H) D :=
    (holomorphic_regularity_of_finiteDimensional hD hH).1
  have hX : DifferentiableOn ℂ (hamiltonianVectorFieldℂ H) D := by
    unfold hamiltonianVectorFieldℂ
    exact DifferentiableOn.prodMk
      (differentiableOn_pi.2 fun i => hdH.clm_apply (differentiableOn_const _))
      (differentiableOn_pi.2 fun i => (hdH.clm_apply (differentiableOn_const _)).neg)
  have hdX := (holomorphic_regularity_of_finiteDimensional hD hX).1
  have hA : DifferentiableOn ℂ (linMat H K) (complexStrip n ρ) := by
    rw [differentiableOn_matrix_iff_entries]
    intro s t
    have h1 : DifferentiableOn ℂ (fun θ => fderiv ℂ (hamiltonianVectorFieldℂ H) (K θ))
        (complexStrip n ρ) := hdX.comp hKd hKD
    have h2 : DifferentiableOn ℂ (fun θ => sumVec n (fderiv ℂ (hamiltonianVectorFieldℂ H) (K θ)
        (phaseBasis t))) (complexStrip n ρ) :=
      (sumVecIso n).differentiable.comp_differentiableOn (h1.clm_apply (differentiableOn_const _))
    have h3 := differentiableOn_pi.1 h2 s
    simpa only [linMat, sqMat_apply_eq_phaseBasis] using h3
  have hDN : DifferentiableOn ℂ (fun θ => fderiv ℂ (normalMat K) θ (fun l => (ω l : ℂ)))
      (complexStrip n ρ) :=
    (holomorphic_regularity hS hN).1.clm_apply (differentiableOn_const _)
  have hT := differentiableOn_torsion_of_frame (H := H) (ω := ω) hN ((hA.matrix_mul hN).sub hDN)
  rcases a with a | ⟨⟩ <;> rcases b with b | ⟨⟩
  · exact (differentiableOn_matrix_iff_entries.1 hT a b).continuousOn
  · exact continuousOn_const
  · have h1 : ContinuousOn (fun θ => fderiv ℂ H (K θ)) (complexStrip n ρ) :=
      hdH.continuousOn.comp hK.continuous.continuousOn hKD
    show ContinuousOn (fun θ => fderiv ℂ H (K θ) (normalFrame K θ b)) (complexStrip n ρ)
    simp only [fderiv_apply_normalFrame]
    exact continuousOn_finsetSum _ fun a _ => (h1.clm_apply continuousOn_const).mul
      (differentiableOn_matrix_iff_entries.1 hN a b).continuousOn
  · exact continuousOn_const

end Generic

/-! ### Second derivatives of a certified embedding -/

section Embedding

variable {α : Type} [CertArith α] {n : ℕ}

omit [CertArith α] in
/-- The directional derivative of a character sum with arbitrary coefficients. -/
theorem hasFDerivAt_charSum (f : CertKey × CC α → ℂ) (l : Fin n) (θ : Fin n → ℂ) :
    ∀ L : List (CertKey × CC α), ∃ D : (Fin n → ℂ) →L[ℂ] ℂ,
      HasFDerivAt (fun y => (L.map fun t => f t * character (certKeyFun n t.1) y).sum) D θ ∧
      D (Pi.single l 1) = (2 * Real.pi) * (L.map fun t => f t * (Complex.I *
        ((certKeyFun n t.1 l : ℤ) : ℂ)) * character (certKeyFun n t.1) θ).sum
  | [] => ⟨0, by simpa using hasFDerivAt_const (0 : ℂ) θ, by simp⟩
  | t :: L => by
    obtain ⟨D, hD, hv⟩ := hasFDerivAt_charSum f l θ L
    refine ⟨f t • fderiv ℂ (character (certKeyFun n t.1)) θ + D, ?_, ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      exact (((differentiable_character _) θ).hasFDerivAt.const_mul (f t)).add hD
    · rw [_root_.add_apply, _root_.smul_apply, hv,
        fderiv_character_single, List.map_cons, List.sum_cons, smul_eq_mul]
      ring

/-- The second partial `∂_l ∂_j P` of a polynomial: `(2π)² Σ -k_j k_l c_k χ_k`. -/
theorem CertPoly.fderiv_fderiv_eval_single (P : CertPoly α) (j l : Fin n) (θ : Fin n → ℂ) :
    fderiv ℂ (fun y => fderiv ℂ (P.eval n) y (Pi.single j 1)) θ (Pi.single l 1) =
      (2 * Real.pi) ^ 2 * (P.terms.map fun t =>
        ((-(certKeyFun n t.1 j * certKeyFun n t.1 l) : ℤ) : ℂ) * t.2.toC *
          character (certKeyFun n t.1) θ).sum := by
  set f : CertKey × CC α → ℂ := fun t => Complex.I * ((certKeyFun n t.1 j : ℤ) : ℂ) * t.2.toC
  have hfun : (fun y => fderiv ℂ (P.eval n) y (Pi.single j 1)) =
      fun y => (2 * (Real.pi : ℂ)) *
        (P.terms.map fun t => f t * character (certKeyFun n t.1) y).sum :=
    funext fun y => CertPoly.fderiv_eval_single P j y
  obtain ⟨D, hD, hv⟩ := hasFDerivAt_charSum f l θ P.terms
  rw [hfun, (hD.const_mul (2 * (Real.pi : ℂ))).fderiv, _root_.smul_apply, hv,
    smul_eq_mul]
  have : ∀ t : CertKey × CC α, f t * (Complex.I * ((certKeyFun n t.1 l : ℤ) : ℂ)) *
      character (certKeyFun n t.1) θ = ((-(certKeyFun n t.1 j * certKeyFun n t.1 l) : ℤ) : ℂ) *
        t.2.toC * character (certKeyFun n t.1) θ := fun t => by
    simp only [f]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  simp only [this]
  ring

/-- `y ↦ ∂_j P(y)` is holomorphic. -/
theorem CertPoly.differentiable_fderiv_eval_single (P : CertPoly α) (j : Fin n) :
    Differentiable ℂ (fun y => fderiv ℂ (P.eval n) y (Pi.single j 1)) := by
  have hfun : (fun y => fderiv ℂ (P.eval n) y (Pi.single j 1)) =
      fun y => (2 * (Real.pi : ℂ)) * (P.terms.map fun t =>
        (Complex.I * ((certKeyFun n t.1 j : ℤ) : ℂ) * t.2.toC) *
          character (certKeyFun n t.1) y).sum :=
    funext fun y => CertPoly.fderiv_eval_single P j y
  rw [hfun]
  exact (differentiable_list_sum P.terms _
    fun t => (differentiable_character _).const_mul _).const_mul _

variable [LawfulCertArith α]

/-- Angle rows of `L = DK`: `L_{(inl i) j} = δ_ij + ∂_j((2π)^{dU_i} U_i)`. -/
theorem tangentMat_eval_inl (K : CertEmbedding α) (θ : Fin n → ℂ) (i j : Fin n) :
    tangentMat (K.eval n) θ (Sum.inl i) j = (Pi.single j 1 : Fin n → ℂ) i +
      (2 * (Real.pi : ℂ)) ^ (K.angleDeg.getD i.val 0) *
        fderiv ℂ ((realCompPoly n K.angle[i.val]?).eval n) θ (Pi.single j 1) := by
  rw [tangentMat_apply, sumVec_apply, Sum.elim_inl, CertEmbedding.fderiv_eval_fst]
  exact congrArg _ (fderiv_realComp_apply n _ _ θ _)

/-- Action rows of `L = DK`: `L_{(inr i) j} = ∂_j((2π)^{dA_i} A_i)`. -/
theorem tangentMat_eval_inr (K : CertEmbedding α) (θ : Fin n → ℂ) (i j : Fin n) :
    tangentMat (K.eval n) θ (Sum.inr i) j = (2 * (Real.pi : ℂ)) ^ (K.actionDeg.getD i.val 0) *
      fderiv ℂ ((realCompPoly n K.action[i.val]?).eval n) θ (Pi.single j 1) := by
  rw [tangentMat_apply, sumVec_apply, Sum.elim_inr, CertEmbedding.fderiv_eval_snd]
  exact fderiv_realComp_apply n _ _ θ _

/-- `∂_l L_{(inl i) j} = (2π)^{dU_i} ∂_l ∂_j U_i`. -/
theorem fderiv_tangentMat_eval_inl (K : CertEmbedding α) (θ : Fin n → ℂ) (i j l : Fin n) :
    fderiv ℂ (fun y => tangentMat (K.eval n) y (Sum.inl i) j) θ (Pi.single l 1) =
      (2 * (Real.pi : ℂ)) ^ (K.angleDeg.getD i.val 0) *
        fderiv ℂ (fun y => fderiv ℂ ((realCompPoly n K.angle[i.val]?).eval n) y
          (Pi.single j 1)) θ (Pi.single l 1) := by
  have hd := (realCompPoly n K.angle[i.val]?).differentiable_fderiv_eval_single j θ
  simp only [tangentMat_eval_inl]
  rw [fderiv_const_add, fderiv_const_mul hd, _root_.smul_apply, smul_eq_mul]

/-- `∂_l L_{(inr i) j} = (2π)^{dA_i} ∂_l ∂_j A_i`. -/
theorem fderiv_tangentMat_eval_inr (K : CertEmbedding α) (θ : Fin n → ℂ) (i j l : Fin n) :
    fderiv ℂ (fun y => tangentMat (K.eval n) y (Sum.inr i) j) θ (Pi.single l 1) =
      (2 * (Real.pi : ℂ)) ^ (K.actionDeg.getD i.val 0) *
        fderiv ℂ (fun y => fderiv ℂ ((realCompPoly n K.action[i.val]?).eval n) y
          (Pi.single j 1)) θ (Pi.single l 1) := by
  have hd := (realCompPoly n K.action[i.val]?).differentiable_fderiv_eval_single j θ
  simp only [tangentMat_eval_inr]
  rw [fderiv_const_mul hd, _root_.smul_apply, smul_eq_mul]

end Embedding

/-! ### The second-derivative model -/

section Deriv2

variable {α : Type} [CertArith α]

/-- The integer factor `-k_j k_l` of `∂_l ∂_j χ_k = (2π)² (-k_j k_l) χ_k`. -/
def deriv2Mult (j l : ℕ) (k : CertKey) : ℤ := -(k.getD j 0 * k.getD l 0)

/-- The coefficient `m c` (backend products). -/
def deriv2Coeff (m : ℤ) (c : CC α) : CC α := ⟨mul c.re (ofInt m), mul c.im (ofInt m)⟩

/-- The rounding error of `deriv2Coeff`. -/
def deriv2Err (m : ℤ) (c : CC α) : α := upAdd (mulErr c.re (ofInt m)) (mulErr c.im (ofInt m))

/-- The term `-k_j k_l c_k` (`none` if the factor vanishes), with its rounding error. -/
def deriv2Item (j l : ℕ) (t : CertKey × CC α) : Option (ErrTerm α) :=
  if deriv2Mult j l t.1 = 0 then none else
    some (t.1, deriv2Coeff (deriv2Mult j l t.1) t.2, deriv2Err (deriv2Mult j l t.1) t.2)

/-- The model of `∂_l ∂_j P` for exact data `P` at degree `d`: coefficients `-k_j k_l c_k`
(backend products, their errors in the radius) at degree `d + 2`. -/
def CertModel.ofDeriv2 (W : CertWeight) (j l : ℕ) (d : ℤ) (P : CertPoly α) : CertModel α :=
  ⟨d + 2, itemsPoly (P.terms.filterMap (deriv2Item j l)),
    errRadius W (P.terms.filterMap (deriv2Item j l))⟩

variable [LawfulCertArith α]

theorem norm_deriv2Coeff_sub (m : ℤ) (c : CC α) :
    ‖(m : ℂ) * c.toC - (deriv2Coeff m c).toC‖ ≤ val (deriv2Err m c) := by
  have e1 := LawfulCertArith.mul_err c.re (ofInt (α := α) m)
  have e2 := LawfulCertArith.mul_err c.im (ofInt (α := α) m)
  rw [LawfulCertArith.val_ofInt] at e1 e2
  refine (norm_le_of_re_im (A := val (mulErr c.re (ofInt (α := α) m)))
    (B := val (mulErr c.im (ofInt (α := α) m))) ?_ ?_).trans
      (LawfulCertArith.upAdd_ge _ _)
  · have : ((m : ℂ) * c.toC - (deriv2Coeff m c).toC).re =
        -(val (mul c.re (ofInt (α := α) m)) - val c.re * m) := by
      simp [deriv2Coeff, CC.toC]; ring
    rw [this, abs_neg]; exact e1
  · have : ((m : ℂ) * c.toC - (deriv2Coeff m c).toC).im =
        -(val (mul c.im (ofInt (α := α) m)) - val c.im * m) := by
      simp [deriv2Coeff, CC.toC]; ring
    rw [this, abs_neg]; exact e2

theorem deriv2Items_spec {n : ℕ} (j l : Fin n) (θ : Fin n → ℂ) :
    ∀ L : List (CertKey × CC α),
    ‖(L.map fun t => ((-(certKeyFun n t.1 j * certKeyFun n t.1 l) : ℤ) : ℂ) * t.2.toC *
        character (certKeyFun n t.1) θ).sum -
      errTermsEval n (L.filterMap (deriv2Item j.val l.val)) θ‖ ≤
      errTermsErr n (L.filterMap (deriv2Item j.val l.val)) θ
  | [] => by simp
  | t :: L => by
    have ih := deriv2Items_spec j l θ L
    have hk : -(certKeyFun n t.1 j * certKeyFun n t.1 l) = deriv2Mult j.val l.val t.1 := rfl
    by_cases h0 : deriv2Mult j.val l.val t.1 = 0
    · have hnone : deriv2Item j.val l.val t = none := by simp only [deriv2Item, h0, ↓reduceIte]
      rw [List.filterMap_cons_none hnone, List.map_cons, List.sum_cons, hk, h0]
      simpa using ih
    · have hsome : deriv2Item j.val l.val t = some (t.1,
          deriv2Coeff (deriv2Mult j.val l.val t.1) t.2,
          deriv2Err (deriv2Mult j.val l.val t.1) t.2) := by
        simp only [deriv2Item, h0, ↓reduceIte]
      rw [List.filterMap_cons_some hsome, List.map_cons, List.sum_cons, errTermsEval_cons,
        errTermsErr_cons, hk]
      simp only
      have e := norm_deriv2Coeff_sub (deriv2Mult j.val l.val t.1) t.2
      set χ := character (certKeyFun n t.1) θ
      set m := deriv2Mult j.val l.val t.1
      set S := (L.map fun t => ((-(certKeyFun n t.1 j * certKeyFun n t.1 l) : ℤ) : ℂ) *
        t.2.toC * character (certKeyFun n t.1) θ).sum
      have : (m : ℂ) * t.2.toC * χ + S -
          ((deriv2Coeff m t.2).toC * χ + errTermsEval n (L.filterMap (deriv2Item j.val l.val)) θ) =
          ((m : ℂ) * t.2.toC - (deriv2Coeff m t.2).toC) * χ +
            (S - errTermsEval n (L.filterMap (deriv2Item j.val l.val)) θ) := by ring
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have := mul_le_mul_of_nonneg_right e (norm_nonneg χ)
      linarith

/-- **Second-derivative model contract.** -/
theorem CertModel.Encloses.ofDeriv2 {n : ℕ} {W : CertWeight} {s N : ℕ}
    (hW : checkWeight W s N = true) (j l : Fin n) (d : ℤ) (P : CertPoly α) :
    (CertModel.ofDeriv2 W j.val l.val d P).Encloses n W.rho (fun θ => (2 * (Real.pi : ℂ)) ^ d *
      fderiv ℂ (fun y => fderiv ℂ (P.eval n) y (Pi.single j 1)) θ (Pi.single l 1)) := by
  intro θ hθ
  have hS := deriv2Items_spec j l θ P.terms
  have hR := errTermsErr_le_errRadius hW (P.terms.filterMap (deriv2Item j.val l.val)) hθ
  have h2pi : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have := Real.pi_pos; exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  beta_reduce
  rw [CertPoly.fderiv_fderiv_eval_single]
  simp only [CertModel.ofDeriv2, itemsPoly_eval]
  rw [zpow_add₀ h2pi, zpow_add₀ (by positivity : (2 * Real.pi) ≠ 0)]
  set S := (P.terms.map fun t => ((-(certKeyFun n t.1 j * certKeyFun n t.1 l) : ℤ) : ℂ) *
    t.2.toC * character (certKeyFun n t.1) θ).sum
  set E := errTermsEval n (P.terms.filterMap (deriv2Item j.val l.val)) θ
  have : (2 * (Real.pi : ℂ)) ^ d * ((2 * ((Real.pi : ℝ) : ℂ)) ^ 2 * S) -
      (2 * (Real.pi : ℂ)) ^ d * (2 * (Real.pi : ℂ)) ^ (2 : ℤ) * E =
      ((2 * (Real.pi : ℂ)) ^ d * (2 * (Real.pi : ℂ)) ^ (2 : ℤ)) * (S - E) := by
    rw [zpow_two, sq]; ring
  rw [this, norm_mul, norm_mul, norm_two_pi_zpow, norm_two_pi_zpow]
  exact mul_le_mul_of_nonneg_left (hS.trans hR) (by positivity)

end Deriv2

end KAM.Certificate

end
