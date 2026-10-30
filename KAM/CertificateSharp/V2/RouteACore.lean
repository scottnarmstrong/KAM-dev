/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteAQ
public import KAM.CertificateSharp.V2.ClassicalQ
public import KAM.CertificateSharp.Sharp

/-!
# The part of the route A test common to the two stages

* `capQ`, `initQ`: the caps and the initial values of `routeAOkI`;
* `finalOk`: the smallness `e < X⋆ γ⁴ δ₀^{4τ}`, the displacement bound and the room of the ray;
* `boxNormUp`, `rayBound`: the rational `Θ̂ ≥ σω ‖ω*‖` and the ray bound `σh = Θ̂/‖ω*‖`.

The route A theorems take `N.Θ = σω ‖ω*‖` as an equality, for an exact real `‖ω*‖`. They are applied
at `σh = Θ̂/‖ω*‖ ≥ σω`, for which the equality holds with the rational `Θ̂`: all the numbers of the
run stay rational and independent of `ω*`. The price is the conclusion `sinf < σh` instead of
`sinf < σω`; `finalOk` recovers it from the displacement bound, `disp < (σω - s) L`,
where `L` is the lower bound of `‖ω*‖` on the box (`ray_lt_of_disp`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Torus KAM.Certificate CertArith KAM.Sharp KAM.Sharp2 KAM.Sharp2.RouteA
  KAM.Iso.Sharp2.RouteA KAM.Iso.Sharp KAM.Sharp.Engine

/-- An upper bound of the sup norm of a vector in the box: `max_i (|c_i| + r_i)`. -/
def boxNormUp (box : FreqBox) : ℚ := box.foldr (fun b acc => max (|b.1| + b.2) acc) 0

theorem abs_add_le_boxNormUp (box : FreqBox) (i : ℕ) :
    |(box.getD i (0, 0)).1| + (box.getD i (0, 0)).2 ≤ boxNormUp box := by
  induction box generalizing i with
  | nil => simp [boxNormUp]
  | cons b box ih =>
    cases i with
    | zero => exact le_max_left _ _
    | succ i =>
      simp only [boxNormUp, List.foldr_cons]
      exact (ih i).trans (le_max_right _ _)

theorem boxNormUp_nonneg (box : FreqBox) : 0 ≤ boxNormUp box := by
  induction box with
  | nil => simp [boxNormUp]
  | cons b box ih => exact ih.trans (le_max_right _ _)

theorem norm_le_boxNormUp {n : ℕ} {box : FreqBox} {ω : Fin n → ℝ} (h : FreqEncloses n box ω) :
    ‖ω‖ ≤ (boxNormUp box : ℝ) := by
  refine (pi_norm_le_iff_of_nonneg (by exact_mod_cast boxNormUp_nonneg box)).2 fun i => ?_
  have h1 := h i
  have h2 : ((|(box.getD i.val (0, 0)).1| + (box.getD i.val (0, 0)).2 : ℚ) : ℝ) ≤
      (boxNormUp box : ℝ) := by exact_mod_cast abs_add_le_boxNormUp box i.val
  push_cast at h2
  rw [Real.norm_eq_abs]
  calc |ω i| = |(ω i - (box.getD i.val (0, 0)).1) + (box.getD i.val (0, 0)).1| := by ring_nf
    _ ≤ |ω i - (box.getD i.val (0, 0)).1| + |((box.getD i.val (0, 0)).1 : ℝ)| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- The caps of `capI`, for the budgets `μ/2`, `ν/2`. -/
def capQ (Q : NumQ) (μ ν : ℚ) : Fin 9 → ℚ :=
  ![μ / 2, Q.sK, Q.sB, Q.sT, Q.sLt, Q.sN, Q.sNt, Q.t, ν / 2]

/-- The initial values of `initI`. -/
def initQ (iLt iN iNt iH σK σB σT μ : ℚ) : Fin 9 → ℚ :=
  ![0, σK - μ, σB - μ, σT - μ, iLt, iN, iNt, iH, 0]

theorem cast_capQ (Q : NumQ) (μ ν : ℚ) :
    capI Q.toNum ((μ : ℝ) / 2) ((ν : ℝ) / 2) = fun i => (capQ Q μ ν i : ℝ) := by
  funext i
  fin_cases i <;> simp [capI, capQ, NumQ.toNum]

theorem cast_initQ (iLt iN iNt iH σK σB σT μ : ℚ) :
    initI ⟨iLt, iN, iNt, iH⟩ σK σB σT μ = fun i => (initQ iLt iN iNt iH σK σB σT μ i : ℝ) := by
  funext i
  fin_cases i <;> simp [initI, initQ]

/-- The final comparisons, at the parameters `p`, the box of `‖ω*‖` and `X⋆`. -/
def finalOk (Q : NumQ) (n : ℕ) (p : CertParams) (box : FreqBox) (Xs : ℚ) : Bool :=
  decide (p.err < Xs * p.γ ^ 4 * Q.δ0 ^ (4 * p.tau)) &&
    decide (max (max (sharpIsoC2Q n p.tau (cRRQ n p.tau) p.M p.σK p.σB p.σT p.γbar p.rho p.rhoInf)
        (sharpIsoC3Q n p.tau (cRRQ n p.tau) p.M p.σK p.σB p.σT p.γbar p.rho p.rhoInf))
      (max (Q.c2Q Xs) (Q.c3Q Xs)) * p.err ≤ p.disp * (p.γ ^ 2 * p.rho ^ (2 * p.tau))) &&
    decide (p.disp < (p.σω - p.s) * freqNormLo box)

/-- The three real inequalities of `Admissible`, from the bound of the constants. -/
theorem min_mul_div_lt {A ρτ γ e X d : ℝ} (hρτ : 0 < ρτ) (hγ : 0 < γ) (hX : 0 < X) (hd : 0 < d)
    (he : 0 ≤ e) (h : e < X * γ ^ 4 * d) : min A (ρτ / (X * d)) * e / (γ ^ 4 * ρτ) < 1 := by
  have h4 : 0 < γ ^ 4 * ρτ := by positivity
  have h1 : min A (ρτ / (X * d)) * e / (γ ^ 4 * ρτ) ≤ (ρτ / (X * d)) * e / (γ ^ 4 * ρτ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) he) h4.le
  refine h1.trans_lt ?_
  have e1 : (ρτ / (X * d)) * e / (γ ^ 4 * ρτ) = e / (X * γ ^ 4 * d) := by
    field_simp
  rw [e1, div_lt_one (by positivity)]
  exact h

theorem max_mul_div_le {a2 c2 a3 c3 B e g D : ℝ} (hg : 0 < g) (he : 0 ≤ e)
    (h1 : max a2 a3 ≤ B) (h2 : c2 ≤ B) (h3 : c3 ≤ B) (h : B * e ≤ D * g) :
    max (max a2 c2) (max a3 c3) * e / g ≤ D := by
  rw [div_le_iff₀ hg]
  refine (mul_le_mul_of_nonneg_right ?_ he).trans h
  exact max_le (max_le ((le_max_left _ _).trans h1) h2) (max_le ((le_max_right _ _).trans h1) h3)

variable {n : ℕ} {α : Type} [CertArith α]

/-- The bounds of `C₂♯`, `C₃♯` at the certificate's parameters: the first half of
`sharpTest_arith`, without its smallness. -/
theorem sharp_disp_le [LawfulCertArith α] {c : TorusCertificate n α} (hs : checkStatic c = true) :
    max (sharpIsoC2 n (c.params.tau : ℝ) (cohConstR n (c.params.tau : ℝ)) c.params.M c.params.σK
        c.params.σB c.params.σT c.params.γbar (c.params.tau : ℝ) c.params.rho c.params.rhoInf)
      (sharpIsoC3 n (c.params.tau : ℝ) (cohConstR n (c.params.tau : ℝ)) c.params.M c.params.σK
        c.params.σB c.params.σT c.params.γbar (c.params.tau : ℝ) c.params.rho c.params.rhoInf) ≤
    ((max (sharpIsoC2Q n c.params.tau (cRRQ n c.params.tau) c.params.M c.params.σK c.params.σB
        c.params.σT c.params.γbar c.params.rho c.params.rhoInf)
      (sharpIsoC3Q n c.params.tau (cRRQ n c.params.tau) c.params.M c.params.σK c.params.σB
        c.params.σT c.params.γbar c.params.rho c.params.rhoInf) : ℚ) : ℝ) := by
  have S := checkStatic_sound hs
  have hτ1 : (1 : ℝ) ≤ (c.params.tau : ℝ) := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast S.hn
    linarith [S.hτ]
  have hD : Data n (cohConstR n (c.params.tau : ℝ)) (cRRQ n c.params.tau) c.params.M c.params.σK
      c.params.σB c.params.σT c.params.γbar c.params.μ c.params.nuRay :=
    { hn := by have := S.hn; omega
      hcR0 := (cohData_russmann (n := n) hτ1).cR_pos
      hcR := cohConstR_le_cRRQ n c.params.tau
      hM := by exact_mod_cast S.hM
      hσK := by exact_mod_cast S.hσK
      hσB := by exact_mod_cast S.hσB
      hσT := by exact_mod_cast S.hσT
      hγb := by exact_mod_cast S.hγbar
      hμ := by exact_mod_cast S.hμ
      hν := by exact_mod_cast S.hν }
  have hρinf : (0 : ℚ) < c.params.rhoInf := by exact_mod_cast S.hρinf
  have hρρ : c.params.rhoInf < c.params.rho := by exact_mod_cast S.hρinfρ
  have P := pos_of c.params.tau hD
  have dA := domA hD P
  have dB := domB hD P dA
  push_cast
  exact max_le_max (sharpIsoC2_le hD P dB hρinf hρρ) (sharpIsoC3_le hD P dB hρinf hρρ)

/-- **`finalOk` gives `Admissible` and the room of the ray.** -/
theorem finalOk_sound [LawfulCertArith α] {c : TorusCertificate n α} {Q : NumQ} {Xs : ℚ}
    (hs : checkStatic c = true) (hτ : Q.τ = c.params.tau) (hρ : Q.ρ = c.params.rho)
    (hρi : Q.ρinf = c.params.rhoInf) (hτ1 : 1 ≤ Q.τ) (hXs : 0 < Xs)
    (h : finalOk Q n c.params c.freqBox Xs = true) {ωstar : Fin n → ℝ}
    (hω : FreqEncloses n c.freqBox ωstar) :
    Admissible c.params
      (min (sharpIsoC1 n (c.params.tau : ℝ) (cohConstR n (c.params.tau : ℝ)) c.params.M c.params.σK
        c.params.σB c.params.σT c.params.γbar c.params.μ c.params.nuRay (c.params.tau : ℝ)
        c.params.rho c.params.rhoInf) (c1A Q.toNum Xs))
      (max (sharpIsoC2 n (c.params.tau : ℝ) (cohConstR n (c.params.tau : ℝ)) c.params.M c.params.σK
        c.params.σB c.params.σT c.params.γbar (c.params.tau : ℝ) c.params.rho c.params.rhoInf)
        (c2I Q.toNum Xs))
      (max (sharpIsoC3 n (c.params.tau : ℝ) (cohConstR n (c.params.tau : ℝ)) c.params.M c.params.σK
        c.params.σB c.params.σT c.params.γbar (c.params.tau : ℝ) c.params.rho c.params.rhoInf)
        (c3I Q.toNum Xs)) ∧
      (c.params.disp : ℝ) < ((c.params.σω : ℝ) - c.params.s) * ‖ωstar‖ := by
  have S := checkStatic_sound hs
  simp only [finalOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hXs' : (0 : ℝ) < Xs := by exact_mod_cast hXs
  have hρ0 : (0 : ℝ) < c.params.rho := S.hρinf.trans S.hρinfρ
  have hd0 : 0 < (Q.δ0 : ℝ) := by
    rw [← NumQ.cast_δ0, hρ, hρi]
    exact delta0_pos (by norm_num) S.hρinfρ
  have e4 : (4 * (c.params.tau : ℝ)) = ((4 * c.params.tau : ℕ) : ℝ) := by push_cast; ring
  have e2 : (2 * (c.params.tau : ℝ)) = ((2 * c.params.tau : ℕ) : ℝ) := by push_cast; ring
  have hg : (0 : ℝ) < (c.params.γ : ℝ) ^ 2 * (c.params.rho : ℝ) ^ (2 * (c.params.tau : ℝ)) := by
    have := Real.rpow_pos_of_pos hρ0 (2 * (c.params.tau : ℝ))
    have := S.hγ
    positivity
  have hS := sharp_disp_le hs
  have hτQ : ((Q.τ : ℕ) : ℝ) = (c.params.tau : ℝ) := by rw [hτ]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hc1 : c1A Q.toNum Xs = (c.params.rho : ℝ) ^ (4 * (c.params.tau : ℝ)) /
        ((Xs : ℝ) * (Q.δ0 : ℝ) ^ (4 * c.params.tau)) := by
      show (Q.ρ : ℝ) ^ (4 * (Q.τ : ℝ)) / ((Xs : ℝ) *
        delta0 3 (Q.ρ : ℝ) Q.ρinf ^ (4 * (Q.τ : ℝ))) = _
      rw [NumQ.cast_δ0, hτQ, hρ, e4, Real.rpow_natCast, Real.rpow_natCast]
    rw [hc1]
    refine min_mul_div_lt (Real.rpow_pos_of_pos hρ0 _) S.hγ hXs' (pow_pos hd0 _) S.he0 ?_
    have := (Rat.cast_lt (K := ℝ)).mpr h1
    push_cast at this
    exact this
  · have hb := (Rat.cast_le (K := ℝ)).mpr h2
    rw [e2, Real.rpow_natCast] at hg ⊢
    rw [NumQ.cast_c2 hτ1, NumQ.cast_c3 hτ1]
    push_cast at hb
    refine max_mul_div_le hg S.he0 ?_ ?_ ?_ hb
    · exact (hS.trans_eq (by push_cast; rfl)).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)
  · have hlen : c.freqBox.length = n := by
      simp only [checkStatic, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, and_assoc] at hs
      exact hs.1
    have hle := freqNormLo_le_norm hlen hω
    have h3' := (Rat.cast_lt (K := ℝ)).mpr h3
    push_cast at h3'
    have hp : (0 : ℝ) ≤ (c.params.σω : ℝ) - c.params.s := by linarith [S.hsσ]
    exact h3'.trans_le (mul_le_mul_of_nonneg_left hle hp)

/-- The ray bound `σh = Θ̂/‖ω*‖` of the route A wrappers. -/
theorem rayBound {σ : ℝ} {Θ : ℚ} {box : FreqBox} {ωstar : Fin n → ℝ} (hσ0 : 0 ≤ σ)
    (hΘ : σ * (boxNormUp box : ℝ) ≤ Θ) (hω : FreqEncloses n box ωstar) (hω0 : ωstar ≠ 0) :
    σ ≤ (Θ : ℝ) / ‖ωstar‖ ∧ (Θ : ℝ) = (Θ : ℝ) / ‖ωstar‖ * ‖ωstar‖ := by
  have hn : 0 < ‖ωstar‖ := norm_pos_iff.2 hω0
  refine ⟨?_, (div_mul_cancel₀ _ hn.ne').symm⟩
  rw [le_div_iff₀ hn]
  exact (mul_le_mul_of_nonneg_left (norm_le_boxNormUp hω) hσ0).trans hΘ

end KAM.CertificateSharp.V2

end
