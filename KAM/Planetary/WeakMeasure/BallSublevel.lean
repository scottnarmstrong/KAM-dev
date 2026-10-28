/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.WeakMeasure.Basic
public import KAM.Planetary.WeakMeasure.ScalarSublevel
public import KAM.Planetary.WeakMeasure.MeasureTools

/-!
# Ball sublevel estimate (blueprint `bpP:p11a:ball-sublevel`, P11A-W5)

For `g` of class `C^q` near the closed Euclidean ball `U = {|y - y₀|₂ ≤ r}` with
`β ≤ |D^q g(y)(a^q)|` on `U` (`|a|₂ = 1`),
`vol {y ∈ U | |g y| ≤ ε} ≤ 2q (2r)^(n-1) (ε/β)^(1/q)` (`KAM.Planetary.ball_sublevel`).

Steps: a Householder matrix `Q` with `Q e_n = a` (`bpP:p11a:f-orth`, `p11_householder`); the
rotation `y = y₀ + Q (x', t)` preserves Lebesgue measure and the Euclidean ball
(`stepP:p11a:bs-rot`); each `t`-section is a sublevel set of `t ↦ g (y₁ + t a)` to which
`scalar_sublevel` applies (`stepP:p11a:bs-sections`, with the line chain rule
`p11_iteratedDeriv_line`); Tonelli over `x' ∈ [-r, r]^(n-1)` (`stepP:p11a:bs-tonelli`).
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped Matrix Topology

namespace KAM.Planetary

section Line

variable {n : ℕ}

/-- Chain rule along a line: `(d/dt)^k g (y₁ + t a) = D^k g (y₁ + t a) (a, …, a)`. -/
theorem p11_iteratedDeriv_line {q : ℕ} {V : Set (P11Vec n)} (hV : IsOpen V) {g : P11Vec n → ℝ}
    (hg : ContDiffOn ℝ q g V) (y1 a : P11Vec n) :
    ∀ k ≤ q, ∀ t : ℝ, y1 + t • a ∈ V →
      iteratedDeriv k (fun t : ℝ => g (y1 + t • a)) t =
        iteratedFDeriv ℝ k g (y1 + t • a) (fun _ => a) := by
  intro k
  induction k with
  | zero => intro _ t _; simp
  | succ k ih =>
    intro hk t ht
    have hW : IsOpen {t : ℝ | y1 + t • a ∈ V} := hV.preimage (by fun_prop)
    have heq : iteratedDeriv k (fun t : ℝ => g (y1 + t • a)) =ᶠ[𝓝 t]
        fun t : ℝ => iteratedFDeriv ℝ k g (y1 + t • a) (fun _ => a) :=
      Filter.eventuallyEq_of_mem (hW.mem_nhds ht) fun s hs => ih (by omega) s hs
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ k g) (y1 + t • a) :=
      (hg.contDiffAt (hV.mem_nhds ht)).differentiableAt_iteratedFDeriv
        (by exact_mod_cast Nat.lt_of_succ_le hk)
    have hφ : HasDerivAt (fun t : ℝ => y1 + t • a) a t := by
      simpa using ((hasDerivAt_id t).smul_const a).const_add y1
    have h1 := hD.hasFDerivAt.comp_hasDerivAt t hφ
    have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => P11Vec n) ℝ
      (fun _ => a)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 := h2.deriv
    simp only [Function.comp_def, ContinuousMultilinearMap.apply_apply] at h3
    rw [h3, iteratedFDeriv_succ_apply_left]
    rfl

end Line

section Euclid

variable {n : ℕ}

theorem p11euclid_sq (x : P11Vec n) : p11euclid x ^ 2 = x ⬝ᵥ x := by
  unfold p11euclid KAM.Nekhoroshev.euclid
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [dotProduct, sq]

theorem p11euclid_eq_one {a : P11Vec n} (ha : p11euclid a = 1) : a ⬝ᵥ a = 1 := by
  rw [← p11euclid_sq, ha, one_pow]

theorem p11euclid_mulVec {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q * Qᵀ = 1) (x : P11Vec n) :
    p11euclid (Q.mulVec x) = p11euclid x := by
  have hQ' : Qᵀ * Q = 1 := by
    have := mul_eq_one_comm.1 hQ
    simpa using this
  have h : (Q.mulVec x) ⬝ᵥ (Q.mulVec x) = x ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hQ',
      Matrix.one_mulVec]
  have h2 : p11euclid (Q.mulVec x) ^ 2 = p11euclid x ^ 2 := by
    rw [p11euclid_sq, p11euclid_sq, h]
  exact (pow_left_inj₀ (p11euclid_nonneg _) (p11euclid_nonneg _) two_ne_zero).1 h2

theorem abs_apply_le_p11euclid (x : P11Vec n) (i : Fin n) : |x i| ≤ p11euclid x := by
  have h1 : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
  have h2 := (KAM.Nekhoroshev.norm_le_euclid x).1
  simpa using h1.trans h2

end Euclid

section Householder

variable {m : ℕ}

/-- `bpP:p11a:f-orth`: a unit vector is the last column of an orthogonal (Householder) matrix. -/
theorem p11_householder {a : P11Vec (m + 1)} (ha : p11euclid a = 1) :
    ∃ Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ,
      Q * Qᵀ = 1 ∧ Q.mulVec (Pi.single (Fin.last m) 1) = a := by
  classical
  set e : P11Vec (m + 1) := Pi.single (Fin.last m) 1 with he
  have haa := p11euclid_eq_one ha
  by_cases hae : a = e
  · exact ⟨1, by simp, by simp [hae]⟩
  set v : P11Vec (m + 1) := e - a with hv
  have hve : v ⬝ᵥ e = 1 - a (Fin.last m) := by simp [hv, he]
  have hvv : v ⬝ᵥ v = 2 * (1 - a (Fin.last m)) := by
    have hae' : a ⬝ᵥ e = a (Fin.last m) := by simp [he]
    have hee : e ⬝ᵥ e = 1 := by simp [he]
    simp only [hv, sub_dotProduct, dotProduct_sub, dotProduct_comm e a, hae', hee, haa]
    ring
  have hvne : v ≠ 0 := fun h => hae (by rw [hv, sub_eq_zero] at h; exact h.symm)
  have hpos : 0 < v ⬝ᵥ v := by
    rcases lt_or_eq_of_le (dotProduct_self_star_nonneg (R := ℝ) v) with h | h
    · simpa using h
    · exact absurd (dotProduct_self_eq_zero.1 (by simpa using h.symm)) hvne
  set c : ℝ := 2 / (v ⬝ᵥ v) with hc
  have hcv : c * (v ⬝ᵥ v) = 2 := by rw [hc]; field_simp
  set Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    Matrix.of fun i j => (if i = j then 1 else 0) - c * v i * v j with hQ
  have hmv : ∀ (x : P11Vec (m + 1)) (i : Fin (m + 1)),
      Q.mulVec x i = x i - c * v i * (v ⬝ᵥ x) := by
    intro x i
    simp only [hQ, Matrix.mulVec, dotProduct, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => by ring
  have hQt : Qᵀ = Q := by
    ext i j
    simp only [hQ, Matrix.transpose_apply, Matrix.of_apply]
    by_cases h : i = j
    · subst h; ring
    · simp [h, Ne.symm h]
      ring
  refine ⟨Q, ?_, ?_⟩
  · rw [hQt]
    ext i k
    have h1 : (Q * Q) i k = Q.mulVec (fun j => Q j k) i := rfl
    have h2 : v ⬝ᵥ (fun j => Q j k) = - v k := by
      have : v ⬝ᵥ (fun j => Q j k) = v k - c * (v ⬝ᵥ v) * v k := by
        simp only [hQ, dotProduct, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
          mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
          Finset.sum_mul, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => by ring
      rw [this, hcv]; ring
    rw [h1, hmv, h2]
    simp only [hQ, Matrix.of_apply, Matrix.one_apply]
    by_cases hik : i = k <;> simp [hik]
  · ext i
    rw [hmv]
    have h3 : c * (v ⬝ᵥ e) = 1 := by
      rw [hve]
      have h2 : 1 - a (Fin.last m) ≠ 0 := by
        intro h; rw [h] at hvv; rw [hvv] at hpos; simp at hpos
      rw [hc, hvv]; field_simp
    rw [mul_assoc, mul_comm (v i), ← mul_assoc, h3, one_mul]
    simp [hv]

end Householder

section Main

variable {m : ℕ}

theorem p11euclid_snoc (x' : Fin m → ℝ) (t : ℝ) :
    p11euclid (Fin.snoc x' t : Fin (m + 1) → ℝ) ^ 2 = p11euclid x' ^ 2 + t ^ 2 := by
  rw [p11euclid_sq, p11euclid_sq]
  simp [dotProduct, Fin.sum_univ_castSucc, sq]

theorem p11_snoc_eq (x' : Fin m → ℝ) (t : ℝ) :
    (Fin.snoc x' t : Fin (m + 1) → ℝ) =
      (Fin.snoc x' 0 : Fin (m + 1) → ℝ) + t • (Pi.single (Fin.last m) 1 : Fin (m + 1) → ℝ) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp [Fin.castSucc_ne_last]

end Main

/-- `bpP:p11a:ball-sublevel`. -/
theorem ball_sublevel {n q : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q)
    {V : Set (P11Vec n)} (hV : IsOpen V) {y0 a : P11Vec n} {r beta eps : ℝ}
    (hr : 0 < r) (ha : p11euclid a=1) (hb : 0 < beta) (he : 0 < eps)
    (hsub : {y | p11euclid (y-y0) ≤ r} ⊆ V) {g : P11Vec n → ℝ}
    (hg : ContDiffOn ℝ q g V)
    (hlow : ∀ y, p11euclid (y-y0) ≤ r →
      beta ≤ |iteratedFDeriv ℝ q g y (fun _ => a)|) :
    volume {y | p11euclid (y-y0) ≤ r ∧ |g y| ≤ eps} ≤
      ENNReal.ofReal (2*q*(2*r)^(n-1)*(eps/beta)^((q : ℝ)⁻¹)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨Q, hQ, hQe⟩ := p11_householder ha
  set Φ : P11Vec (m + 1) → P11Vec (m + 1) := fun x => y0 + Q.mulVec x with hΦdef
  have hΦ := p11_measurePreserving_orthogonal hQ y0
  have hnorm : ∀ z, p11euclid (Φ z - y0) = p11euclid z := by
    intro z; simp [hΦdef, p11euclid_mulVec hQ]
  set K : Set (P11Vec (m + 1)) := {y | p11euclid (y - y0) ≤ r} with hK
  have hKc : IsClosed K :=
    isClosed_le (p11euclid_continuous.comp (continuous_sub_right y0)) continuous_const
  set S : Set (P11Vec (m + 1)) := {y | p11euclid (y - y0) ≤ r ∧ |g y| ≤ eps} with hSdef
  have hSc : IsClosed S := by
    have : S = K ∩ g ⁻¹' Icc (-eps) eps := by
      ext y; simp [hSdef, hK, abs_le]
    rw [this]
    exact (hg.continuousOn.mono hsub).preimage_isClosed_of_isClosed hKc isClosed_Icc
  have hSm : MeasurableSet S := hSc.measurableSet
  set S' : Set (P11Vec (m + 1)) := Φ ⁻¹' S with hS'
  have h1 : volume S = volume S' := (hΦ.measure_preimage hSm.nullMeasurableSet).symm
  have hS'm : MeasurableSet S' := hΦ.measurable hSm
  have hproj : ∀ x ∈ S', ∀ j : Fin m, |x (Fin.castSucc j)| ≤ r := by
    intro x hx j
    have : p11euclid x ≤ r := by
      have := hx.1
      rwa [hnorm] at this
    exact (abs_apply_le_p11euclid x _).trans this
  set c : ℝ := 2 * q * (eps / beta) ^ ((q : ℝ)⁻¹) with hc
  have hsec : ∀ x' : Fin m → ℝ, volume {t : ℝ | Fin.snoc x' t ∈ S'} ≤ ENNReal.ofReal c := by
    intro x'
    set y1 : P11Vec (m + 1) := y0 + Q.mulVec (Fin.snoc x' 0) with hy1
    have hΦt : ∀ t : ℝ, Φ (Fin.snoc x' t) = y1 + t • a := by
      intro t
      simp only [hΦdef, hy1, p11_snoc_eq x' t, Matrix.mulVec_add, Matrix.mulVec_smul, hQe]
      abel
    have hmem : ∀ t : ℝ, (Fin.snoc x' t : Fin (m + 1) → ℝ) ∈ S' ↔
        p11euclid (Fin.snoc x' t : Fin (m + 1) → ℝ) ≤ r ∧ |g (y1 + t • a)| ≤ eps := by
      intro t
      show p11euclid (Φ (Fin.snoc x' t) - y0) ≤ r ∧ |g (Φ (Fin.snoc x' t))| ≤ eps ↔ _
      rw [hnorm, hΦt]
    set ρ := p11euclid x' with hρ
    set s : ℝ := Real.sqrt (r ^ 2 - ρ ^ 2) with hs
    have hsect : {t : ℝ | Fin.snoc x' t ∈ S'} ⊆ {t ∈ Icc (-s) s | |g (y1 + t • a)| ≤ eps} := by
      intro t ht
      obtain ⟨h1, h2⟩ := (hmem t).1 ht
      refine ⟨?_, h2⟩
      have : t ^ 2 ≤ r ^ 2 - ρ ^ 2 := by
        have := p11euclid_snoc x' t
        nlinarith [p11euclid_nonneg (Fin.snoc x' t : Fin (m + 1) → ℝ)]
      exact abs_le.1 (Real.abs_le_sqrt this)
    rcases (Real.sqrt_nonneg (r ^ 2 - ρ ^ 2)).eq_or_lt with h0 | hpos
    · have hsub0 : {t : ℝ | Fin.snoc x' t ∈ S'} ⊆ {0} := by
        intro t ht
        have := (hsect ht).1
        rw [show s = 0 from h0.symm] at this
        simp only [neg_zero, Icc_self, mem_singleton_iff] at this ⊢
        exact this
      have : volume {t : ℝ | Fin.snoc x' t ∈ S'} = 0 :=
        measure_mono_null hsub0 (measure_singleton 0)
      rw [this]; exact zero_le
    · have hr2 : 0 < r ^ 2 - ρ ^ 2 := Real.sqrt_pos.1 hpos
      have hs2 : s ^ 2 = r ^ 2 - ρ ^ 2 := Real.sq_sqrt hr2.le
      have hball : ∀ t : ℝ, |t| ≤ s → p11euclid (Fin.snoc x' t : Fin (m + 1) → ℝ) ≤ r := by
        intro t ht
        have ht2 : t ^ 2 ≤ s ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
        have := p11euclid_snoc x' t
        refine (sq_le_sq₀ (p11euclid_nonneg _) hr.le).1 ?_
        nlinarith
      have hballK : ∀ t : ℝ, |t| ≤ s → p11euclid (y1 + t • a - y0) ≤ r := fun t ht => by
        rw [← hΦt t, hnorm]; exact hball t ht
      have hmemV : ∀ t : ℝ, |t| ≤ s → y1 + t • a ∈ V := fun t ht => hsub (hballK t ht)
      have hf : ContDiffOn ℝ q (fun t : ℝ => g (y1 + t • a)) (Icc (-s) s) :=
        hg.comp (by fun_prop : ContDiff ℝ q fun t : ℝ => y1 + t • a).contDiffOn
          (fun t ht => hmemV t (abs_le.2 ht))
      have hlow' : ∀ t ∈ Ioo (-s) s, beta ≤ |iteratedDeriv q (fun t : ℝ => g (y1 + t • a)) t| := by
        intro t ht
        have habs : |t| ≤ s := abs_le.2 ⟨ht.1.le, ht.2.le⟩
        rw [p11_iteratedDeriv_line hV hg y1 a q le_rfl t (hmemV t habs)]
        exact hlow _ (hballK t habs)
      have := scalar_sublevel hq (a := -s) (b := s) (by linarith) hb he hf hlow'
      exact (measure_mono hsect).trans this
  have key := p11_volume_le_of_sections hS'm hr.le hproj hsec
  rw [h1]
  refine key.trans (le_of_eq ?_)
  rw [Nat.add_sub_cancel, hc]
  congr 1
  ring



end KAM.Planetary
