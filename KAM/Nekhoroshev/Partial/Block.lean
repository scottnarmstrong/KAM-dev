/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Domain
public import KAM.Nekhoroshev.Partial.Hessian
public import KAM.Nekhoroshev.Partial.BlockData
public import KAM.Nekhoroshev.Partial.Nonresonant
public import KAM.Nekhoroshev.Partial.Resonant
import KAM.Nekhoroshev.Partial.Threshold

/-!
# Stopped block stability (Part 11, package N11-N)

`block` (`bpN:p11:block`): Pöschel's Theorem 1 with slow parameters. The block data come from
`block_data`; the slow coordinates are rescaled by `λ = w/r`, and the nonresonant or resonant
stability proposition applies. Design `docs/tracks/N/design/N11-LEAN-DESIGN.md`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Nekhoroshev

variable {n k : ℕ}

/-! ### Rescaling the slow pair -/

/-- Coordinate factors of the slow rescaling: `1` on the fast actions, `t` on the slow pair. -/
def nblkFactor (t : ℝ) : Fin (n + (k + k)) → ℝ := Fin.append (fun _ => 1) (fun _ => t)

/-- Multiply the slow pair of a real extended point by `t`. -/
def nblkScale (t : ℝ) (z : ER n k) : ER n k := (z.1, fun j => nblkFactor t j * z.2 j)

theorem nblkFactor_fast (t : ℝ) (i : Fin n) : nblkFactor (k := k) t (Fin.castAdd (k+k) i) = 1 := by
  simp [nblkFactor]

theorem nblkFactor_slow (t : ℝ) (i : Fin (k + k)) : nblkFactor (n := n) t (Fin.natAdd n i) = t := by
  simp [nblkFactor]

theorem nblkScale_cancel {t : ℝ} (ht : t ≠ 0) (z : ER n k) : nblkScale t (nblkScale t⁻¹ z) = z := by
  refine Prod.ext rfl (funext fun j => ?_)
  simp only [nblkScale, ← mul_assoc]
  refine ext_cases (P := fun j => nblkFactor t j * nblkFactor t⁻¹ j * z.2 j = z.2 j) ?_ ?_ ?_ j
  · intro i; simp [nblkFactor_fast]
  · intro i; rw [nblkFactor_slow, nblkFactor_slow, mul_inv_cancel₀ ht, one_mul]
  · intro i; rw [nblkFactor_slow, nblkFactor_slow, mul_inv_cancel₀ ht, one_mul]

theorem fastAction_nblkScale (t : ℝ) (z : ER n k) : fastAction (nblkScale t z) = fastAction z := by
  funext i; simp [fastAction, nblkScale, nblkFactor_fast]

theorem slowPair_nblkScale (t : ℝ) (z : ER n k) : slowPair (nblkScale t z) = t • slowPair z := by
  ext i
  · simp [slowPair, nblkScale, nblkFactor_slow]
  · simp [slowPair, nblkScale, nblkFactor_slow]

theorem nblk_slowScale_extCx (t : ℝ) (z : ER n k) :
    slowScale t (extCx z) = extCx (nblkScale t z) := by
  refine Prod.ext rfl (funext fun j => ?_)
  refine ext_cases (P := fun j => (slowScale t (extCx z)).2 j = (extCx (nblkScale t z)).2 j)
    ?_ ?_ ?_ j
  · intro i
    simp only [slowScale, extCx, nblkScale, fastAction, Fin.append_left, nblkFactor_fast, one_mul]
  · intro i
    simp only [slowScale, extCx, nblkScale, slowPair, Fin.append_right, Fin.append_left,
      nblkFactor_slow, Complex.ofReal_mul]
  · intro i
    simp only [slowScale, extCx, nblkScale, slowPair, Fin.append_right, nblkFactor_slow,
      Complex.ofReal_mul]

/-- The rescaling as a continuous linear map. -/
def nblkCLM (t : ℝ) : ER n k →L[ℝ] ER n k :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    ((ContinuousLinearMap.pi fun j => nblkFactor t j • ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ _ _))

theorem nblkCLM_apply (t : ℝ) (z : ER n k) : nblkCLM t z = nblkScale t z := by
  refine Prod.ext rfl (funext fun j => ?_)
  simp [nblkCLM, nblkScale]

/-- For `t ≠ 0` the rescaling is a continuous linear equivalence. -/
def nblkCLE {t : ℝ} (ht : t ≠ 0) : ER n k ≃L[ℝ] ER n k :=
  ContinuousLinearEquiv.equivOfInverse (nblkCLM t) (nblkCLM t⁻¹)
    (fun z => by
      rw [nblkCLM_apply, nblkCLM_apply]
      simpa only [inv_inv] using nblkScale_cancel (inv_ne_zero ht) z)
    (fun z => by rw [nblkCLM_apply, nblkCLM_apply]; exact nblkScale_cancel ht z)

theorem nblkCLE_apply {t : ℝ} (ht : t ≠ 0) (z : ER n k) : nblkCLE ht z = nblkScale t z :=
  nblkCLM_apply t z

theorem nblkScale_single (t : ℝ) (j : Fin (n + (k + k))) :
    nblkScale t ((0 : Fin n → ℝ), Pi.single j (1:ℝ)) =
      nblkFactor t j • ((0 : Fin n → ℝ), Pi.single j (1:ℝ)) := by
  refine Prod.ext (by simp [nblkScale]) (funext fun m => ?_)
  by_cases hm : m = j
  · subst hm; simp [nblkScale]
  · simp [nblkScale, Pi.single_apply, hm]

theorem nblkScale_fst (t : ℝ) (v : Fin n → ℝ) :
    nblkScale (k := k) t (v, (0 : Fin (n + (k + k)) → ℝ)) = (v, 0) := by
  refine Prod.ext rfl (funext fun j => ?_)
  simp [nblkScale]

theorem nblkScale_fst' (t : ℝ) (w : ER n k) : (nblkScale t w).1 = w.1 := rfl

theorem nblkScale_snd (t : ℝ) (w : ER n k) (j : Fin (n + (k + k))) :
    (nblkScale t w).2 j = nblkFactor t j * w.2 j := rfl

theorem fastAction_extCx_nblkScale (t : ℝ) (v : ER n k) :
    fastAction (extCx (nblkScale t v)) = fastAction (extCx v) := by
  funext i; simp [fastAction, extCx, nblkScale, nblkFactor_fast]

theorem nblk_isOpen (b : PartialBlock n k) (R : ℝ) : IsOpen (b.realDom R) := by
  have hc : Continuous fun z : ER n k => extCx z :=
    (continuous_pi fun i =>
        Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_fst)).prodMk
      (continuous_pi fun i =>
        Complex.continuous_ofReal.comp ((continuous_apply i).comp continuous_snd))
  exact (KAM.Weighted.isOpen_Dom _ _ _).preimage hc

/-- The weighted field transforms under the slow rescaling `x = t x̃`, with `c t² = 2π`. -/
theorem nblk_field {t c : ℝ} (ht : t ≠ 0) (hc : c * t ^ 2 = 2 * Real.pi) {U : Set (ER n k)}
    (hU : IsOpen U) {Hs Hp : ER n k → ℝ} (hHs : EqOn Hs (Hp ∘ nblkScale t) U) {z : ER n k}
    (hz : z ∈ U) :
    realWfield c Hs z = nblkScale t⁻¹ (realWfield (2 * Real.pi) Hp (nblkScale t z)) := by
  have hD : fderiv ℝ Hs z = (fderiv ℝ Hp (nblkScale t z)).comp (nblkCLM t) := by
    have h1 : fderiv ℝ Hs z = fderiv ℝ (Hp ∘ nblkCLE ht) z :=
      (hHs.eventuallyEq_of_mem (hU.mem_nhds hz)).fderiv_eq.trans (by
        congr 1)
    rw [h1, ContinuousLinearEquiv.comp_right_fderiv, nblkCLE_apply]
    congr 1
  have hsl : ∀ j, fderiv ℝ Hs z ((0 : Fin n → ℝ), Pi.single j (1:ℝ)) =
      nblkFactor t j * fderiv ℝ Hp (nblkScale t z) ((0 : Fin n → ℝ), Pi.single j (1:ℝ)) := by
    intro j
    rw [hD, ContinuousLinearMap.comp_apply, nblkCLM_apply, nblkScale_single, map_smul,
      smul_eq_mul]
  have hfa : ∀ v : Fin n → ℝ, fderiv ℝ Hs z (v, (0 : Fin (n + (k + k)) → ℝ)) =
      fderiv ℝ Hp (nblkScale t z) (v, 0) := by
    intro v
    rw [hD, ContinuousLinearMap.comp_apply, nblkCLM_apply, nblkScale_fst]
  have hct : c * t = t⁻¹ * (2 * Real.pi) := by
    rw [← hc, eq_inv_mul_iff_mul_eq₀ ht]; ring
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · simp only [realWfield, nblkScale_fst']
    rw [hsl, nblkFactor_fast, one_mul]
  · refine ext_cases (P := fun j => (realWfield c Hs z).2 j =
      (nblkScale t⁻¹ (realWfield (2 * Real.pi) Hp (nblkScale t z))).2 j) ?_ ?_ ?_ j
    · intro i
      simp only [realWfield, nblkScale_snd, Fin.append_left, nblkFactor_fast, one_mul]
      rw [hfa]
    · intro i
      simp only [realWfield, nblkScale_snd, Fin.append_right, Fin.append_left, nblkFactor_slow]
      rw [hsl, nblkFactor_slow, ← mul_assoc, hct]
      ring
    · intro i
      simp only [realWfield, nblkScale_snd, Fin.append_right, nblkFactor_slow]
      rw [hsl, nblkFactor_slow]
      linear_combination (-(fderiv ℝ Hp (nblkScale t z)
        ((0 : Fin n → ℝ), Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1))) * hct

/-- Transport of the physical orbit and field to the rescaled block coordinates `x̃ = x/λ`. -/
theorem nblk_transport (b : PartialBlock n k) (hr : 0 < b.rB) (hw : 0 < b.w)
    {Hc : EC n k → ℂ} {Hp : ER n k → ℝ}
    (hH : ∀ v ∈ b.realDom b.rB, (Hc (extCx v)).re = Hp (nblkScale b.lam v))
    {W : Set (ER n k)} (hW : ∀ v ∈ b.realDom b.rB, nblkScale b.lam v ∈ W)
    {F : ER n k → ER n k} (hF : EqOn F (realWfield (2*Real.pi) Hp) W)
    {J : Set ℝ} {y : ℝ → ER n k} (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u) :
    EqOn (fun w => nblkScale b.lam⁻¹ (F (nblkScale b.lam w)))
      (realWfield b.c (realHamiltonianExt b b.rB Hc)) (b.realDom b.rB) ∧
    ∀ u ∈ J, HasDerivAt (fun u => nblkScale b.lam⁻¹ (y u))
      (nblkScale b.lam⁻¹ (F (nblkScale b.lam (nblkScale b.lam⁻¹ (y u))))) u := by
  have hlam : b.lam ≠ 0 := (div_pos hw hr).ne'
  have hcl : b.c * b.lam ^ 2 = 2 * Real.pi := by
    show 2*Real.pi/b.lam^2 * b.lam^2 = 2*Real.pi
    field_simp
  refine ⟨fun w hw' => ?_, fun u hu => ?_⟩
  · have hHs : EqOn (realHamiltonianExt b b.rB Hc) (Hp ∘ nblkScale b.lam) (b.realDom b.rB) :=
      fun v hv => by
        simp only [realHamiltonianExt, Set.indicator_of_mem hv, Function.comp_apply]
        exact hH v hv
    rw [nblk_field hlam hcl (nblk_isOpen b b.rB) hHs hw']
    exact congrArg (nblkScale b.lam⁻¹) (hF (hW w hw'))
  · have h1 := (nblkCLM b.lam⁻¹).hasFDerivAt.comp_hasDerivAt u (hy u hu)
    have e : (⇑(nblkCLM b.lam⁻¹) ∘ y) = fun u => nblkScale b.lam⁻¹ (y u) :=
      funext fun u => nblkCLM_apply _ _
    rw [e, nblkCLM_apply] at h1
    rwa [nblkScale_cancel hlam]

/-- The rescaled block domain lies in the physical domain of `domain_field`. -/
theorem nblk_dom (a : PartialData n k) {μ r : ℝ} {Ic : Fin n → ℝ} (hr : 0 < r)
    (hd : 0 < (constants a).d μ) (hrr0 : r ≤ (constants a).r0) {z : ER n k}
    (hz : z ∈ (block_setting a μ Ic r).realDom r) :
    nblkScale (block_setting a μ Ic r).lam z ∈ physicalDomain Ic (constants a).r0
      ((constants a).d μ/4) (innerCore a.D (3*(constants a).d μ/4)) := by
  have hw : 0 < (constants a).d μ/4 := by positivity
  have hlam : 0 < (block_setting a μ Ic r).lam := div_pos hw hr
  have hlam' : (block_setting a μ Ic r).lam ≠ 0 := hlam.ne'
  have hr' : r ≠ 0 := hr.ne'
  obtain ⟨-, J, ⟨x, hxS, rfl⟩, hJ⟩ := hz
  have hco : ∀ j, ‖(extCx z).2 j - Fin.append (fun i => (Ic i : ℂ))
      (Fin.append (fun i => ((x.1 i/(block_setting a μ Ic r).lam : ℝ) : ℂ))
        (fun i => ((x.2 i/(block_setting a μ Ic r).lam : ℝ) : ℂ))) j‖ < r :=
    fun j => (norm_le_pi_norm (_ - _) j).trans_lt hJ
  have hsc : ∀ q y : ℝ, ‖q - y/(block_setting a μ Ic r).lam‖ < r →
      ‖(block_setting a μ Ic r).lam * q - y‖ < (constants a).d μ/4 := by
    intro q y h
    have e : (block_setting a μ Ic r).lam * q - y =
        (block_setting a μ Ic r).lam * (q - y/(block_setting a μ Ic r).lam) := by
      field_simp
    rw [e, norm_mul, Real.norm_of_nonneg hlam.le]
    calc (block_setting a μ Ic r).lam * ‖q - y/(block_setting a μ Ic r).lam‖
        < (block_setting a μ Ic r).lam * r := mul_lt_mul_of_pos_left h hlam
      _ = (constants a).d μ/4 := by
        show (constants a).d μ/4/r*r = (constants a).d μ/4; field_simp
  refine ⟨?_, x, hxS, ?_⟩
  · rw [fastAction_nblkScale]
    refine lt_of_lt_of_le ((pi_norm_lt_iff hr).2 fun i => ?_) hrr0
    have := hco (Fin.castAdd (k+k) i)
    simpa [extCx, fastAction, ← Complex.ofReal_sub, Complex.norm_real] using this
  · rw [slowPair_nblkScale, Prod.norm_def, max_lt_iff]
    refine ⟨(pi_norm_lt_iff hw).2 fun i => ?_, (pi_norm_lt_iff hw).2 fun i => ?_⟩
    · have := hco (Fin.natAdd n (Fin.castAdd k i))
      simp only [extCx, Fin.append_right, Fin.append_left, ← Complex.ofReal_sub,
        Complex.norm_real] at this
      simpa [slowPair] using hsc _ _ this
    · have := hco (Fin.natAdd n (Fin.natAdd k i))
      simp only [extCx, Fin.append_right, ← Complex.ofReal_sub, Complex.norm_real] at this
      simpa [slowPair] using hsc _ _ this

/-! ### The block theorem -/

theorem block (a : PartialData n k) (hne : a.G.Nonempty) {μ σ : ℝ} (hμ : 0 < μ)
    (hσ : DefiniteSign a σ) (hε : (constants a).eps μ ≤ (constants a).eps0)
    (hd : (constants a).d μ ≤ a.ρ) (hκ : 6 ≤ (constants a).kappa μ)
    (hSL : 256*k*a.ρ*(constants a).R0/((constants a).d μ)^2 ≤ (constants a).K μ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (hP : IsPartialPerturbation a.G' a.D a.ρ P)
    {Ic : Fin n → ℝ} (hIc : Ic ∈ a.G) (F : ER n k → ER n k)
    (hF : EqOn F (realWfield (2*Real.pi)
      (fun z => (liftFast (signedH a σ) (extCx z)+signedF a σ μ P (extCx z)).re))
      (physicalDomain Ic (constants a).r0 ((constants a).d μ/4)
        (innerCore a.D (3*(constants a).d μ/4))))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u) (hinit : fastAction (y 0) = Ic)
    (hx : slowPair (y 0) ∈ innerCore a.D (3*(constants a).d μ/4))
    {t1 : ℝ} (ht1 : t1 ∈ J) (htT : |t1| ≤ (constants a).blockTime μ)
    (hstop : ∀ u ∈ uIcc 0 t1, slowPair (y u) ∈ innerCore a.D ((constants a).d μ)) :
    ∀ u ∈ uIcc 0 t1, ‖fastAction (y u)-Ic‖ ≤ (constants a).R0/(2*(constants a).K μ) := by
  classical
  obtain ⟨hg, hm, -⟩ := a.definite
  obtain ⟨hs, hm1, hM1, hr0, hA, he0, hR0, hκC, -⟩ :=
    (constants a).nthr_pos a.hρ hg hm a.hMc
  have hcn : (constants a).n = n := rfl
  have hdpos : 0 < (constants a).d μ := Real.rpow_pos_of_pos hμ _
  have hεpos : 0 < (constants a).eps μ := div_pos (mul_pos hκC hμ) (by positivity)
  have hK1 : 1 ≤ (constants a).K μ := by
    show 1 ≤ ((constants a).eps0/(constants a).eps μ) ^ (1/(2*((constants a).n:ℝ)))
    exact Real.one_le_rpow ((one_le_div hεpos).2 hε) (by positivity)
  have hKpos : 0 < (constants a).K μ := one_pos.trans_le hK1
  obtain ⟨hmM, hconvAll⟩ := hessian_at_sign a hne hσ
  have hA1 : 1 ≤ (constants a).A := by
    show 1 ≤ 40*a.Mc/a.m
    rw [le_div_iff₀ hm]; linarith
  have hm1M1 : (constants a).m1 ≤ (constants a).M1 := by
    show a.m/(2*Real.pi) ≤ a.Mc/(2*Real.pi); gcongr
  -- bl-block: the block data.
  obtain ⟨Λ, r, -, hrΘ, hrR, hr, hnr, ⟨δ, -, hδ, hnear⟩, hlip, hε1, hε2⟩ :=
    block_data a hne hμ hε hσ hκ hIc
  have hrr0 : r ≤ (constants a).r0 :=
    hrR.trans ((div_le_self hR0.le hK1).trans (div_le_self hr0.le hA1))
  have hwpos : 0 < (block_setting a μ Ic r).w := by
    show 0 < (constants a).d μ/4; positivity
  -- bl-sl: the slow-loss condition, from (B2).
  have hSLb : (block_setting a μ Ic r).SL (constants a).s := by
    show 64*Real.pi*k*(a.ρ/(4*Real.pi))*r ≤ ((constants a).d μ/4)^2
    have h1 : 256*k*a.ρ*(constants a).R0 ≤ (constants a).K μ * ((constants a).d μ)^2 :=
      (div_le_iff₀ (pow_pos hdpos 2)).1 hSL
    have h2 : r * (constants a).K μ ≤ (constants a).R0 := (le_div_iff₀ hKpos).1 hrR
    have h0 : (0:ℝ) ≤ 256*k*a.ρ := mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg k)) a.hρ.le
    have h3 : 256*k*a.ρ*r * (constants a).K μ ≤ ((constants a).d μ)^2 * (constants a).K μ := by
      calc 256*k*a.ρ*r * (constants a).K μ = 256*k*a.ρ*(r * (constants a).K μ) := by ring
        _ ≤ 256*k*a.ρ*(constants a).R0 := mul_le_mul_of_nonneg_left h2 h0
        _ ≤ ((constants a).d μ)^2 * (constants a).K μ := by linarith
    have h4 := le_of_mul_le_mul_right h3 hKpos
    have e : 64*Real.pi*k*(a.ρ/(4*Real.pi))*r = 16*k*a.ρ*r := by
      have := Real.pi_pos.ne'; field_simp; ring
    have e2 : ((constants a).d μ/4)^2 = ((constants a).d μ)^2/16 := by ring
    rw [e, e2]; linarith
  -- bl-ext: the extended system on the block.
  have hconv : FastConvex Ic r (constants a).m1 (constants a).M1 (signedH a σ) :=
    hconvAll Ic hIc r hr hrr0
  obtain ⟨-, hpert, hbound⟩ := domain a hμ hσ hIc hr hrr0 hd P hP
  have hn1 : 1 ≤ n := by have := a.hn; omega
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn1)
  have hsqrt' : Real.sqrt n ≠ 0 := hsqrt.ne'
  have hkap : 2*Real.pi*((constants a).K μ/Real.sqrt n)*(constants a).s =
      (constants a).kappa μ := by
    show _ = 2*Real.pi*(constants a).K μ*(constants a).s/Real.sqrt (constants a).n
    rw [hcn]; ring
  have hNF : ExtNFHyp (block_setting a μ Ic r) (constants a).s ((constants a).K μ/Real.sqrt n)
      ((9/8)*(constants a).M1*(constants a).K μ*r) (Real.sqrt n*(constants a).M1) (9/8)
      ((constants a).eps μ) (Λ : Set (Fin n → ℤ)) (signedH a σ) (blockPert a μ σ Ic r P) :=
    { n_pos := hn1
      k_pos := a.hk
      radius_pos := hr
      slow_width_pos := hwpos
      s_pos := hs
      K_pos := div_pos hKpos hsqrt
      alpha_pos := by positivity
      L_nonneg := by positivity
      p_gt := by norm_num
      eps_pos := hεpos
      symmetric := fun j => ⟨fun h => neg_mem h, fun h => by simpa using neg_mem h⟩
      hol := hconv.hol
      real := hconv.real
      nr := hnr
      lip := hlip
      divisor_size := by
        show (constants a).K μ/Real.sqrt n*(Real.sqrt n*(constants a).M1)*r ≤
          (9/8)*(constants a).M1*(constants a).K μ*r/(9/8)
        apply le_of_eq; field_simp
      slow := hSLb
      pert := hpert
      bound := hbound
      cutoff := by rw [hkap]; exact hκ }
  -- The rescaled orbit `ỹ = (θ, I, x/λ)` solves the scaled block system.
  have hlam : (block_setting a μ Ic r).lam ≠ 0 := (div_pos hwpos hr).ne'
  obtain ⟨hFt, hyt⟩ := nblk_transport (block_setting a μ Ic r) hr hwpos
    (Hc := liftFast (signedH a σ) + blockPert a μ σ Ic r P)
    (Hp := fun z => (liftFast (signedH a σ) (extCx z) + signedF a σ μ P (extCx z)).re)
    (fun v _ => by
      simp only [Pi.add_apply, blockPert, Function.comp_apply, liftFast, nblk_slowScale_extCx,
        fastAction_extCx_nblkScale])
    (fun v hv => nblk_dom a hr hdpos hrr0 hv) hF hy
  have hinit' : fastAction (nblkScale (block_setting a μ Ic r).lam⁻¹ (y 0)) =
      (block_setting a μ Ic r).Ic := by
    rw [fastAction_nblkScale]; exact hinit
  have hcore : ∀ u, slowPair (y u) ∈ innerCore a.D ((constants a).d μ) →
      (block_setting a μ Ic r).lam • slowPair (nblkScale (block_setting a μ Ic r).lam⁻¹ (y u)) ∈
        (block_setting a μ Ic r).S := by
    intro u hu
    rw [slowPair_nblkScale, smul_smul, mul_inv_cancel₀ hlam, one_smul]
    exact ⟨hu.1, (Metric.closedBall_subset_closedBall (by linarith)).trans hu.2⟩
  have hx' : (block_setting a μ Ic r).lam •
      slowPair (nblkScale (block_setting a μ Ic r).lam⁻¹ (y 0)) ∈ (block_setting a μ Ic r).S := by
    rw [slowPair_nblkScale, smul_smul, mul_inv_cancel₀ hlam, one_smul]; exact hx
  have hstop' : ∀ u ∈ uIcc 0 t1, (block_setting a μ Ic r).lam •
      slowPair (nblkScale (block_setting a μ Ic r).lam⁻¹ (y u)) ∈ (block_setting a μ Ic r).S :=
    fun u hu => hcore u (hstop u hu)
  have hrK : r/2 ≤ (constants a).R0/(2*(constants a).K μ) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith [(le_div_iff₀ hKpos).1 hrR]
  have hrΘpos : 0 ≤ (constants a).rTheta μ := by
    show 0 ≤ (constants a).r0/((constants a).A*(constants a).K μ)^(constants a).n
    positivity
  have hbt : (constants a).blockTime μ =
      (constants a).s*(constants a).m1*(constants a).rTheta μ/
        (240*(constants a).M1*(constants a).eps μ) *
        Real.exp ((2*Real.pi*((constants a).K μ/Real.sqrt n)*(constants a).s)/6) := by
    rw [hkap]; rfl
  intro u hu
  rw [← fastAction_nblkScale (block_setting a μ Ic r).lam⁻¹ (y u)]
  by_cases hΛ : Λ = ⊥
  · -- bl-theta: the nonresonant block.
    subst hΛ
    rw [AddSubgroup.coe_bot] at hNF
    have hq : KAM.NormalForm.conjExp (9/8:ℝ) = 9 := by norm_num [KAM.NormalForm.conjExp]
    have hsmall : (constants a).eps μ ≤ (9/8)*(constants a).M1*(constants a).K μ*r*
        (block_setting a μ Ic r).rB/(2^7*KAM.NormalForm.conjExp (9/8)*
          ((constants a).K μ/Real.sqrt n)) := by
      rw [hq]; exact hε2
    have htime : |t1| ≤ (constants a).s*(block_setting a μ Ic r).rB/(5*(constants a).eps μ)*
        Real.exp ((2*Real.pi*((constants a).K μ/Real.sqrt n)*(constants a).s)/6) := by
      refine htT.trans ?_
      rw [hbt]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : (constants a).m1*(constants a).rTheta μ ≤ (constants a).M1*r :=
        mul_le_mul hm1M1 hrΘ hrΘpos hM1.le
      have h2 : 0 ≤ (constants a).s*(constants a).eps μ := (mul_pos hs hεpos).le
      have h5 : 0 ≤ (constants a).M1*r := (mul_pos hM1 hr).le
      show (constants a).s*(constants a).m1*(constants a).rTheta μ*(5*(constants a).eps μ) ≤
        (constants a).s*r*(240*(constants a).M1*(constants a).eps μ)
      nlinarith [mul_le_mul_of_nonneg_left h1 h2]
    have := nonresonant (block_setting a μ Ic r) hNF hsmall _ hFt hJ h0 hyt hinit' hx' ht1 htime
      hstop' u hu
    exact this.trans hrK
  · -- bl-res: the resonant block.
    have hne' : NearResonance (Λ : Set (Fin n → ℤ)) (signedH a σ) (block_setting a μ Ic r).Ic
        ((constants a).m1*(block_setting a μ Ic r).rB/32) :=
      fun v hv => (hnear v hv).trans
        (mul_le_mul_of_nonneg_right hδ.le (Real.sqrt_nonneg _))
    have htime : |t1| ≤ (constants a).s*(constants a).m1*(block_setting a μ Ic r).rB/
        (240*(constants a).M1*(constants a).eps μ)*
          Real.exp ((2*Real.pi*((constants a).K μ/Real.sqrt n)*(constants a).s)/6) := by
      refine htT.trans ?_
      rw [hbt]
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hrΘ (mul_pos hs hm1).le
    have := resonant (block_setting a μ Ic r) hNF hconv hne' hε1 _ hFt hJ h0 hyt hinit' hx' ht1
      htime hstop' u hu
    exact ((norm_le_euclid _).1.trans this).trans hrK

end KAM.Nekhoroshev

end
