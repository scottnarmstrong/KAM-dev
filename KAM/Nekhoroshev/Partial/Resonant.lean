/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Nekhoroshev.NormalForm.Setting
public import KAM.Nekhoroshev.Partial.NormalForm
public import KAM.Nekhoroshev.Partial.Energy
public import KAM.Nekhoroshev.Partial.Hessian
public import KAM.Nekhoroshev.Partial.Preimage
public import KAM.Nekhoroshev.Partial.Transfer
public import KAM.Nekhoroshev.Partial.CompositionCoeff
public import KAM.Weighted.Projections

/-!
# Resonant block stability (Part 11, package N11-M2)

`resonant` (`bpN:p11:resonant`): on a resonant block of a fast-convex Hamiltonian the fast
actions of an orbit that starts at the block centre move by at most `r_B/2` (Euclidean).
Design `docs/tracks/N/design/N11-LEAN-DESIGN.md`.

Proof, following the blueprint steps:
* `stepN:p11:rs-red`: `p = 9/8`, `q = 9` (`nrs_q`); from `K L r ≤ α/p`, `L = √n M` and
  `ε ≤ m r²/2¹⁴` we get `18432 K ε ≤ α r` (`nrs_key`), hence the smallness of `nf`
  (`nrs_nf_small`).
* `stepN:p11:rs-nf`: `nf` gives `Ψ, g, f_*` on `𝒟(r/2, s/6)`; `|g| ≤ |P_Λ T_K f| + 16 c₁ ε² ≤
  5ε/4` (`nrs_g_bound`, `nrs_g_small`); `|f_*| ≤ η := e^{-κ/6} ε ≤ ε/e` (`nrs_eta_le`); the slow
  loss `16 k c (s/6) ≤ r/2` (`nrs_slowLoss`); `RealFastConvex` on the half radius is extracted
  with `FastConvex.toRealFastConvex` (`nrs_rfc_mono`).
* `stepN:p11:rs-t12`: (T1) the displacement of `Ψ` at real points, `‖ΔI‖₂ ≤ √n q K ε/α ≤
  d := m r/(2¹¹ M)` (`nrs_t1_fast`) and `‖Δx‖ ≤ r/2¹⁰` (`nrs_t1_slow`); (T2) real preimages by
  `preimage` with `ρ = r/2`, `σ = s/3` (`nrs_t2_small`).
* `stepN:p11:rs-t3`: (T3) is proved from `energy_free` on the normal form (`nrs_t3`) with
  `δ = m r/32`, `ζ = η` and `T = s m r e^{κ/6}/(240 M ε)` (`nrs_time`).
* `stepN:p11:rs-concl`: `transfer_conditional` with `Nrm = euclid`, `a = (r/2)/4` gives
  `‖I(u) - I_c‖₂ ≤ r/8 + 2d ≤ r/2`.
-/

@[expose] public noncomputable section

open Set
open KAM.Weighted KAM.NormalForm

namespace KAM.Nekhoroshev

variable {n k : ℕ}

/-! ### Numerical reductions (`stepN:p11:rs-red`) -/

/-- `q = p/(p-1) = 9` for `p = 9/8`. -/
private theorem nrs_q : conjExp (9/8 : ℝ) = 9 := by
  show (9/8 : ℝ) / ((9/8 : ℝ) - 1) = 9
  norm_num

private theorem nrs_one_le_sqrt (hn : 1 ≤ n) : 1 ≤ Real.sqrt n := by
  rw [show (1:ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (by exact_mod_cast hn)

/-- The divisor size `K (√n M) r ≤ α/(9/8)` in product form. -/
private theorem nrs_alpha {K α M rB : ℝ} (hdiv : K*(Real.sqrt n*M)*rB ≤ α/(9/8)) :
    (9/8)*(Real.sqrt n*M*K*rB) ≤ α := by
  rw [le_div_iff₀ (by norm_num : (0:ℝ) < 9/8)] at hdiv
  linarith

private theorem nrs_eps {m rB ε : ℝ} (hsmall : ε ≤ m*rB^2/2^14) : 16384*ε ≤ m*rB^2 := by
  have h : (2:ℝ)^14 = 16384 := by norm_num
  rw [h, le_div_iff₀ (by norm_num : (0:ℝ) < 16384)] at hsmall
  linarith

/-- The key inequality of `rs-red`: `(9/8) 2¹⁴ K ε ≤ α r`. -/
private theorem nrs_key {K α ε m M rB : ℝ} (hK : 0 < K) (hrB : 0 < rB) (hm : 0 < m)
    (hmM : m ≤ M) (hsn : 1 ≤ Real.sqrt n) (hα9 : (9/8)*(Real.sqrt n*M*K*rB) ≤ α)
    (hε14 : 16384*ε ≤ m*rB^2) : 18432*(K*ε) ≤ α*rB := by
  have hM : 0 < M := hm.trans_le hmM
  have h1 : 16384*ε ≤ M*rB^2 := hε14.trans (mul_le_mul_of_nonneg_right hmM (by positivity))
  have h2 : (9/8)*K*(16384*ε) ≤ (9/8)*K*(M*rB^2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : (9/8)*K*(M*rB^2) ≤ (9/8)*K*(M*rB^2)*Real.sqrt n :=
    le_mul_of_one_le_right (by positivity) hsn
  have h4 : (9/8)*(Real.sqrt n*M*K*rB)*rB ≤ α*rB := mul_le_mul_of_nonneg_right hα9 hrB.le
  calc 18432*(K*ε) = (9/8)*K*(16384*ε) := by ring
    _ ≤ (9/8)*K*(M*rB^2) := h2
    _ ≤ (9/8)*K*(M*rB^2)*Real.sqrt n := h3
    _ = (9/8)*(Real.sqrt n*M*K*rB)*rB := by ring
    _ ≤ α*rB := h4

/-- `rs-red`: the smallness premise of `nf`, `ε ≤ α r/(2⁷ q K)`. -/
private theorem nrs_nf_small {K α ε rB : ℝ} (hK : 0 < K) (hε : 0 < ε)
    (hkey : 18432*(K*ε) ≤ α*rB) : ε ≤ α*rB/(2^7*conjExp (9/8)*K) := by
  have h7 : (2:ℝ)^7 = 128 := by norm_num
  rw [nrs_q, h7, le_div_iff₀ (by positivity)]
  have hKε : 0 < K*ε := mul_pos hK hε
  linarith

/-! ### Sizes of the normal form (`stepN:p11:rs-nf`) -/

/-- `16 c₁ ε² + ε ≤ 5ε/4`, with `c₁ = 2qK/(αr)`. -/
private theorem nrs_g_small {K α ε rB : ℝ} (hK : 0 < K) (hα : 0 < α) (hε : 0 < ε)
    (hrB : 0 < rB) (hkey : 18432*(K*ε) ≤ α*rB) :
    16*(2*conjExp (9/8)*K/(α*rB))*ε^2 + ε ≤ 5*ε/4 := by
  rw [nrs_q]
  have e : 16*(2*9*K/(α*rB))*ε^2 = ε*(288*(K*ε))/(α*rB) := by ring
  have h1 : ε*(288*(K*ε))/(α*rB) ≤ ε/4 := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : ε*(18432*(K*ε)) ≤ ε*(α*rB) := mul_le_mul_of_nonneg_left hkey hε.le
    have h3 : 0 ≤ ε*(K*ε) := by positivity
    linarith
  rw [e]
  linarith

/-- `η = e^{-κ/6} ε ≤ ε/e` from `κ ≥ 6`. -/
private theorem nrs_eta_le {K s ε : ℝ} (hε : 0 < ε) (hcut : 6 ≤ 2*Real.pi*K*s) :
    Real.exp (-(2*Real.pi*K*s)/6)*ε ≤ ε/Real.exp 1 := by
  have h1 : Real.exp (-(2*Real.pi*K*s)/6) ≤ Real.exp (-1) :=
    Real.exp_le_exp.2 (by linarith)
  rw [Real.exp_neg] at h1
  calc Real.exp (-(2*Real.pi*K*s)/6)*ε ≤ (Real.exp 1)⁻¹*ε :=
        mul_le_mul_of_nonneg_right h1 hε.le
    _ = ε/Real.exp 1 := by ring

/-- The slow loss on the normal-form domain: `16 k c (s/6) ≤ r/2` from (SL). -/
private theorem nrs_slowLoss (b : PartialBlock n k) {s : ℝ} (hr : 0 < b.rB) (hw : 0 < b.w)
    (hSL : b.SL s) : 16*(k:ℝ)*b.c*(s/6) ≤ b.rB/2 := by
  have hc : b.c = 2*Real.pi*b.rB^2/b.w^2 := by
    show 2*Real.pi/(b.w/b.rB)^2 = 2*Real.pi*b.rB^2/b.w^2
    rw [div_pow, div_div_eq_mul_div]
  have hSL' : 64*Real.pi*k*s*b.rB ≤ b.w^2 := hSL
  have hw2 : 0 < b.w^2 := by positivity
  rw [hc]
  have e : 16*(k:ℝ)*(2*Real.pi*b.rB^2/b.w^2)*(s/6) =
      b.rB*(64*Real.pi*k*s*b.rB)/(12*b.w^2) := by ring
  rw [e, div_le_iff₀ (by positivity)]
  have h1 : b.rB*(64*Real.pi*k*s*b.rB) ≤ b.rB*b.w^2 := mul_le_mul_of_nonneg_left hSL' hr.le
  have h2 : 0 < b.rB*b.w^2 := mul_pos hr hw2
  linarith

/-- The energy-confinement time: `T (240 M η) = s m r` for `T = s m r e^{κ/6}/(240 M ε)` and
`η = e^{-κ/6} ε`. -/
private theorem nrs_time {s m R M ε y : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    s*m*R/(240*M*ε)*Real.exp (y/6)*(240*M*(Real.exp (-y/6)*ε)) = s*m*R := by
  have hEE : Real.exp (y/6)*Real.exp (-y/6) = 1 := by
    rw [← Real.exp_add, show y/6 + -y/6 = 0 by ring, Real.exp_zero]
  have hne : (240*M*ε) ≠ 0 := by positivity
  have e : s*m*R/(240*M*ε)*Real.exp (y/6)*(240*M*(Real.exp (-y/6)*ε)) =
      s*m*R*((Real.exp (y/6)*Real.exp (-y/6))*((240*M*ε)/(240*M*ε))) := by ring
  rw [e, hEE, div_self hne, one_mul, mul_one]

/-! ### Sizes of the displacement (`stepN:p11:rs-t12`) -/

/-- (T1), fast actions: `√n q K ε/α ≤ d = m r/(2¹¹ M)`. -/
private theorem nrs_t1_fast {K α ε m M rB : ℝ} (hK : 0 < K) (hα : 0 < α)
    (hrB : 0 < rB) (hm : 0 < m) (hmM : m ≤ M) (hα9 : (9/8)*(Real.sqrt n*M*K*rB) ≤ α)
    (hε14 : 16384*ε ≤ m*rB^2) :
    Real.sqrt n * (conjExp (9/8)*K*ε/α) ≤ m*rB/(2048*M) := by
  have hM : 0 < M := hm.trans_le hmM
  rw [nrs_q, show Real.sqrt n * (9*K*ε/α) = Real.sqrt n*9*K*ε/α by ring,
    div_le_div_iff₀ hα (by positivity)]
  have e2 : (9/8)*Real.sqrt n*K*M*(16384*ε) ≤ (9/8)*Real.sqrt n*K*M*(m*rB^2) :=
    mul_le_mul_of_nonneg_left hε14 (by positivity)
  have e3 : (9/8)*(Real.sqrt n*M*K*rB)*(m*rB) ≤ α*(m*rB) :=
    mul_le_mul_of_nonneg_right hα9 (by positivity)
  calc Real.sqrt n*9*K*ε*(2048*M) = (9/8)*Real.sqrt n*K*M*(16384*ε) := by ring
    _ ≤ (9/8)*Real.sqrt n*K*M*(m*rB^2) := e2
    _ = (9/8)*(Real.sqrt n*M*K*rB)*(m*rB) := by ring
    _ ≤ α*(m*rB) := e3
    _ = m*rB*α := by ring

/-- (T1), slow pair: `q K ε/(8α) ≤ r/2¹⁰`. -/
private theorem nrs_t1_slow {K α ε rB : ℝ} (hK : 0 < K) (hα : 0 < α) (hε : 0 < ε)
    (hkey : 18432*(K*ε) ≤ α*rB) : conjExp (9/8)*K*ε/(8*α) ≤ rB/1024 := by
  rw [nrs_q, div_le_div_iff₀ (by positivity) (by norm_num)]
  have hKε : 0 < K*ε := mul_pos hK hε
  linarith

/-- (T2): the smallness premise of `preimage` with `ρ = r/2`, `σ = s/3`. -/
private theorem nrs_t2_small {K α ε rB s : ℝ} (hK : 0 < K) (hα : 0 < α) (hε : 0 < ε)
    (hrB : 0 < rB) (hs : 0 < s) (hcut : 6 ≤ 2*Real.pi*K*s) (hkey : 18432*(K*ε) ≤ α*rB) :
    max (10*conjExp (9/8)*ε/(2*Real.pi*α*rB)/(s/3))
      (max (conjExp (9/8)*K*ε/α/(rB/2)) (conjExp (9/8)*K*ε/(8*α)/(rB/2))) ≤ 1/4 := by
  rw [nrs_q]
  have hKε : 0 < K*ε := mul_pos hK hε
  refine max_le ?_ (max_le ?_ ?_)
  · rw [div_le_iff₀ (by positivity), div_le_iff₀ (by positivity)]
    have c1 : 18432*(K*ε)*(2*Real.pi*s) ≤ α*rB*(2*Real.pi*s) :=
      mul_le_mul_of_nonneg_right hkey (by positivity)
    have c2 : 6*(18432*ε) ≤ (2*Real.pi*K*s)*(18432*ε) :=
      mul_le_mul_of_nonneg_right hcut (by positivity)
    linarith
  · rw [div_le_iff₀ (by positivity), div_le_iff₀ hα]
    linarith
  · rw [div_le_iff₀ (by positivity), div_le_iff₀ (by positivity)]
    linarith

/-- `d = m r/(2¹¹ M) ≤ r/2¹¹`. -/
private theorem nrs_d_le {m M rB : ℝ} (hm : 0 < m) (hmM : m ≤ M) (hrB : 0 < rB) :
    m*rB/(2048*M) ≤ rB/2048 := by
  have hM : 0 < M := hm.trans_le hmM
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have h1 : rB*m ≤ rB*M := mul_le_mul_of_nonneg_left hmM hrB.le
  linarith

/-- `d < ρ' = δ/(4M)` with `δ = m r/32`. -/
private theorem nrs_d_lt {m M rB : ℝ} (hm : 0 < m) (hM : 0 < M) (hrB : 0 < rB) :
    m*rB/(2048*M) < m*rB/32/(4*M) := by
  have hx : 0 < m*rB/32/(4*M) := by positivity
  have e : m*rB/(2048*M) = (m*rB/32/(4*M))/16 := by ring
  rw [e]
  linarith

/-! ### Real points, monotonicity and the weighted norm of `g` -/

private theorem nrs_extCx_mem_Dom (b : PartialBlock n k) {R s : ℝ} (hs : 0 < s) {z : ER n k}
    (hz : z ∈ b.realDom R) : extCx z ∈ Dom n b.base R s := by
  have h1 : extCx z ∈ Dom n b.base R 1 := hz
  exact ⟨KAM.ofReal_mem_complexStrip hs z.1, h1.2⟩

private theorem nrs_extRe_extCx (y : ER n k) : extRe (extCx y) = y := by
  ext i <;> simp [extRe, extCx]

private theorem nrs_fastAction_extCx (y : ER n k) :
    fastAction (extCx y) = KAM.realInclusion n (fastAction y) := by
  ext i; simp [fastAction, extCx]

private theorem nrs_norm_fast_sub (x y : ER n k) :
    ‖fastAction (extCx y) - fastAction (extCx x)‖ = ‖fastAction y - fastAction x‖ := by
  rw [nrs_fastAction_extCx, nrs_fastAction_extCx, ← map_sub, KAM.norm_realInclusion]

private theorem nrs_norm_slow_sub (x y : ER n k) :
    ‖slowPair (extCx y) - slowPair (extCx x)‖ = ‖slowPair y - slowPair x‖ := by
  have h : slowPair (extCx y) - slowPair (extCx x) =
      (KAM.realInclusion k ((slowPair y - slowPair x).1),
        KAM.realInclusion k ((slowPair y - slowPair x).2)) := by
    ext i <;> simp [slowPair, extCx]
  rw [h, Prod.norm_def, Prod.norm_def, KAM.norm_realInclusion, KAM.norm_realInclusion]

/-- `RealFastConvex` restricts to a smaller radius. -/
private theorem nrs_rfc_mono {Ic : Fin n → ℝ} {R R' m M : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : RealFastConvex Ic R m M h) (hR : R' ≤ R) : RealFastConvex Ic R' m M h :=
  ⟨hh.m_pos, hh.m_le, hh.hol.mono (polyNbhd_mono hR),
    fun I hI => hh.real I (polyNbhd_mono hR hI),
    fun I hI v => hh.convex I (lt_of_lt_of_le hI hR) v,
    fun I hI v => hh.hessian_real I (lt_of_lt_of_le hI hR) v⟩

/-- `|g| ≤ |g - P| + |P|` (subadditivity of the weighted norm). -/
private theorem nrs_wbound_of_sub {N : ℕ} {D : Set (Fin N → ℂ)} {r s A B : ℝ}
    {g P : (Fin n → ℂ) × (Fin N → ℂ) → ℂ} (hs : 0 < s) (hg : InClass D r s g)
    (hP : InClass D r s P) (hgP : WBound D r s (g - P) A) (hPb : WBound D r s P B) :
    WBound D r s g (A + B) := by
  have hd : InClass D r s (g - P) := by
    refine ⟨?_, fun j z hz => ?_⟩
    · exact hg.differentiableOn.sub hP.differentiableOn
    · simp only [Pi.sub_apply]
      rw [hg.periodic j z hz, hP.periodic j z hz]
  have h := wbound_add_ext hs hd hP hgP hPb
  have e : (fun z => (g - P) z + P z) = g := by
    funext z
    simp only [Pi.sub_apply, sub_add_cancel]
  rwa [e] at h

/-- `rs-nf`: `|g|_{r/2,s/6} ≤ B + ε` from `|g - P_Λ T_K f| ≤ B` and `|f|_{r,s} ≤ ε`. -/
private theorem nrs_g_bound (b : PartialBlock n k) {s K ε B : ℝ} {Λ : Set (Fin n → ℤ)}
    {f g : EC n k → ℂ} (hs : 0 < s) (hr : 0 < b.rB)
    (hf : InClass b.base b.rB s f) (hfb : WBound b.base b.rB s f ε)
    (hg : InClass b.base (b.rB/2) (s/6) g)
    (hga : WBound b.base (b.rB/2) (s/6) (g-projMode Λ (truncate K f)) B) :
    WBound b.base (b.rB/2) (s/6) g (B + ε) := by
  obtain ⟨t1, -, t3, -⟩ := projections hs hf hfb {j : Fin n → ℤ | KAM.Fourier.modeSize j ≤ K}
  obtain ⟨p1, -, p3, -⟩ := projections hs t1 t3 Λ
  have hP1 : InClass b.base b.rB s (projMode Λ (truncate K f)) := p1
  have hP3 : WBound b.base b.rB s (projMode Λ (truncate K f)) ε := p3
  have hrr : b.rB/2 ≤ b.rB := by linarith
  have hss : s/6 ≤ s := by linarith
  have hPc : InClass b.base (b.rB/2) (s/6) (projMode Λ (truncate K f)) :=
    ⟨hP1.differentiableOn.mono (Dom_mono hrr hss),
      fun j z hz => hP1.periodic j z (Dom_mono hrr hss hz)⟩
  have hPb : WBound b.base (b.rB/2) (s/6) (projMode Λ (truncate K f)) ε :=
    hP3.mono hrr hss le_rfl
  exact nrs_wbound_of_sub (by positivity) hg hPc hga hPb

/-! ### (T3) from the energy confinement (`stepN:p11:rs-t3`) -/

/-- `rs-t3`: every normal-form orbit starting `d`-close to `Ic` (with `d < ρ' = δ/(4M)`) and
keeping its slow pair `dx`-close to `λ⁻¹ S` (`dx < r̃/2`) moves its fast action by at most
`r̃/4 = (r/2)/4` for `|t| ≤ T`, `240 M T η ≤ s m r`; this is `energy_free` with `r̃ = r/2`,
`s̃ = s/6`, `δ = m r/32` and `ζ = η`. -/
private theorem nrs_t3 (b : PartialBlock n k) {s m M ε η Tv d dx : ℝ}
    {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {g fs : EC n k → ℂ}
    (hr : 0 < b.rB) (hs : 0 < s) (hh : RealFastConvex b.Ic (b.rB/2) m M h)
    (hg : ext_class b (b.rB/2) (s/6) g) (hf : ext_class b (b.rB/2) (s/6) fs)
    (hgb : WBound b.base (b.rB/2) (s/6) g (5*ε/4))
    (hfb : WBound b.base (b.rB/2) (s/6) fs η)
    (hsupp : ∀ J ∈ polyNbhd b.base (b.rB/2), ∀ j : Fin n → ℤ, j ∉ Λ → coeff g J j = 0)
    (hε : 0 < ε) (hη : 0 < η) (hηε : η ≤ ε/Real.exp 1)
    (hsmall : ε ≤ m*b.rB^2/2^14) (hSL : 16*(k:ℝ)*b.c*(s/6) ≤ b.rB/2)
    (hnr : NearResonance Λ h b.Ic (m*b.rB/32))
    (hd : d < m*b.rB/32/(4*M)) (hdx : dx < b.rB/2/2)
    (hT0 : 0 ≤ Tv) (hTη : Tv*(240*M*η) ≤ s*m*b.rB) :
    ∀ J : Set ℝ, J.OrdConnected → (0:ℝ) ∈ J → ∀ y : ℝ → ER n k,
      ExtOrbit b (b.rB/2) (liftFast h+g+fs) J y → euclid (fastAction (y 0)-b.Ic) ≤ d →
      (∀ u ∈ J, slowTube b dx (slowPair (y u))) →
      ∀ u ∈ J, ENNReal.ofReal |u| ≤ ENNReal.ofReal Tv →
        euclid (fastAction (y u)-fastAction (y 0)) ≤ b.rB/2/4 := by
  intro J hJ h0 y hy hy0 htube u hu huT
  have hm : 0 < m := hh.m_pos
  have hM : 0 < M := hh.m_pos.trans_le hh.m_le
  have hu' : |u| ≤ Tv := by
    by_contra hlt
    have h1 : Tv < |u| := not_le.1 hlt
    have h2 : ENNReal.ofReal Tv < ENNReal.ofReal |u| :=
      (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hT0 h1)).2 h1
    exact absurd huT (not_le.2 h2)
  have hsm : ε ≤ m*(b.rB/2)^2/2^12 := by
    calc ε ≤ m*b.rB^2/2^14 := hsmall
      _ = m*(b.rB/2)^2/2^12 := by ring
  have htime : |u| ≤ s/6*m*(b.rB/2)/(20*M*η) := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : |u| * (240*M*η) ≤ Tv*(240*M*η) := mul_le_mul_of_nonneg_right hu' (by positivity)
    linarith
  have hinit : euclid (fastAction (y 0)-b.Ic) < m*b.rB/32/(4*M) := lt_of_le_of_lt hy0 hd
  have hslow : ∀ v ∈ J, ∃ w ∈ b.S, ‖slowPair (y v)-b.lam⁻¹ • w‖ < b.rB/2/2 := by
    intro v hv
    obtain ⟨w, hw, hle⟩ := htube v hv
    exact ⟨w, hw, lt_of_le_of_lt hle hdx⟩
  exact energy_free b (r := b.rB/2) (s := s/6) (m := m) (M := M) (ε := ε) (η := η) (ζ := η)
    (δ := m*b.rB/32) (by positivity) (by positivity) hh hg hf hgb hfb hsupp hε hη.le hη le_rfl
    hηε hsm hSL (by positivity) (le_of_eq (by ring)) hnr hJ h0 hy hinit hslow u hu htime

/-! ### The resonant block theorem -/

/-- `bpN:p11:resonant`: resonant stability in the extended phase space, convex case. -/
theorem resonant (b : PartialBlock n k) {s K α m M ε : ℝ}
    {Λ : AddSubgroup (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ}
    (hh : ExtNFHyp b s K α (Real.sqrt n*M) (9/8) ε (Λ:Set (Fin n → ℤ)) h f)
    (hconv : FastConvex b.Ic b.rB m M h)
    (hne : NearResonance (Λ:Set (Fin n → ℤ)) h b.Ic (m*b.rB/32))
    (hsmall : ε ≤ m*b.rB^2/2^14)
    (F : ER n k → ER n k)
    (hF : EqOn F (realWfield b.c (realHamiltonianExt b b.rB (liftFast h+f))) (b.realDom b.rB))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u)
    (hinit : fastAction (y 0) = b.Ic) (hx : b.lam • slowPair (y 0) ∈ b.S)
    {t1 : ℝ} (ht1 : t1 ∈ J) (ht : |t1| ≤ s*m*b.rB/(240*M*ε)*Real.exp ((2*Real.pi*K*s)/6))
    (hstop : ∀ u ∈ uIcc 0 t1, b.lam • slowPair (y u) ∈ b.S) :
    ∀ u ∈ uIcc 0 t1, euclid (fastAction (y u)-b.Ic) ≤ b.rB/2 := by
  -- `rs-red`
  have hr : 0 < b.rB := hh.radius_pos
  have hw : 0 < b.w := hh.slow_width_pos
  have hs : 0 < s := hh.s_pos
  have hK : 0 < K := hh.K_pos
  have hα : 0 < α := hh.alpha_pos
  have hε : 0 < ε := hh.eps_pos
  have hm : 0 < m := hconv.m_pos
  have hmM : m ≤ M := hconv.m_le
  have hM : 0 < M := hm.trans_le hmM
  have hs6 : 0 < s/6 := by positivity
  have hsn : 1 ≤ Real.sqrt n := nrs_one_le_sqrt hh.n_pos
  have hsn0 : 0 < Real.sqrt n := by linarith
  have hα9 : (9/8)*(Real.sqrt n*M*K*b.rB) ≤ α := nrs_alpha hh.divisor_size
  have hε14 : 16384*ε ≤ m*b.rB^2 := nrs_eps hsmall
  have hkey : 18432*(K*ε) ≤ α*b.rB := nrs_key hK hr hm hmM hsn hα9 hε14
  -- `rs-nf`
  obtain ⟨Ψ, g, fs, hΨd, hΨm, -, hΨc, -, hΨr, hgc, hfsc, hsupp, hΨid, hga, hfsb, hΨb⟩ :=
    nf b hh (nrs_nf_small hK hε hkey)
  have hRF : RealFastConvex b.Ic b.rB m M h := hconv.toRealFastConvex
  have hRF2 : RealFastConvex b.Ic (b.rB/2) m M h := nrs_rfc_mono hRF (by linarith)
  have hgb : WBound b.base (b.rB/2) (s/6) g (5*ε/4) :=
    (nrs_g_bound b hs hr hh.pert.1 hh.bound hgc.1 hga).mono le_rfl le_rfl
      (nrs_g_small hK hα hε hr hkey)
  have hη : 0 < Real.exp (-(2*Real.pi*K*s)/6)*ε := by positivity
  have hηε : Real.exp (-(2*Real.pi*K*s)/6)*ε ≤ ε/Real.exp 1 := nrs_eta_le hε hh.cutoff
  have hSL : 16*(k:ℝ)*b.c*(s/6) ≤ b.rB/2 := nrs_slowLoss b hr hw hh.slow
  have hsupp' : ∀ J' ∈ polyNbhd b.base (b.rB/2), ∀ j : Fin n → ℤ,
      j ∉ (Λ:Set (Fin n → ℤ)) → coeff g J' j = 0 :=
    fun J' hJ' j hj => hsupp J' hJ' j (fun hj' => hj hj'.1)
  -- the conjugacy data
  have hcj : ExtConjHyp b b.rB s (b.rB/2) (s/6) (liftFast h + f) (liftFast h + g + fs) Ψ :=
    ⟨hr, by positivity, hs, hs6, by linarith, by linarith,
      ext_class_add b (ext_class_liftFast b hRF) hh.pert,
      ext_class_add b (ext_class_add b (ext_class_liftFast b hRF2) hgc) hfsc,
      hΨd, hΨm, fun z hz => hΨr z hz, hΨc, fun z hz => by
        show liftFast h z + g z + fs z = liftFast h (Ψ z) + f (Ψ z)
        exact (hΨid z hz).symm⟩
  -- `rs-t12`: (T1)
  have hT1 : Real.sqrt n * (conjExp (9/8)*K*ε/α) ≤ m*b.rB/(2048*M) :=
    nrs_t1_fast hK hα hr hm hmM hα9 hε14
  have hdisp : ∀ z ∈ b.realDom (b.rB/2),
      euclid (fastAction (reExtMap Ψ z) - fastAction z) ≤ m*b.rB/(2048*M) ∧
        ‖slowPair (reExtMap Ψ z) - slowPair z‖ ≤ b.rB/1024 := by
    intro z hz
    have hzD : extCx z ∈ Dom n b.base (b.rB/2) (s/6) := nrs_extCx_mem_Dom b hs6 hz
    obtain ⟨h1, -, h3⟩ := hΨb (extCx z) hzD
    have hre : Ψ (extCx z) = extCx (reExtMap Ψ z) := (hΨr z hzD).symm
    rw [hre, nrs_norm_fast_sub] at h1
    rw [hre, nrs_norm_slow_sub] at h3
    have h4 := (norm_le_euclid (fastAction (reExtMap Ψ z) - fastAction z)).2.1
    exact ⟨h4.trans ((mul_le_mul_of_nonneg_left h1 hsn0.le).trans hT1),
      h3.trans (nrs_t1_slow hK hα hε hkey)⟩
  -- `rs-t12`: (T2)
  have hpre : ∀ y' : ER n k, fastAction y' = b.Ic → b.lam • slowPair y' ∈ b.S →
      ∃ x ∈ b.realDom (b.rB/2), reExtMap Ψ x = y' ∧
        euclid (fastAction x - b.Ic) ≤ m*b.rB/(2048*M) := by
    intro y' hI hS
    obtain ⟨x, hxD, hΨx, -, hxI, -⟩ := preimage b hr hw (R := b.rB/2) (s := s/6)
      (dθ := 10*conjExp (9/8)*ε/(2*Real.pi*α*b.rB)) (dI := conjExp (9/8)*K*ε/α)
      (dx := conjExp (9/8)*K*ε/(8*α)) (ρ := b.rB/2) (σ := s/3) hΨd (fun z hz => hΨr z hz)
      (fun z hz => ⟨(hΨb z hz).2.1, (hΨb z hz).1, (hΨb z hz).2.2⟩) (by positivity) le_rfl
      (by positivity) (by linarith) (nrs_t2_small hK hα hε hr hs hh.cutoff hkey) y' hI hS
    refine ⟨x, hxD, ?_, ?_⟩
    · show extRe (Ψ (extCx x)) = y'
      rw [hΨx, nrs_extRe_extCx]
    · have h4 := (norm_le_euclid (fastAction x - b.Ic)).2.1
      exact h4.trans ((mul_le_mul_of_nonneg_left hxI hsn0.le).trans hT1)
  -- `rs-t3`
  have hT3 := nrs_t3 b (Λ := (Λ:Set (Fin n → ℤ))) (d := m*b.rB/(2048*M)) (dx := b.rB/1024)
    (Tv := s*m*b.rB/(240*M*ε)*Real.exp ((2*Real.pi*K*s)/6)) hr hs hRF2 hgc hfsc hgb hfsb
    hsupp' hε hη hηε hsmall hSL hne (nrs_d_lt hm hM hr) (by linarith) (by positivity)
    (le_of_eq (nrs_time (s := s) (m := m) (R := b.rB) (y := 2*Real.pi*K*s) hM hε))
  -- `rs-concl`
  have key := transfer_conditional b hr hw (R := b.rB) (s := s) (r := b.rB/2) (t := s/6)
    (d := m*b.rB/(2048*M)) (dx := b.rB/1024) (a := b.rB/2/4)
    (T := ENNReal.ofReal (s*m*b.rB/(240*M*ε)*Real.exp ((2*Real.pi*K*s)/6)))
    hcj (fun v => euclid v) KAM.Stability.isActionNorm_euclid (by positivity) (by positivity)
    (by linarith) (by positivity) (by linarith [nrs_d_le hm hmM hr])
    (ENNReal.ofReal_pos.2 (by positivity)) hdisp hpre hT3 F hF hJ h0 hy hinit hx ht1
    (ENNReal.ofReal_le_ofReal ht) hstop
  intro u hu
  have h1 : euclid (fastAction (y u)-b.Ic) ≤ b.rB/2/4 + 2*(m*b.rB/(2048*M)) := (key u hu).2
  have h2 : m*b.rB/(2048*M) ≤ b.rB/2048 := nrs_d_le hm hmM hr
  linarith

end KAM.Nekhoroshev

end
