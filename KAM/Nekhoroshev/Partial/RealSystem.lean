/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Nekhoroshev.Partial.Coordinates
public import KAM.Nekhoroshev.Stability.Gradient
public import KAM.Weighted.Cauchy
public import KAM.Weighted.SupWeighted
public import KAM.Strip.Bridges
public import KAM.Strip.Periodic
public import KAM.ODE.Maximal

/-!
# Real extended systems (`bpN:p11:real-system`)

For `H ∈ O(R,s)^{e,ℝ}`: the real restriction `realHamiltonianExt b R H` is `C^∞` on
`W^e_R = b.realDom R`, periodic in the angles, its weighted field is the restriction of the complex
weighted field (also periodic and `C¹`), and the energy is conserved along orbits.  Also the
fixed-base derivative bound `real_system_bounds` and the resonant-gradient statement
`real_system_resonant`.  The proofs follow Part 7 (`KAM.Stability.real_system`) on the unequal
product `EC n k`: the regrouping is proved by component identities.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.NormalForm

variable {n k : ℕ}

private theorem extCx_eq (z : ER n k) :
    extCx z = (KAM.realInclusion n z.1, KAM.realInclusion (n+(k+k)) z.2) := by
  ext i <;> simp [extCx]

/-- The real points of `EC n k` as a continuous `ℝ`-linear map. -/
private def extCxCLM (n k : ℕ) : ER n k →L[ℝ] EC n k :=
  (KAM.realInclusion n).prodMap (KAM.realInclusion (n+(k+k)))

private theorem extCxCLM_apply (z : ER n k) : extCxCLM n k z = extCx z := (extCx_eq z).symm

private theorem extCx_eq_clm : (extCx : ER n k → EC n k) = extCxCLM n k :=
  funext fun z => (extCxCLM_apply z).symm

private theorem extCx_mem_Dom_iff (b : PartialBlock n k) {R s : ℝ} (hs : 0 < s) (z : ER n k) :
    extCx z ∈ Dom n b.base R s ↔ (extCx z).2 ∈ polyNbhd b.base R := by
  simp only [Dom, mem_prod]
  exact ⟨fun h => h.2, fun h => ⟨KAM.ofReal_mem_complexStrip hs z.1, h⟩⟩

private theorem mem_realDom_iff (b : PartialBlock n k) (R : ℝ) (z : ER n k) :
    z ∈ b.realDom R ↔ (extCx z).2 ∈ polyNbhd b.base R :=
  extCx_mem_Dom_iff b one_pos z

private theorem isOpen_realDom (b : PartialBlock n k) (R : ℝ) : IsOpen (b.realDom R) := by
  have hc : Continuous (extCx : ER n k → EC n k) := by
    rw [extCx_eq_clm]; exact (extCxCLM n k).continuous
  exact (isOpen_Dom (n := n) b.base R 1).preimage hc

private theorem realDom_mono (b : PartialBlock n k) {R R' : ℝ} (h : R' ≤ R) :
    b.realDom R' ⊆ b.realDom R := fun z hz =>
  (mem_realDom_iff b R z).2 (polyNbhd_mono h ((mem_realDom_iff b R' z).1 hz))

private theorem realDom_shift (b : PartialBlock n k) (R : ℝ) (ℓ : Fin n → ℤ) (z : ER n k) :
    (z.1 + (fun i => (ℓ i : ℝ)), z.2) ∈ b.realDom R ↔ z ∈ b.realDom R := by
  rw [mem_realDom_iff, mem_realDom_iff]
  rfl

private theorem hreal_of_ext {b : PartialBlock n k} {R s : ℝ} {H : EC n k → ℂ}
    (hH : ext_class b R s H) (y : ER n k) (hy : extCx y ∈ Dom n b.base R s) :
    (H (extCx y)).im = 0 := by
  have := hH.2 y (by rw [← extCx_eq]; exact hy)
  rwa [← extCx_eq] at this

private theorem realHamiltonianExt_eventually (b : PartialBlock n k) (R : ℝ) (H : EC n k → ℂ)
    {z : ER n k} (hz : z ∈ b.realDom R) :
    ∀ᶠ y in nhds z, realHamiltonianExt b R H y = (H (extCx y)).re := by
  filter_upwards [(isOpen_realDom b R).mem_nhds hz] with y hy
  simp [realHamiltonianExt, indicator_of_mem hy]

/-- Real derivative transport on `EC n k` (the unequal-carrier form of
`KAM.hamiltonian_real_fderiv`). -/
private theorem fderiv_ext_real {V : Set (EC n k)} {H : EC n k → ℂ} {Hr : ER n k → ℝ}
    {z : ER n k} (hV : IsOpen V) (hh : DifferentiableOn ℂ H V)
    (hreal : ∀ y : ER n k, extCx y ∈ V → (H (extCx y)).im = 0)
    (hz : extCx z ∈ V) (hH : ∀ᶠ y in nhds z, Hr y = (H (extCx y)).re) :
    DifferentiableAt ℝ Hr z ∧ ∀ e : ER n k,
      ((fderiv ℝ Hr z e : ℝ) : ℂ) = fderiv ℂ H (extCx z) (extCx e) := by
  set L := extCxCLM n k with hL
  have hz' : L z ∈ V := by rwa [hL, extCxCLM_apply]
  have hhd : DifferentiableAt ℂ H (L z) := hh.differentiableAt (hV.mem_nhds hz')
  have h2 : HasFDerivAt (fun y => H (L y))
      (((fderiv ℂ H (L z)).restrictScalars ℝ).comp L) z :=
    (hhd.hasFDerivAt.restrictScalars ℝ).comp z L.hasFDerivAt
  have h3 : HasFDerivAt (fun y => (H (L y)).re)
      (Complex.reCLM.comp (((fderiv ℂ H (L z)).restrictScalars ℝ).comp L)) z :=
    Complex.reCLM.hasFDerivAt.comp z h2
  have hH' : ∀ᶠ y in nhds z, Hr y = (H (L y)).re := by
    simpa only [hL, extCxCLM_apply] using hH
  have h4 : HasFDerivAt Hr (Complex.reCLM.comp
      (((fderiv ℂ H (L z)).restrictScalars ℝ).comp L)) z := h3.congr_of_eventuallyEq hH'
  refine ⟨h4.differentiableAt, fun e => ?_⟩
  have hmem : ∀ᶠ y in nhds z, L y ∈ V := L.continuous.continuousAt.eventually_mem (hV.mem_nhds hz')
  have hev : (fun y => H (L y)) =ᶠ[nhds z] fun y => ((Hr y : ℝ) : ℂ) := by
    filter_upwards [hH', hmem] with y hy hyV
    rw [hy]
    refine Complex.ext (by simp) ?_
    simpa [hL, extCxCLM_apply] using hreal y (by rwa [← extCxCLM_apply])
  have h5 : HasFDerivAt (fun y => ((Hr y : ℝ) : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ Hr z)) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z h4.differentiableAt.hasFDerivAt
  have h6 := (h2.congr_of_eventuallyEq hev.symm).unique h5
  have := (congrArg (fun L => L e) h6).symm
  simpa [hL, extCxCLM_apply] using this

private theorem extCx_zero_single (j : Fin (n+(k+k))) :
    extCx ((0 : Fin n → ℝ), (Pi.single j 1 : Fin (n+(k+k)) → ℝ)) =
      ((0 : Fin n → ℂ), (Pi.single j 1 : Fin (n+(k+k)) → ℂ)) := by
  ext i <;> simp [extCx, Pi.single_apply, apply_ite Complex.ofReal]

private theorem extCx_single_zero (j : Fin n) :
    extCx ((Pi.single j 1 : Fin n → ℝ), (0 : Fin (n+(k+k)) → ℝ)) =
      ((Pi.single j 1 : Fin n → ℂ), (0 : Fin (n+(k+k)) → ℂ)) := by
  ext i <;> simp [extCx, Pi.single_apply, apply_ite Complex.ofReal]

private theorem clm_decomp (D : ER n k →L[ℝ] ℝ) (x : Fin n → ℝ) (y : Fin (n+(k+k)) → ℝ) :
    D (x, y) = ∑ i, x i * D (Pi.single i 1, 0) + ∑ j, y j * D (0, Pi.single j 1) := by
  have h1 : ((x, y) : ER n k) = ∑ i, x i • ((Pi.single i 1 : Fin n → ℝ), (0 : Fin (n+(k+k)) → ℝ))
      + ∑ j, y j • ((0 : Fin n → ℝ), (Pi.single j 1 : Fin (n+(k+k)) → ℝ)) := by
    ext l
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  rw [h1, map_add, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- The symplectic cancellation `D (X_c D) = 0`. -/
private theorem clm_realWfield_zero (c : ℝ) (D : ER n k →L[ℝ] ℝ) :
    D (((fun i => D (0, Pi.single (Fin.castAdd (k+k) i) 1),
      Fin.append (fun i => -D (Pi.single i 1, 0))
        (Fin.append
          (fun i => c * D (0, Pi.single (Fin.natAdd n (Fin.natAdd k i)) 1))
          (fun i => -c * D (0, Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1)))) : ER n k)) = 0 := by
  rw [clm_decomp]
  simp only [Fin.sum_univ_add, Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib]
  have e1 : ∑ i : Fin n, D (0, Pi.single (Fin.castAdd (k+k) i) 1) * D (Pi.single i 1, 0) =
      ∑ i : Fin n, D (Pi.single i 1, 0) * D (0, Pi.single (Fin.castAdd (k+k) i) 1) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have e2 : ∑ i : Fin k, c * D (0, Pi.single (Fin.natAdd n (Fin.natAdd k i)) 1) *
        D (0, Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1) =
      ∑ i : Fin k, c * D (0, Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1) *
        D (0, Pi.single (Fin.natAdd n (Fin.natAdd k i)) 1) :=
    Finset.sum_congr rfl fun i _ => by ring
  linarith

private theorem realH_contDiff (b : PartialBlock n k) {R s : ℝ} {H : EC n k → ℂ} (hs : 0 < s)
    (hH : ext_class b R s H) : ContDiffOn ℝ ∞ (realHamiltonianExt b R H) (b.realDom R) := by
  have hreg := KAM.holomorphic_regularity_of_finiteDimensional
    (isOpen_Dom (n := n) b.base R s) hH.1.differentiableOn
  have h1 : ContDiffOn ℝ ∞ H (Dom n b.base R s) := hreg.2.2.1.restrict_scalars ℝ
  have hmaps : ∀ y ∈ b.realDom R, extCxCLM n k y ∈ Dom n b.base R s := fun y hy => by
    rw [extCxCLM_apply]; exact (extCx_mem_Dom_iff b hs y).2 ((mem_realDom_iff b R y).1 hy)
  have h2 := h1.comp (extCxCLM n k).contDiff.contDiffOn hmaps
  have h3 := Complex.reCLM.contDiff.comp_contDiffOn h2
  exact h3.congr fun y hy => by simp [realHamiltonianExt, indicator_of_mem hy, extCxCLM_apply]

private theorem realWfield_contDiff (b : PartialBlock n k) {R s : ℝ} {H : EC n k → ℂ}
    (hs : 0 < s) (hH : ext_class b R s H) :
    ContDiffOn ℝ 1 (realWfield b.c (realHamiltonianExt b R H)) (b.realDom R) := by
  have hsm := realH_contDiff b hs hH
  have h2 : ContDiffOn ℝ 2 (realHamiltonianExt b R H) (b.realDom R) :=
    hsm.of_le (by exact WithTop.coe_le_coe.2 le_top)
  have hf : ContDiffOn ℝ 1 (fderiv ℝ (realHamiltonianExt b R H)) (b.realDom R) :=
    h2.fderiv_of_isOpen (isOpen_realDom b R) (by norm_num)
  have hc : ∀ v : ER n k,
      ContDiffOn ℝ 1 (fun z => fderiv ℝ (realHamiltonianExt b R H) z v) (b.realDom R) :=
    fun v => hf.clm_apply contDiffOn_const
  have h1 : ContDiffOn ℝ 1 (fun z => (realWfield b.c (realHamiltonianExt b R H) z).1)
      (b.realDom R) :=
    contDiffOn_pi.2 fun i => by simpa only [realWfield] using hc _
  have h2' : ContDiffOn ℝ 1 (fun z => (realWfield b.c (realHamiltonianExt b R H) z).2)
      (b.realDom R) := by
    refine contDiffOn_pi.2 fun j => ?_
    refine ext_cases (P := fun j => ContDiffOn ℝ 1
      (fun z => (realWfield b.c (realHamiltonianExt b R H) z).2 j) (b.realDom R))
      (fun i => ?_) (fun i => ?_) (fun i => ?_) j
    · simpa only [realWfield, Fin.append_left] using (hc _).neg
    · simpa only [realWfield, Fin.append_right, Fin.append_left] using contDiffOn_const.mul (hc _)
    · simpa only [realWfield, Fin.append_right] using contDiffOn_const.mul (hc _)
  exact ContDiffOn.prodMk h1 h2'

private theorem realWfield_cx (b : PartialBlock n k) {R s : ℝ} {H : EC n k → ℂ}
    (hs : 0 < s) (hH : ext_class b R s H) {z : ER n k} (hz : z ∈ b.realDom R) :
    extCx (realWfield b.c (realHamiltonianExt b R H) z) = wfield b.c H (extCx z) := by
  have hzD : extCx z ∈ Dom n b.base R s :=
    (extCx_mem_Dom_iff b hs z).2 ((mem_realDom_iff b R z).1 hz)
  have hd := (fderiv_ext_real (isOpen_Dom (n := n) b.base R s) hH.1.differentiableOn
    (hreal_of_ext hH) hzD (realHamiltonianExt_eventually b R H hz)).2
  refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
  · show ((fderiv ℝ (realHamiltonianExt b R H) z (0, Pi.single (Fin.castAdd (k+k) i) 1) : ℝ) : ℂ)
      = fderiv ℂ H (extCx z) (0, Pi.single (Fin.castAdd (k+k) i) 1)
    rw [hd, extCx_zero_single]
  · refine ext_cases (P := fun j => ((((realWfield b.c (realHamiltonianExt b R H) z).2 j : ℝ)) : ℂ)
      = (wfield b.c H (extCx z)).2 j) (fun i => ?_) (fun i => ?_) (fun i => ?_) j
    · simp only [realWfield, wfield, Fin.append_left, Complex.ofReal_neg, hd,
        extCx_single_zero]
    · simp only [realWfield, wfield, Fin.append_right, Fin.append_left, Complex.ofReal_mul, hd,
        extCx_zero_single]
    · simp only [realWfield, wfield, Fin.append_right, Complex.ofReal_mul, Complex.ofReal_neg, hd,
        extCx_zero_single]

private theorem realH_periodic (b : PartialBlock n k) {R s : ℝ} {H : EC n k → ℂ} (hs : 0 < s)
    (hH : ext_class b R s H) (ℓ : Fin n → ℤ) {z : ER n k} (hz : z ∈ b.realDom R) :
    realHamiltonianExt b R H (z.1 + (fun i => (ℓ i : ℝ)), z.2) = realHamiltonianExt b R H z := by
  have hz' : (z.1 + (fun i => (ℓ i : ℝ)), z.2) ∈ b.realDom R := (realDom_shift b R ℓ z).2 hz
  simp only [realHamiltonianExt, indicator_of_mem hz, indicator_of_mem hz']
  have hI : (extCx z).2 ∈ polyNbhd b.base R := (mem_realDom_iff b R z).1 hz
  have hθ : (extCx z).1 ∈ KAM.complexStrip n s := KAM.ofReal_mem_complexStrip hs z.1
  have hp : ∀ (i : Fin n) (θ : Fin n → ℂ), θ ∈ KAM.complexStrip n s →
      (fun θ => H (θ, (extCx z).2)) (θ + Pi.single i 1) = (fun θ => H (θ, (extCx z).2)) θ :=
    fun i θ hθ' => hH.1.periodic i (θ, (extCx z).2) ⟨hθ', hI⟩
  have h := KAM.periodic_int_shift (u := fun θ => H (θ, (extCx z).2)) hp ℓ hθ
  have e : extCx (z.1 + (fun i => (ℓ i : ℝ)), z.2) =
      ((extCx z).1 + fun i => (ℓ i : ℂ), (extCx z).2) := by ext i <;> simp [extCx]
  rw [e]
  exact congrArg Complex.re h

private theorem realWfield_periodic (b : PartialBlock n k) {R s : ℝ} {H : EC n k → ℂ}
    (hs : 0 < s) (hH : ext_class b R s H) (ℓ : Fin n → ℤ) {z : ER n k} (hz : z ∈ b.realDom R) :
    realWfield b.c (realHamiltonianExt b R H) (z.1 + (fun i => (ℓ i : ℝ)), z.2) =
      realWfield b.c (realHamiltonianExt b R H) z := by
  set a : ER n k := (fun i => (ℓ i : ℝ), 0) with ha
  have hza : (z.1 + (fun i => (ℓ i : ℝ)), z.2) = z + a :=
    Prod.ext (by simp [ha]) (by simp [ha])
  have hev : (fun x => realHamiltonianExt b R H (x + a)) =ᶠ[nhds z] realHamiltonianExt b R H := by
    filter_upwards [(isOpen_realDom b R).mem_nhds hz] with x hx
    have := realH_periodic b hs hH ℓ hx
    have e : x + a = (x.1 + (fun i => (ℓ i : ℝ)), x.2) :=
      Prod.ext (by simp [ha]) (by simp [ha])
    rw [e]
    exact this
  have hfd : fderiv ℝ (realHamiltonianExt b R H) (z + a) =
      fderiv ℝ (realHamiltonianExt b R H) z := by
    rw [← fderiv_comp_add_right]
    exact hev.fderiv_eq
  rw [hza]
  simp only [realWfield, hfd]

private theorem realH_energy (b : PartialBlock n k) {R s : ℝ} {H : EC n k → ℂ} (hs : 0 < s)
    (hH : ext_class b R s H) {J : Set ℝ} (hJ : J.OrdConnected) {r : ℝ} (hrR : r ≤ R)
    {y : ℝ → ER n k} (hy : ExtOrbit b r H J y) :
    ∀ t ∈ J, ∀ u ∈ J, realHamiltonianExt b R H (y t) = realHamiltonianExt b R H (y u) := by
  have hy' : KAM.ODE.IsSolutionIn (realWfield b.c (realHamiltonianExt b r H)) (b.realDom r) J y :=
    hy
  have hd : ∀ t ∈ J, HasDerivAt (fun u => realHamiltonianExt b R H (y u)) 0 t := fun t ht => by
    obtain ⟨hyt, hder⟩ := hy' t ht
    have hyR : y t ∈ b.realDom R := realDom_mono b hrR hyt
    have hzD : extCx (y t) ∈ Dom n b.base R s :=
      (extCx_mem_Dom_iff b hs _).2 ((mem_realDom_iff b R _).1 hyR)
    have hdiff := (fderiv_ext_real (isOpen_Dom (n := n) b.base R s) hH.1.differentiableOn
      (hreal_of_ext hH) hzD (realHamiltonianExt_eventually b R H hyR)).1
    have hev : realHamiltonianExt b r H =ᶠ[nhds (y t)] realHamiltonianExt b R H := by
      filter_upwards [realHamiltonianExt_eventually b r H hyt,
        realHamiltonianExt_eventually b R H hyR] with x h1 h2 using h1.trans h2.symm
    have hF : realWfield b.c (realHamiltonianExt b r H) (y t) =
        realWfield b.c (realHamiltonianExt b R H) (y t) := by
      simp only [realWfield, hev.fderiv_eq]
    rw [hF] at hder
    have := hdiff.hasFDerivAt.comp_hasDerivAt t hder
    rwa [show fderiv ℝ (realHamiltonianExt b R H) (y t)
      (realWfield b.c (realHamiltonianExt b R H) (y t)) = 0 from
      clm_realWfield_zero b.c _] at this
  have key : ∀ a ∈ J, ∀ c ∈ J, a ≤ c →
      realHamiltonianExt b R H (y c) = realHamiltonianExt b R H (y a) := by
    intro a ha c hc hac
    have hsub : Icc a c ⊆ J := hJ.out ha hc
    have hcont : ContinuousOn (fun u => realHamiltonianExt b R H (y u)) (Icc a c) := fun u hu =>
      (hd u (hsub hu)).continuousAt.continuousWithinAt
    exact constant_of_has_deriv_right_zero hcont
      (fun u hu => (hd u (hsub (Ico_subset_Icc_self hu))).hasDerivWithinAt) c ⟨hac, le_rfl⟩
  intro t ht t' ht'
  rcases le_total t t' with h | h
  · exact (key t ht t' ht' h).symm
  · exact key t' ht' t ht h

theorem real_system (b : PartialBlock n k) {R s : ℝ} {H : EC n k → ℂ}
    (hR : 0 < R) (hs : 0 < s) (hH : ext_class b R s H) :
    ContDiffOn ℝ ∞ (realHamiltonianExt b R H) (b.realDom R) ∧
    ContDiffOn ℝ 1 (realWfield b.c (realHamiltonianExt b R H)) (b.realDom R) ∧
    (∀ z ∈ b.realDom R, extCx (realWfield b.c (realHamiltonianExt b R H) z) = wfield b.c H (extCx z)) ∧
    (∀ ℓ : Fin n → ℤ, ∀ z ∈ b.realDom R,
      realHamiltonianExt b R H (z.1+(fun i => (ℓ i:ℝ)),z.2) = realHamiltonianExt b R H z) ∧
    (∀ ℓ : Fin n → ℤ, ∀ z ∈ b.realDom R,
      realWfield b.c (realHamiltonianExt b R H) (z.1+(fun i => (ℓ i:ℝ)),z.2) =
        realWfield b.c (realHamiltonianExt b R H) z) ∧
    (∀ J : Set ℝ, J.OrdConnected → ∀ r, 0 < r → r ≤ R → ∀ y, ExtOrbit b r H J y →
      ∀ t ∈ J, ∀ u ∈ J, realHamiltonianExt b R H (y t) = realHamiltonianExt b R H (y u)) :=
  ⟨realH_contDiff b hs hH, realWfield_contDiff b hs hH,
    fun _ hz => realWfield_cx b hs hH hz, fun ℓ _ hz => realH_periodic b hs hH ℓ hz,
    fun ℓ _ hz => realWfield_periodic b hs hH ℓ hz,
    fun _ hJ _ _ hrR _ hy => realH_energy b hs hH hJ hrR hy⟩

end KAM.Nekhoroshev

end
