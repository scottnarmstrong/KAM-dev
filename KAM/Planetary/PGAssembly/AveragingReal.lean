/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.AveragingFacts
public import KAM.Planetary.PGAssembly.JetsAverage
public import KAM.Planetary.PGAssembly.ExtensionTube

/-!
# P Part 5: reality of the extension on its real slice (`stepP:p5:av-R1`)

The tube `extensionDomain d δ` is open, connected and invariant under complex conjugation, and the
extension `P̃` agrees with the real function `d.P` on an open real subset of it. The reflection
`z ↦ conj (P̃ (conj z))` is holomorphic, so the identity theorem gives `P̃` real at every real point
of the tube (`ext_P_real`), with no off-cylinder equality assumed.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-AV (revision 4).
-/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace KAM.Planetary

variable {a b n N : ℕ}

/-- Pointwise complex conjugation of a vector. -/
def conjPi (y : Fin N → ℂ) : Fin N → ℂ := fun i => starRingEnd ℂ (y i)

theorem conjPi_conjPi (y : Fin N → ℂ) : conjPi (conjPi y) = y := by
  ext i; simp [conjPi]

theorem conjPi_add (y z : Fin N → ℂ) : conjPi (y + z) = conjPi y + conjPi z := by
  ext i; simp [conjPi]

theorem norm_conjPi (y : Fin N → ℂ) : ‖conjPi y‖ = ‖y‖ := by
  simp [Pi.norm_def, conjPi]

theorem continuous_conjPi : Continuous (conjPi : (Fin N → ℂ) → Fin N → ℂ) :=
  continuous_pi fun i => Complex.continuous_conj.comp (continuous_apply i)

theorem conjPi_realInclusion (x : Fin N → ℝ) : conjPi (KAM.realInclusion N x) =
    KAM.realInclusion N x := by
  ext i; simp [conjPi]

theorem differentiableAt_conj_conj_pi {F : (Fin N → ℂ) → ℂ} {z : Fin N → ℂ}
    (hF : DifferentiableAt ℂ F (conjPi z)) :
    DifferentiableAt ℂ (fun y => starRingEnd ℂ (F (conjPi y))) z := by
  set L := fderiv ℂ F (conjPi z) with hL
  let Lb : (Fin N → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun h => starRingEnd ℂ (L (conjPi h))
      map_add' := fun x y => by simp [conjPi_add]
      map_smul' := fun c x => by
        have : conjPi (c • x) = starRingEnd ℂ c • conjPi x := by ext i; simp [conjPi]
        simp [this, map_smul] }
  have hLb : ∀ h, LinearMap.toContinuousLinearMap Lb h = starRingEnd ℂ (L (conjPi h)) :=
    fun h => rfl
  refine ⟨LinearMap.toContinuousLinearMap Lb, ?_⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have h1 := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hF.hasFDerivAt)
  have h2 : Tendsto (conjPi : (Fin N → ℂ) → Fin N → ℂ) (𝓝 0) (𝓝 0) := by
    have h0 : conjPi (0 : Fin N → ℂ) = 0 := by ext; simp [conjPi]
    have := (continuous_conjPi (N := N)).tendsto 0
    rwa [h0] at this
  have h3 := h1.comp_tendsto h2
  rw [← Asymptotics.isLittleO_norm_left, ← Asymptotics.isLittleO_norm_right] at h3 ⊢
  refine h3.congr (fun h => ?_) (fun h => ?_)
  · simp only [hLb, ← hL, Function.comp]
    rw [← Complex.norm_conj, map_sub, map_sub, conjPi_add]
  · simp [norm_conjPi]

theorem differentiableOn_conj_conj_pi {F : (Fin N → ℂ) → ℂ} {U : Set (Fin N → ℂ)}
    (hU : IsOpen U) (hsym : ∀ y ∈ U, conjPi y ∈ U) (hF : DifferentiableOn ℂ F U) :
    DifferentiableOn ℂ (fun y => starRingEnd ℂ (F (conjPi y))) U := fun y hy =>
  (differentiableAt_conj_conj_pi
    ((hF _ (hsym y hy)).differentiableAt (hU.mem_nhds (hsym y hy)))).differentiableWithinAt

/-! ### Packing a complex phase point into one vector -/

/-- `(θ, I) ↦ (θ_1,…,θ_n,I_1,…,I_n)`. -/
def pkC (z : PGComplexPhase n) : Fin (n+n) → ℂ := Fin.append z.1 z.2

/-- The inverse of `pkC`. -/
def upkC (y : Fin (n+n) → ℂ) : PGComplexPhase n := (blockFast y, blockSlow y)

theorem upkC_pkC (z : PGComplexPhase n) : upkC (pkC z) = z :=
  Prod.ext (pgAv_blockFast_append _ _) (pgAv_blockSlow_append _ _)

theorem pkC_upkC (y : Fin (n+n) → ℂ) : pkC (upkC y) = y := append_blocks y

theorem continuous_pkC : Continuous (pkC : PGComplexPhase n → Fin (n+n) → ℂ) := by
  refine continuous_pi fun i => ?_
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [pkC, Fin.append_left, Fin.append_right]
  · exact (continuous_apply j).comp continuous_fst
  · exact (continuous_apply j).comp continuous_snd

theorem continuous_upkC : Continuous (upkC : (Fin (n+n) → ℂ) → PGComplexPhase n) :=
  (continuous_pi fun j => continuous_apply _).prodMk (continuous_pi fun j => continuous_apply _)

theorem differentiable_upkC : Differentiable ℂ (upkC : (Fin (n+n) → ℂ) → PGComplexPhase n) := by
  refine Differentiable.prodMk (differentiable_pi.2 fun j => ?_) (differentiable_pi.2 fun j => ?_)
  · exact differentiable_apply (𝕜 := ℂ) _
  · exact differentiable_apply (𝕜 := ℂ) _

/-- `(θ, I) ↦` real packed vector, and its inverse. -/
def pkR (z : Phase n) : Fin (n+n) → ℝ := Fin.append z.1 z.2

def upkR (x : Fin (n+n) → ℝ) : Phase n := (blockFast x, blockSlow x)

theorem upkC_realInclusion (x : Fin (n+n) → ℝ) :
    upkC (KAM.realInclusion (n+n) x) = KAM.realInclusion₂ n (upkR x) := rfl

theorem pkC_realInclusion₂ (w : Phase n) :
    pkC (KAM.realInclusion₂ n w) = KAM.realInclusion (n+n) (pkR w) := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [pkC, pkR, Fin.append_left, Fin.append_right, KAM.realInclusion_apply,
      KAM.realInclusion₂_apply]

theorem upkR_pkR (w : Phase n) : upkR (pkR w) = w :=
  Prod.ext (pgAv_blockFast_append _ _) (pgAv_blockSlow_append _ _)

theorem continuous_upkR : Continuous (upkR : (Fin (n+n) → ℝ) → Phase n) :=
  (continuous_pi fun j => continuous_apply _).prodMk (continuous_pi fun j => continuous_apply _)

/-! ### The tube -/

/-- The real base of the tube: one fast-action fibre over `closure V`, slow part `≤ r0/2`. -/
def pgBase (d : PGData a b) : Set (Phase (a+b)) :=
  {w | blockFast w.2 ∈ closure d.V ∧ ‖(blockSlow w.2, blockSlow w.1)‖ ≤ d.r0/2}

theorem isPreconnected_pgBase (d : PGData a b) : IsPreconnected (pgBase d) := by
  have hS : IsPreconnected (closure d.V ×ˢ ((univ : Set (Fin a → ℝ)) ×ˢ
      (closedBall (0 : (Fin b → ℝ) × (Fin b → ℝ)) (d.r0/2)))) :=
    d.hVc.isPreconnected.closure.prod (isPreconnected_univ.prod
      (convex_closedBall _ _).isPreconnected)
  have himg := hS.image (fun p : (Fin a → ℝ) × ((Fin a → ℝ) × ((Fin b → ℝ) × (Fin b → ℝ))) =>
      assemble p.1 p.2.1 p.2.2.1 p.2.2.2)
    (by
      refine Continuous.continuousOn ?_
      refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun j => ?_)
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
          simp only [Fin.append_left, Fin.append_right]
        · exact (continuous_apply i).comp (continuous_fst.comp continuous_snd)
        · exact (continuous_apply i).comp (continuous_snd.comp (continuous_snd.comp
            continuous_snd))
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
          simp only [Fin.append_left, Fin.append_right]
        · exact (continuous_apply i).comp continuous_fst
        · exact (continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp
            continuous_snd)))
  convert himg using 1
  ext w
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(blockFast w.2, blockFast w.1, (blockSlow w.2, blockSlow w.1)),
      ⟨h1, mem_univ _, ?_⟩, ?_⟩
    · simpa using h2
    · exact Prod.ext (by simp only [assemble]; exact append_blocks _)
        (by simp only [assemble]; exact append_blocks _)
  · rintro ⟨⟨I, φ, p, q⟩, ⟨h1, -, h3⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · show blockFast (Fin.append I p) ∈ closure d.V
      rw [pgAv_blockFast_append]; exact h1
    · show ‖(blockSlow (Fin.append I p), blockSlow (Fin.append φ q))‖ ≤ d.r0/2
      rw [pgAv_blockSlow_append, pgAv_blockSlow_append]
      simpa using h3

theorem isPreconnected_extensionDomain (d : PGData a b) (δ : ℝ) :
    IsPreconnected (extensionDomain d δ) := by
  have hS : IsPreconnected (pgBase d ×ˢ ball (0 : PGComplexPhase (a+b)) δ) :=
    (isPreconnected_pgBase d).prod (convex_ball _ _).isPreconnected
  have himg := hS.image (fun p : Phase (a+b) × PGComplexPhase (a+b) =>
      KAM.realInclusion₂ (a+b) p.1 + p.2)
    (((KAM.realInclusion₂ (a+b)).continuous.comp continuous_fst).add continuous_snd).continuousOn
  convert himg using 1
  ext z
  constructor
  · rintro ⟨w, hw1, hw2, hw3⟩
    exact ⟨(w, z - KAM.realInclusion₂ (a+b) w), ⟨⟨hw1, hw2⟩, by simpa using hw3⟩, by simp⟩
  · rintro ⟨⟨w, v⟩, ⟨⟨h1, h2⟩, h3⟩, rfl⟩
    exact ⟨w, h1, h2, by simpa using h3⟩

theorem conj_mem_extensionDomain (d : PGData a b) (δ : ℝ) {z : PGComplexPhase (a+b)}
    (hz : z ∈ extensionDomain d δ) :
    (conjPi z.1, conjPi z.2) ∈ extensionDomain d δ := by
  obtain ⟨w, hw1, hw2, hw3⟩ := hz
  refine ⟨w, hw1, hw2, ?_⟩
  have : ((conjPi z.1, conjPi z.2) - KAM.realInclusion₂ (a+b) w) =
      (conjPi (z - KAM.realInclusion₂ (a+b) w).1, conjPi (z - KAM.realInclusion₂ (a+b) w).2) := by
    refine Prod.ext ?_ ?_ <;> ext i <;> simp [conjPi]
  rw [this, Prod.norm_def, norm_conjPi, norm_conjPi, ← Prod.norm_def]
  exact hw3


/-- The extension is real at every real point of its tube (reflection + identity theorem). -/
theorem ext_P_real (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0) (w : Phase (a+b))
    (hw : KAM.realInclusion₂ (a+b) w ∈ extensionDomain d (pgExtension d).delta) :
    ((pgExtension d).P mu (KAM.realInclusion₂ (a+b) w)).im = 0 := by
  set E := pgExtension d with hE
  set U : Set (Fin ((a+b)+(a+b)) → ℂ) := upkC ⁻¹' extensionDomain d E.delta with hU
  have hUo : IsOpen U := (isOpen_extensionDomain d _).preimage continuous_upkC
  have hUc : IsPreconnected U := by
    have h := (isPreconnected_extensionDomain d E.delta).image pkC continuous_pkC.continuousOn
    convert h using 1
    ext y
    constructor
    · intro hy; exact ⟨upkC y, hy, pkC_upkC y⟩
    · rintro ⟨z, hz, rfl⟩; show upkC (pkC z) ∈ extensionDomain d E.delta; rw [upkC_pkC]; exact hz
  have hsym : ∀ y ∈ U, conjPi y ∈ U := by
    intro y hy
    have hy' : upkC y ∈ extensionDomain d E.delta := hy
    have := conj_mem_extensionDomain d E.delta hy'
    have e : upkC (conjPi y) = (conjPi (upkC y).1, conjPi (upkC y).2) := rfl
    show upkC (conjPi y) ∈ extensionDomain d E.delta
    rw [e]; exact this
  let F : (Fin ((a+b)+(a+b)) → ℂ) → ℂ := fun y => E.P mu (upkC y)
  have hF : DifferentiableOn ℂ F U :=
    (E.holo mu hmu).comp differentiable_upkC.differentiableOn (fun y hy => hy)
  have hG := differentiableOn_conj_conj_pi hUo hsym hF
  -- the open real set where the extension equals the real function
  let Vr : Set (Fin ((a+b)+(a+b)) → ℝ) :=
    {x | blockFast (upkR x).2 ∈ d.V ∧ ‖(blockSlow (upkR x).2, blockSlow (upkR x).1)‖ < d.r0/2}
  have hVo : IsOpen Vr := by
    refine IsOpen.inter ?_ ?_
    · exact d.hV.preimage (continuous_blockFast_real.comp (continuous_snd.comp continuous_upkR))
    · exact isOpen_lt (continuous_norm.comp
        (((continuous_blockSlow_real.comp (continuous_snd.comp continuous_upkR))).prodMk
          (continuous_blockSlow_real.comp (continuous_fst.comp continuous_upkR)))) continuous_const
  have hVne : Vr.Nonempty := by
    obtain ⟨I0, hI0⟩ := d.hVc.nonempty
    refine ⟨pkR ((0 : Fin (a+b) → ℝ), Fin.append I0 (0 : Fin b → ℝ)), ?_⟩
    simp only [Vr, upkR_pkR, pgAv_blockSlow_append, pgAv_blockFast_append, mem_ofPred_eq]
    refine ⟨hI0, ?_⟩
    have : blockSlow (0 : Fin (a+b) → ℝ) = 0 := rfl
    rw [this, Prod.norm_def]; simp [d.hr0]
  have hmemV : ∀ x ∈ Vr, KAM.realInclusion₂ (a+b) (upkR x) ∈ extensionDomain d E.delta := by
    intro x hx
    exact ⟨upkR x, subset_closure hx.1, hx.2.le, by simpa using E.delta_pos⟩
  have hVU : KAM.realInclusion ((a+b)+(a+b)) '' Vr ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    show upkC (KAM.realInclusion ((a+b)+(a+b)) x) ∈ extensionDomain d E.delta
    rw [upkC_realInclusion]; exact hmemV x hx
  have heq : ∀ x ∈ Vr, F (KAM.realInclusion ((a+b)+(a+b)) x) =
      starRingEnd ℂ (F (conjPi (KAM.realInclusion ((a+b)+(a+b)) x))) := by
    intro x hx
    rw [conjPi_realInclusion]
    have hcyl : upkR x ∈ closure (cylinder d.V d.r0 : Set (Phase (a+b))) := by
      refine subset_closure ⟨hx.1, fun j => ?_⟩
      have hpq := hx.2
      rw [Prod.norm_def, max_lt_iff] at hpq
      have h1 := (norm_le_pi_norm (blockSlow (upkR x).2) j).trans_lt hpq.1
      have h2 := (norm_le_pi_norm (blockSlow (upkR x).1) j).trans_lt hpq.2
      rw [Real.norm_eq_abs] at h1 h2
      have h1' := sq_lt_sq' (by linarith [abs_lt.1 h1]) (abs_lt.1 h1).2
      have h2' := sq_lt_sq' (by linarith [abs_lt.1 h2]) (abs_lt.1 h2).2
      show (blockSlow (upkR x).2 j)^2 + (blockSlow (upkR x).1 j)^2 < d.r0^2
      nlinarith [d.hr0]
    have := E.agrees mu hmu (upkR x) hcyl (hmemV x hx)
    show E.P mu (upkC _) = starRingEnd ℂ (E.P mu (upkC _))
    rw [upkC_realInclusion, this, Complex.conj_ofReal]
  have key := real_slice_identity hUo hUc hF hG hVo hVne hVU heq
  have hy0 : pkC (KAM.realInclusion₂ (a+b) w) ∈ U := by
    show upkC (pkC (KAM.realInclusion₂ (a+b) w)) ∈ extensionDomain d E.delta
    rw [upkC_pkC]; exact hw
  have := key hy0
  simp only [F, upkC_pkC] at this
  rw [pkC_realInclusion₂, conjPi_realInclusion, ← pkC_realInclusion₂, upkC_pkC] at this
  exact Complex.conj_eq_iff_im.1 this.symm

end KAM.Planetary

end
