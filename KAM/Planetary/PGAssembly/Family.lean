/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.FamilySigma
public import KAM.Planetary.PGAssembly.FamilyFreq

/-!
# P Part 5: the torus family (`bpP:p5:kset`, `bpP:p5:torus-conv`)

`torus_conv` assembles the family of whole tori from the single joint output of `two_scale_kam`
applied to the exact P3 record `pg_kam_hyp`, transports it through the chart `phi` with the
P1 `cyl_pipeline`, and retains the quantitative data (Lipschitz bound, lattice periodicity,
injectivity in the parameter, location, measure of the missed set) as `PGFamilySpec`.
`pgFamily` chooses the witness; `kset` and `rawUnion` are unions of whole ranges over a parameter
set. Declarations are copied verbatim from `P45Signatures.lean`; `frequency_bounds` lives in
`FamilyFreq` and the auxiliary lemmas in `FamilyAux` and `FamilySigma`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-FAM.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory

namespace KAM.Planetary

variable {a b : ℕ}

/-- Parameter actions J0; raw output is in frozen angle/action order. -/
structure PGFamily (n : ℕ) where
  raw : (Fin n → ℝ) → (Fin n → ℝ) → Phase n

def physicalTorus (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (F : PGFamily (a+b)) (J : Fin (a+b) → ℝ) : (Fin (a+b) → ℝ) → Phase (a+b) :=
  phi d r mu h ∘ angleScale (2*Real.pi) ∘ F.raw J

def PGFamilySpec (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (F : PGFamily (a+b)) : Prop :=
  IsSigmaCompact (pgD0 d r mu) ∧
  (∃ L : ℝ, 0 < L ∧ ∀ z ∈ pgD0 d r mu ×ˢ unitCube (a+b),
    ∀ z' ∈ pgD0 d r mu ×ˢ unitCube (a+b),
      ‖F.raw z.1 z.2-F.raw z'.1 z'.2‖ ≤ L*‖z-z'‖) ∧
  (∀ J ∈ pgD0 d r mu, ∀ theta, ∀ k : Fin (a+b) → ℤ,
    F.raw J (theta+fun i => (k i:ℝ)) = F.raw J theta+((fun i => (k i:ℝ)),0)) ∧
  (∀ J ∈ pgD0 d r mu, ∀ J' ∈ pgD0 d r mu, ∀ theta theta',
    physicalTorus d r mu h F J theta = physicalTorus d r mu h F J' theta' → J=J') ∧
  (∀ J ∈ pgD0 d r mu, ∀ theta,
    (F.raw J theta).2 ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rK) ∧
  (volume (({z : Phase (a+b) | z.2 ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rK ∧
      z.1 ∈ unitCube (a+b)}) \ (⋃ J ∈ pgD0 d r mu, range (F.raw J))) ≤
    ENNReal.ofReal (1+(1+2^(a+b))*(1+(4/3:ℝ)^(a+b))) *
      (volume (pgActionDomain d r mu \ pgD0 d r mu) +
        volume (realNbhd (pgActionDomain d r mu) (params d r mu).rK \ pgActionDomain d r mu))) ∧
  (∀ J ∈ pgD0 d r mu,
    IsCylinderTorus (degenerateHamiltonian d.H0 d.P mu) (cylinder d.V r)
      ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) (physicalTorus d r mu h F J))

/-- Assembly from the single joint two_scale_kam output, via P1 cyl_pipeline. -/
theorem torus_conv (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) :
    ∃ F : PGFamily (a+b), PGFamilySpec d r mu h F := by
  obtain ⟨-, hrho, hE, hD⟩ := pg_kam_dictionary d r mu h
  have H := pg_kam_hyp d r mu h
  obtain ⟨i, Φ, K, I₀, KC, hI₀, -, hi, hΦ, -, hKΦ, hTor, hinj, -, -, hvol⟩ :=
    two_scale_kam H (Eq.refl (pgKamScale d r mu).L)
  have hr' : 32 * eHat (pgKamScale d r mu) * rhoHat (pgKamScale d r mu) =
      (params d r mu).rK := by rw [hE, hrho]; rfl
  have hmemΩ : ∀ J ∈ pgD0 d r mu, realFreq (kamH d mu) J ∈
      omegaSet (pgActionDomain d r mu) (kamH d mu) (pgKamScale d r mu) := fun J hJ => by
    rw [← hD] at hJ
    exact ⟨⟨J, hJ.1, rfl⟩, hJ.2⟩
  have hI0J : ∀ J ∈ pgD0 d r mu, I₀ (realFreq (kamH d mu) J) = J := fun J hJ => by
    have hJ' := hJ
    rw [← hD] at hJ'
    exact ((hI₀ _ (hmemΩ J hJ)).2.2 J hJ' rfl).symm
  have hT : ∀ J ∈ pgD0 d r mu, IsLatticeTorus KAM.ODE.angleShift
      (fun z : Phase (a+b) => (kamH d mu (KAM.realInclusion (a+b) z.2) +
        kamF d r mu h (KAM.realInclusion₂ (a+b) z)).re)
      (univ ×ˢ realTube (pgActionDomain d r mu) (params d r mu).rK)
      (realFreq (kamH d mu) J) (K (realFreq (kamH d mu) J)) := fun J hJ => by
    have := (hTor _ (hmemΩ J hJ)).1
    rw [hr'] at this
    exact this
  have hmemRK : ∀ J ∈ pgD0 d r mu, ∀ θ, (K (realFreq (kamH d mu) J) θ).2 ∈
      realNbhd (pgActionDomain d r mu) (params d r mu).rK := fun J hJ θ => by
    obtain ⟨⟨-, hKO⟩, -⟩ := hT J hJ
    have := (hKO θ).1.2
    rwa [fam_realTube_eq] at this
  have hKe : ∀ J ∈ pgD0 d r mu, ∀ θ, K (realFreq (kamH d mu) J) θ = Φ (θ, i J) :=
    fun J hJ θ => by rw [hKΦ _ (hmemΩ J hJ) θ, hI0J J hJ]
  have hloc : ∀ J ∈ pgD0 d r mu, ∀ θ,
      angleScale (2*Real.pi) (K (realFreq (kamH d mu) J) θ) ∈ phiDomain d r mu ∧
      phi d r mu h (angleScale (2*Real.pi) (K (realFreq (kamH d mu) J) θ)) ∈ cylinder d.V r :=
    fun J hJ θ => location d r mu h _ (hmemRK J hJ θ)
  refine ⟨⟨fun J θ => K (realFreq (kamH d mu) J) θ⟩, fam_isSigmaCompact_D0 h, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · -- Lipschitz
    have hR : 0 < rhoHat (pgKamScale d r mu) := by
      rw [hrho]; exact params_rhoHat_pos d h.1 mu
    have hs : 0 < (pgKamScale d r mu).s := H.positive.2.1
    have he := H.eHat_nonneg
    have hn : (0:ℝ) ≤ (a:ℝ) + b := by positivity
    obtain ⟨L, hL, hLip⟩ := fam_lipschitz hR hs (c := 2560 * ((a:ℝ) + b) * eHat (pgKamScale d r mu))
      (c' := 768 * ((a:ℝ) + b) * eHat (pgKamScale d r mu)) (by positivity) (by positivity)
      Φ i _ hi hΦ
    refine ⟨L, hL, fun z hz z' hz' => ?_⟩
    have h1 := hLip z ⟨by rw [hD]; exact hz.1, mem_univ _⟩ z'
      ⟨by rw [hD]; exact hz'.1, mem_univ _⟩
    dsimp only
    rw [hKe _ hz.1, hKe _ hz'.1]
    exact h1
  · -- periodicity
    intro J hJ θ k
    obtain ⟨-, hper, -⟩ := hT J hJ
    exact hper θ k
  · -- injectivity in the parameter
    intro J hJ J' hJ' θ θ' heq
    obtain ⟨-, -, -, hQ2⟩ := phi_chart d r mu h
    simp only [physicalTorus, Function.comp_apply] at heq
    have h0 : (fastShift (0 : Fin a → ℤ) : Phase (a+b)) = 0 := by
      refine Prod.ext (funext fun i => ?_) rfl
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [fastShift, Fin.append_left, Fin.append_right]
    obtain ⟨m, hm⟩ := hQ2 _ (hloc J hJ θ).1 _ (hloc J' hJ' θ').1 0
      (by rw [h0, add_zero, heq])
    have hm' : angleScale (2*Real.pi) (K (realFreq (kamH d mu) J') θ') =
        angleScale (2*Real.pi) (K (realFreq (kamH d mu) J) θ + KAM.ODE.angleShift m) := by
      rw [angleScale_add_angleShift]; exact hm
    have hm'' := fam_angleScale_injective (by positivity) hm'
    have := (hinj _ (hmemΩ J' hJ') _ (hmemΩ J hJ) θ' θ m hm'').1
    rw [← hI0J J hJ, ← hI0J J' hJ', this]
  · exact hmemRK
  · -- measure
    have hmeas := hvol
    refine le_trans (measure_mono ?_) (hmeas.trans (le_of_eq ?_))
    · rintro z ⟨⟨hz2, hz1⟩, hznot⟩
      refine ⟨⟨⟨mem_univ _, ?_⟩, ?_⟩, ?_⟩
      · rw [hr', fam_realTube_eq]; exact hz2
      · intro hmem
        obtain ⟨ω, hω, θ, hθ⟩ := mem_iUnion₂.1 hmem
        refine hznot (mem_iUnion₂.2 ⟨I₀ ω, ?_, θ, ?_⟩)
        · rw [← hD]; exact (hI₀ ω hω).1
        · dsimp only
          rw [(hI₀ ω hω).2.1]; exact hθ
      · intro j; simpa using (Set.mem_pi.1 hz1) j (mem_univ j)
    · rw [hD, hr', fam_realTube_eq]; rfl
  · -- cylinder torus
    intro J hJ
    have hJV : blockFast J ∈ d.V := hJ.1.1.1.1
    have hw : (2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J = realFreq (kamH d mu) J :=
      (realFreq_kamH d (mu_mem_Icc h) hJV).symm
    rw [hw]
    obtain ⟨-, hch, hQ1, hQ2⟩ := phi_chart d r mu h
    refine cyl_pipeline hch (fun z hz k => hQ1 z hz k) (fun z hz z' hz' k hk =>
      hQ2 z hz z' hz' _ hk) (fam_lattice h (hT J hJ)) ?_
    rintro _ ⟨_, ⟨θ, rfl⟩, rfl⟩
    exact (hloc J hJ θ).2

def pgFamily (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu) : PGFamily (a+b) :=
  (torus_conv d r mu h).choose

def kset (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (B : Set (Fin (a+b) → ℝ)) : Set (Phase (a+b)) :=
  ⋃ J ∈ B, range (physicalTorus d r mu h (pgFamily d r mu h) J)

def rawUnion (d : PGData a b) (r mu : ℝ) (h : admissible d (pgRstar d) r mu)
    (B : Set (Fin (a+b) → ℝ)) : Set (Phase (a+b)) :=
  ⋃ J ∈ B, range ((pgFamily d r mu h).raw J)

end KAM.Planetary

end
