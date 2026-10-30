/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Analytic.HoloAnalytic
public import KAM.Wave.Analytic.ComplexificationLp
public import KAM.Strip.Cauchy

/-!
# Real-analytic tori from complex strips

Blueprint-W `bpW:w1:torus-analytic` (package W1-ANALYTIC). This is source-faithful infrastructure
used by several nodes; the dependency graph is still being built.

`WaveSpaceC` is `E^ℂ_{1,1}`, two copies of `ℓ²_ℂ`; `complexifyWave` and `reWave` are `ι` and `re` on
it. A holomorphic, real-on-reals, `1`-periodic map `K̃` on the strip `T_s = complexStrip 2 s` with
values in `WaveSpaceC` restricts to a real-analytic `ℤ²`-periodic map `K = re ∘ K̃|_{ℝ²}` into
`WaveSpace`, whose derivative is `re ∘ D K̃` (`KAM.Wave.torus_analytic`).
-/

@[expose] public noncomputable section

open Filter Topology

namespace KAM.Wave

/-- `E^ℂ_{1,1}` in weighted coordinates: two copies of `ℓ²_ℂ` (blueprint `bpW:w1:complexification`). -/
abbrev WaveSpaceC : Type :=
  lp (fun _ : ℕ+ => ℂ) 2 × lp (fun _ : ℕ+ => ℂ) 2

/-- The inclusion `ι : E_{1,1} → E^ℂ_{1,1}`, componentwise. -/
def complexifyWave : WaveSpace →L[ℝ] WaveSpaceC := complexifyLp.prodMap complexifyLp

/-- The real part `re : E^ℂ_{1,1} → E_{1,1}`, componentwise. -/
def reWave : WaveSpaceC →L[ℝ] WaveSpace := reLp.prodMap reLp

@[simp] theorem reWave_complexifyWave (w : WaveSpace) : reWave (complexifyWave w) = w := by
  simp [reWave, complexifyWave]

/-- Blueprint `bpW:w1:torus-analytic`. -/
theorem torus_analytic {s : ℝ} (hs : 0 < s) {Kt : (Fin 2 → ℂ) → WaveSpaceC}
    (hK : DifferentiableOn ℂ Kt (KAM.complexStrip 2 s))
    (hreal : ∀ θ : Fin 2 → ℝ, ∃ w : WaveSpace, Kt (KAM.realInclusion 2 θ) = complexifyWave w)
    (hper : ∀ z ∈ KAM.complexStrip 2 s, ∀ k : Fin 2 → ℤ, Kt (z + fun i => (k i : ℂ)) = Kt z) :
    AnalyticOnNhd ℝ (fun θ : Fin 2 → ℝ => reWave (Kt (KAM.realInclusion 2 θ))) Set.univ ∧
      (∀ (θ : Fin 2 → ℝ) (k : Fin 2 → ℤ),
        reWave (Kt (KAM.realInclusion 2 (θ + fun i => (k i : ℝ)))) =
          reWave (Kt (KAM.realInclusion 2 θ))) ∧
      ∀ (θ h : Fin 2 → ℝ),
        fderiv ℝ (fun θ : Fin 2 → ℝ => reWave (Kt (KAM.realInclusion 2 θ))) θ h =
          reWave (fderiv ℂ Kt (KAM.realInclusion 2 θ) (KAM.realInclusion 2 h)) := by
  have hmem : ∀ θ : Fin 2 → ℝ, KAM.realInclusion 2 θ ∈ KAM.complexStrip 2 s := fun θ i => by
    simpa using hs
  have han := analyticOnNhd_of_differentiableOn_banach (KAM.isOpen_complexStrip 2 s) hK
  have key := fun θ : Fin 2 → ℝ => analyticAt_real_part (KAM.realInclusion 2) complexifyWave reWave
    reWave_complexifyWave (han _ (hmem θ)) (Eventually.of_forall fun θ' => hreal θ')
  refine ⟨fun θ _ => (key θ).1, fun θ k => ?_, fun θ h => (key θ).2.2 h⟩
  have : KAM.realInclusion 2 (θ + fun i => (k i : ℝ)) =
      KAM.realInclusion 2 θ + fun i => (k i : ℂ) := by
    ext i; simp
  rw [this, hper _ (hmem θ) k]

end KAM.Wave
