/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PlanarAssembly.Data
public import KAM.Planetary.PlanarAssembly.Transport
public import KAM.Planetary.PlanarAssembly.Measure
public import KAM.Planetary.Newtonian.Assembly
public import KAM.Frozen.Planetary.Theorems.ProperlyDegenerateKAM

/-!
# Planar assembly: the planar two-planet theorem (Part 12)

`bpP:p12:planar` (`stepP:p12:pl-const`, `pl-pg`, `pl-mu`, `pl-S`, `pl-tori`, `pl-phys`): the
joint data of `pg_hypotheses` are fed to the sealed frozen P-G anchor, the cylinder set is
transported to the physical phase space by `transport` and `measure`, and the physical
Kolmogorov predicate is obtained from `movingKolmogorovSet_of_tube`.
-/

@[expose] public noncomputable section

open Set Real MeasureTheory Function

namespace KAM.Planetary

open KAM KAM.Kepler

namespace PlanarAssembly

private theorem cylinder_subset_of_le {V : Set (Fin 2 → ℝ)} {r r0 : ℝ} (hr : 0 < r)
    (hrr : r ≤ r0) : cylinder (b := 2) V r ⊆ cylinder (b := 2) V r0 := fun _ hz =>
  ⟨hz.1, fun j => (hz.2 j).trans_le (pow_le_pow_left₀ hr.le hrr 2)⟩

/-- bpP:p12:planar: exactly the frozen type. -/
theorem planar (G m0 : ℝ) (m a : Fin 2 → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : a 0 < a 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ mu0 d D : ℝ, 0 < mu0 ∧ 0 < d ∧ d < D ∧
      ∀ mu : ℝ, 0 < mu → mu < mu0 →
        ∃ S : Set (Phase (2 * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          MovingKolmogorovSet G m0 m a mu eta d D S := by
  obtain ⟨V, W, O, T, r0, δ, B, P0, Ω, β, hV, hVc, hVb, hW, hVW, hbd, hr0, hδ, hB, hO, hcl,
    hper, -, -, hana, hsym, -, hlat, hinj, hHam, hmaps, hP, hPper, hfreq, hBNF, htor, hsymm⟩ :=
    pg_hypotheses G m0 m a hG hm0 hm ha hsep eta heta
  have hinja : Function.Injective a := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> linarith
  have hax := axisData_canonical (n := 2) (by norm_num) ha hinja
  obtain ⟨rG, C, c, hrG, hrG0, hrG1, hC, hc, hmain⟩ :=
    properlyDegenerateKAM (a := 2) (b := 2) two_pos two_pos V hV hVc hVb W hW hVW hbd r0 1 B hr0
      one_pos hB (kepler_h (G * m0) m) (perturbation G m0 m T) P0 Ω β hP hPper hfreq hBNF htor
      hsymm
  obtain ⟨hr, hrrG, hr1, h2r, hthr, hthr1, hthrμ⟩ := radius_choices rG δ c hrG hrG1 hδ hc
  set r := secular_radius rG δ with hrdef
  refine ⟨coupling_threshold r c, tubeD (axisGap a), tubeBigD (axisGap a) (axisMax a), hthr,
    ?_, tubeD_lt_tubeBigD hax (by norm_num), fun μ hμ hμt => ?_⟩
  · have := hax.gap_pos
    unfold tubeD; positivity
  have hrr0 : r ≤ r0 := (hrrG.trans hrG0).le
  obtain ⟨Sc, hSc, hpos, -, -⟩ := hmain r μ hr hrrG hμ (hμt.trans_le hthr1) (hthrμ μ hμ hμt)
  have hQ1 : ∀ z ∈ O, ∀ k : Fin 2 → ℤ,
      z + fastShift (a := 2) (b := 2) k ∈ O ∧
        total_chart G m0 m T (z + fastShift (a := 2) (b := 2) k) = total_chart G m0 m T z :=
    fun z hz k => ⟨hper z hz k, hlat z hz k⟩
  have hcyl : cylinder (b := 2) V r ⊆ O :=
    (cylinder_subset_of_le hr hrr0).trans (subset_closure.trans hcl)
  have hSO : Sc ⊆ O := hSc.2.1.trans hcyl
  obtain ⟨-, -, hmeas, hvol⟩ := measure hO hana hsym hQ1 hinj hSc hSO
  have hδ' : 2 * r ^ 2 ≤ δ := by linarith
  obtain ⟨hsub, hpos', hfin⟩ := measure_in_tube hG hm0 ha hSc hvol hpos
    (hmaps r hr hrr0 hδ')
  refine ⟨_, hpos', hfin, movingKolmogorovSet_of_tube hax heta (by norm_num) hG hm0 hm hμ.le
    hmeas hsub fun z hz => ?_⟩
  obtain ⟨z0, hz0, rfl⟩ := hz
  obtain ⟨w, K, θ, hKz, hKS, hK, ⟨γ, τ, hγ, hτ, hw⟩, -⟩ := hSc.2.2 z0 hz0
  obtain ⟨hphys, hrange⟩ := transport hO hana hsym (H := degenerateHamiltonian (a := 2) (b := 2)
    (kepler_h (G * m0) m) (perturbation G m0 m T) μ) (G := movingHamiltonian G m0 m μ)
    (hHam μ) hQ1 hinj (U := cylinder (b := 2) V r) hcyl hK hγ hτ hw
  refine ⟨w, total_chart G m0 m T ∘ K, θ, by simp [hKz], ?_, hphys⟩
  rw [hrange]
  exact image_mono hKS

end PlanarAssembly

end KAM.Planetary

end
