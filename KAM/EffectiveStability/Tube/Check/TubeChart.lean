/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Check.Confine
public import KAM.EffectiveStability.Tube.Check.Gamma
public import KAM.EffectiveStability.Tube.Check.Lip

/-!
# Tube confinement in the modal polar chart (T2-CONF, N5b)

The generic tube checker theorem in the chart `x ↦ (u, φ) = tubeChart V B x` of N2, with every
literal check an abstract numeric hypothesis on functions of `(u, φ)`, so that the kernel checks
plug in. Data:

* an orthogonal `V`, a `2π`-periodic differentiable shift `B` with `bmin ≤ B ≤ bmax`,
  `|∂_{φ_b} B_l| ≤ β_l` and the symmetry `∂_{θ_i} B_l = ∂_{θ_l} B_i` (N2 (D));
* a Hamiltonian `H` of class `C²` with `H ∘ Rinv ∘ polar = h̃ ∘ shiftChart B` (N5a);
* observables `f j` of `(u, φ)` (`2π`-periodic, differentiable), `F_j = f_j ∘ tubeChart V B`,
  centred at `c_j = F_j(z)` (`z` the nominal state), with a literal `c̃_j`,
  `|f_j(u(z), φ(z)) - c̃_j| ≤ γ_j`.

Checks, on the box `|u_l| ≤ ρ` (all `φ`):
* rates `|Σ_a (D_a f_j ∂_{φ_a} h̃ - ∂_{φ_a} f_j D_a h̃)| ≤ η_j` (`reducedBracket`), `T η_j < δ/2`;
* the face bound `|f_j - c̃_j - u_j| ≤ ε_j`, `δ + ε_j + γ_j < ρ`;
* partials `|∂_{u_l} f_j| ≤ Fu_{jl}`, `|∂_{φ_b} f_j| ≤ Fφ_{jb}` (for the ball `Q`);
* a property `Pγ j` of the planet actions `Γ_j(I, φ)` for `|I_k - B_k(φ)| ≤ ρ` (N6: two-sided
  eccentricity bounds).

And on the ball `Q = closedBall z r` (sup norm): mode bounds `|q_j| + |p_j| ≤ A_j`,
`0 < a_j ≤ q_j² + p_j²` (`modeBounds_of_mem_closedBall`), `|u_j(z)| ≤ μ_j`,
`μ_j + chartLip … (Pi.single j 1) 0 · r < ρ` and `chartLip … (Fu j) (Fφ j) · r ≤ δ/2`.

Conclusion (`tubeChart_confinement`): every `z₀ ∈ Q` has a solution on `(-T₁, T₁)`, `T₁ > T`,
unique among solutions on intervals through `0`, with `Pγ j (Γ_j(z(t)))` for `|t| ≤ T`.
`mem_closedBall_iff_coords` writes `Q` in the coordinates of the T2-CONF statement.
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.Tube

open Set Filter Topology Matrix Real

theorem abs_fderiv_fst_apply_single_le (j l : Fin 3) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) :
    |fderiv ℝ (fun p : (Fin 3 → ℝ) × (Fin 2 → ℝ) => p.1 j) p (Pi.single l 1, 0)| ≤
      (Pi.single j 1 : Fin 3 → ℝ) l := by
  have h : HasFDerivAt (fun p : (Fin 3 → ℝ) × (Fin 2 → ℝ) => p.1 j)
      ((ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) (Fin 2 → ℝ))) p := by
    have e : (fun p : (Fin 3 → ℝ) × (Fin 2 → ℝ) => p.1 j) =
        ⇑((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j).comp
          (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) (Fin 2 → ℝ))) := rfl
    rw [e]
    exact ContinuousLinearMap.hasFDerivAt _
  rw [h.fderiv]
  by_cases hjl : j = l
  · subst hjl; simp
  · simp [hjl, Ne.symm hjl]

theorem fderiv_fst_apply_snd (j : Fin 3) (p : (Fin 3 → ℝ) × (Fin 2 → ℝ)) (b : Fin 2) :
    fderiv ℝ (fun p : (Fin 3 → ℝ) × (Fin 2 → ℝ) => p.1 j) p (0, Pi.single b 1) = 0 := by
  have h : HasFDerivAt (fun p : (Fin 3 → ℝ) × (Fin 2 → ℝ) => p.1 j)
      ((ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) (Fin 2 → ℝ))) p := by
    have e : (fun p : (Fin 3 → ℝ) × (Fin 2 → ℝ) => p.1 j) =
        ⇑((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j).comp
          (ContinuousLinearMap.fst ℝ (Fin 3 → ℝ) (Fin 2 → ℝ))) := rfl
    rw [e]
    exact ContinuousLinearMap.hasFDerivAt _
  rw [h.fderiv]
  simp

theorem chartLip_nonneg {Nv : ℝ} {A a β Fu : Fin 3 → ℝ} {Fφ : Fin 2 → ℝ} (hN : 0 ≤ Nv)
    (hA : ∀ j, 0 ≤ A j) (ha : ∀ j, 0 < a j) (hβ : ∀ l, 0 ≤ β l) (hFu : ∀ l, 0 ≤ Fu l)
    (hFφ : ∀ b, 0 ≤ Fφ b) : 0 ≤ chartLip Nv A a β Fu Fφ := by
  have hθ := thetaW_nonneg hA ha
  exact mul_nonneg hN (add_nonneg
    (Finset.sum_nonneg fun l _ => mul_nonneg (hFu l)
      (add_nonneg (hA l) (mul_nonneg (hβ l) (add_nonneg (hθ 0) (hθ 1)))))
    (Finset.sum_nonneg fun b _ => mul_nonneg (hFφ b) (hθ b)))

/-- The sup-norm ball in phase space in coordinates, in the order of the T2-CONF statement
(`ξ = x.2` first, then `η = x.1`). -/
theorem mem_closedBall_iff_coords {z₀ z : (Fin 3 → ℝ) × (Fin 3 → ℝ)} {r : ℝ} (hr : 0 ≤ r) :
    z₀ ∈ Metric.closedBall z r ↔ ∀ j, |z₀.2 j - z.2 j| ≤ r ∧ |z₀.1 j - z.1 j| ≤ r := by
  rw [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def, max_le_iff,
    pi_norm_le_iff_of_nonneg hr, pi_norm_le_iff_of_nonneg hr]
  simp only [Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, Real.norm_eq_abs]
  exact ⟨fun h j => ⟨h.2 j, h.1 j⟩, fun h => ⟨fun j => (h j).2, fun j => (h j).1⟩⟩

/-- **Tube confinement in the modal polar chart.** See the module docstring. -/
theorem tubeChart_confinement {V : Matrix (Fin 3) (Fin 3) ℝ} (hV : Vᵀ * V = 1)
    {B : (Fin 2 → ℝ) → (Fin 3 → ℝ)} {H : (Fin 3 → ℝ) × (Fin 3 → ℝ) → ℝ}
    {h : (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ} {f : Fin 3 → (Fin 3 → ℝ) × (Fin 2 → ℝ) → ℝ}
    {bmin bmax β ct ε γ η μ A a : Fin 3 → ℝ} {Fu : Fin 3 → Fin 3 → ℝ}
    {Fφ : Fin 3 → Fin 2 → ℝ} {δ ρ T Nv r : ℝ} {z : (Fin 3 → ℝ) × (Fin 3 → ℝ)}
    {Pγ : Fin 3 → ℝ → Prop}
    -- the shift `B`
    (hBper : ShiftPeriodic B) (hB : Differentiable ℝ B) (hρ : ∀ j, ρ < bmin j)
    (hBmin : ∀ φ j, bmin j ≤ B φ j) (hBmax : ∀ φ j, B φ j ≤ bmax j)
    (hβ : ∀ φ (b : Fin 2) (l : Fin 3), |fderiv ℝ B φ (Pi.single b 1) l| ≤ β l)
    (hsym : ∀ φ (i l : Fin 3), fderiv ℝ B φ (phiOf (Pi.single i 1)) l =
      fderiv ℝ B φ (phiOf (Pi.single l 1)) i)
    -- the Hamiltonian
    (hH : ContDiff ℝ 2 H) (hHh : ∀ y ∈ actionPos 3, H (rotMap V (polar y)) = h (shiftChart B y))
    (hhd : ∀ u φ, (∀ l, |u l| ≤ ρ) → DifferentiableAt ℝ h (u, φ))
    -- the observables
    (hfper : ∀ j, ObsPeriodic (f j)) (hfd : ∀ j, Differentiable ℝ (f j))
    -- rates, faces, centre
    (hη : ∀ j u φ, (∀ l, |u l| ≤ ρ) → |reducedBracket (f j) h (u, φ)| ≤ η j)
    (hT : 0 ≤ T) (hTη : ∀ j, T * η j < δ / 2)
    (hface : ∀ j u φ, (∀ l, |u l| ≤ ρ) → |f j (u, φ) - ct j - u j| ≤ ε j)
    (hc : ∀ j, |f j (tubeChart V B z) - ct j| ≤ γ j) (hερ : ∀ j, δ + ε j + γ j < ρ)
    -- the ball `Q = closedBall z r`
    (hN : ∀ j, ∑ k, |V k j| ≤ Nv)
    (hAb : ∀ y ∈ Metric.closedBall z r, ∀ j, |(rotMap Vᵀ y).1 j| + |(rotMap Vᵀ y).2 j| ≤ A j)
    (ha : ∀ j, 0 < a j) (hab : ∀ y ∈ Metric.closedBall z r, ∀ j, a j ≤ modeSq V y j)
    (hμ : ∀ j, |tubeU V B z j| ≤ μ j)
    (hμρ : ∀ j, μ j + chartLip Nv A a β (Pi.single j 1) 0 * r < ρ)
    (hFu : ∀ j u φ, (∀ l, |u l| ≤ ρ) → ∀ l, |fderiv ℝ (f j) (u, φ) (Pi.single l 1, 0)| ≤ Fu j l)
    (hFφ : ∀ j u φ, (∀ l, |u l| ≤ ρ) → ∀ b, |fderiv ℝ (f j) (u, φ) (0, Pi.single b 1)| ≤ Fφ j b)
    (hLF : ∀ j, chartLip Nv A a β (Fu j) (Fφ j) * r ≤ δ / 2)
    -- the planet actions on the tube
    (hG : ∀ (φ : Fin 2 → ℝ) (I : Fin 3 → ℝ), (∀ k, |I k - B φ k| ≤ ρ) → ∀ j,
      Pγ j (chartGamma V I φ j))
    {z₀ : (Fin 3 → ℝ) × (Fin 3 → ℝ)} (hz₀ : z₀ ∈ Metric.closedBall z r) :
    ∃ T₁ : ℝ, T < T₁ ∧ ∃ x : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ), x 0 = z₀ ∧
      (∀ t ∈ Ioo (-T₁) T₁, HasDerivAt x (KAM.hamiltonianVectorField H (x t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin 3 → ℝ) × (Fin 3 → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I →
        y 0 = z₀ → (∀ t ∈ I, HasDerivAt y (KAM.hamiltonianVectorField H (y t)) t) →
        ∀ t ∈ I, t ∈ Ioo (-T₁) T₁ → y t = x t) ∧
      ∀ t : ℝ, |t| ≤ T → ∀ j, Pγ j (KAM.Planetary.oscillatorAction (x t).2 (x t).1 j) := by
  -- elementary consequences of the numeric hypotheses
  have hr : 0 ≤ r := Metric.nonempty_closedBall.1 ⟨z₀, hz₀⟩
  have hN0 : 0 ≤ Nv := le_trans (Finset.sum_nonneg fun k _ => abs_nonneg (V k 0)) (hN 0)
  have hA0 : ∀ j, 0 ≤ A j := fun j => (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans
    (hAb z (Metric.mem_closedBall_self hr) j)
  have hβ0 : ∀ l, 0 ≤ β l := fun l => (abs_nonneg _).trans (hβ 0 0 l)
  have hLu0 : ∀ j, 0 ≤ chartLip Nv A a β (Pi.single j 1) 0 := fun j =>
    chartLip_nonneg hN0 hA0 ha hβ0 (fun l => by by_cases h : l = j <;> simp [h]) fun _ => le_rfl
  have hρ0 : 0 ≤ ρ := by
    have := hμρ 0; have := mul_nonneg (hLu0 0) hr; have := (abs_nonneg _).trans (hμ 0)
    linarith
  have hbox0 : ∀ l, |(0 : Fin 3 → ℝ) l| ≤ ρ := fun l => by simpa using hρ0
  have hFu0 : ∀ j l, 0 ≤ Fu j l := fun j l => (abs_nonneg _).trans (hFu j 0 0 hbox0 l)
  have hFφ0 : ∀ j b, 0 ≤ Fφ j b := fun j b => (abs_nonneg _).trans (hFφ j 0 0 hbox0 b)
  have hzW : ∀ y ∈ Metric.closedBall z r, y ∈ modesPos V := fun y hy j =>
    (ha j).trans_le (hab y hy j)
  -- `u` on the ball
  have hub : ∀ y ∈ Metric.closedBall z r, ∀ j, |tubeU V B y j| < ρ := by
    intro y hy j
    have hd := abs_sub_le_of_closedBall (G := fun x => tubeU V B x j) (hLu0 j)
      (fun y' hy' => differentiableAt_tubeU hV hBper hB (hzW y' hy') j)
      (fun y' hy' v => abs_fderiv_comp_tubeChart_le (f := fun p => p.1 j) hV hBper
        (fun _ _ _ => rfl) (hzW y' hy') (by fun_prop) (hB _) hN (hAb y' hy') ha (hab y' hy')
        (hβ _) (fun l => abs_fderiv_fst_apply_single_le j l _) (fun b => by
          rw [fderiv_fst_apply_snd]; simp) v) hy
    have := abs_sub_abs_le_abs_sub (tubeU V B y j) (tubeU V B z j)
    linarith [hμ j, hμρ j]
  have hFb : ∀ y ∈ Metric.closedBall z r, ∀ j,
      |f j (tubeChart V B y) - f j (tubeChart V B z)| ≤ δ / 2 := by
    intro y hy j
    have hbox : ∀ y' ∈ Metric.closedBall z r, ∀ l, |(tubeChart V B y').1 l| ≤ ρ :=
      fun y' hy' l => (hub y' hy' l).le
    exact (abs_sub_le_of_closedBall (G := fun x => f j (tubeChart V B x))
      (chartLip_nonneg hN0 hA0 ha hβ0 (hFu0 j) (hFφ0 j))
      (fun y' hy' => differentiableAt_comp_tubeChart hV hBper (hfper j) (hzW y' hy')
        ((hfd j) _) (hB _))
      (fun y' hy' v => abs_fderiv_comp_tubeChart_le hV hBper (hfper j) (hzW y' hy')
        ((hfd j) _) (hB _) hN (hAb y' hy') ha (hab y' hy') (hβ _)
        (hFu j _ _ (hbox y' hy')) (hFφ j _ _ (hbox y' hy')) v) hy).trans (hLF j)
  -- apply the abstract theorem
  refine tube_confinement_observable (W := modesPos V) (K := tubeK V B ρ)
    (Q := Metric.closedBall z r) (F := fun j x => f j (tubeChart V B x))
    (u := fun j x => tubeU V B x j) (c := fun j => f j (tubeChart V B z))
    (ε := fun j => ε j + γ j) (η := η) (δ := δ) (ρ := ρ) (T := T)
    (P := fun x => ∀ j, Pγ j (KAM.Planetary.oscillatorAction x.2 x.1 j))
    hH (isOpen_modesPos V) (isCompact_tubeK hV hBper hB hρ hBmin hBmax) (fun x hx => hx.1)
    (fun x hx hu => ⟨hx, hu⟩)
    (fun j x hx => (differentiableAt_comp_tubeChart hV hBper (hfper j) hx ((hfd j) _)
      (hB _)).differentiableWithinAt)
    (fun j => continuousOn_tubeU hV hBper hB j) ?_ ?_ (fun j => by linarith [hερ j]) hT hTη
    (fun x hx => ⟨hzW x hx, fun j => hFb x hx j, fun j => hub x hx j⟩)
    (fun x hx => oscillatorAction_prop_of_tube hV hG hx) hz₀
  · intro j x hx
    have hbox : ∀ l, |(tubeChart V B x).1 l| ≤ ρ := hx.2
    rw [fderiv_comp_tubeChart_apply_hamiltonianVectorField hV hBper (hfper j) hHh hx.1
      ((hfd j) _) (hhd _ _ hbox) (hB _) (hsym _)]
    exact hη j _ _ hbox
  · intro j x hx
    have hbox : ∀ l, |(tubeChart V B x).1 l| ≤ ρ := hx.2
    have h1 := hface j (tubeChart V B x).1 (tubeChart V B x).2 hbox
    have h2 := hc j
    calc |f j (tubeChart V B x) - f j (tubeChart V B z) - tubeU V B x j|
        = |(f j (tubeChart V B x) - ct j - (tubeChart V B x).1 j) -
            (f j (tubeChart V B z) - ct j)| := by rw [tubeU]; ring_nf
      _ ≤ ε j + γ j := (abs_sub _ _).trans (add_le_add h1 h2)

end KAM.EffectiveStability.Tube

end
