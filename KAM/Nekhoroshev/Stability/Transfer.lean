/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Stability.Conjugation
public import KAM.ODE.Maximal
public import KAM.ODE.Uniqueness
public import KAM.ODE.Continuation
public import KAM.ODE.Exit

/-!
# Transfer of confinement through a change of variables

(`bpN:p7:transfer`, `bpN:p7:stopped-extension`)

* `stopped_extension`: a confinement statement for orbits staying in `W_r` extends to every curve
  solving a field `F` that agrees with the Hamiltonian field on `W_r` (first-exit argument with
  `KAM.ODE.gen_exit`).
* `transfer`: a confinement statement for `H'`-orbits in `W_{r'}` (hypothesis `(T3)`), together with
  the displacement `(T1)` and the surjectivity `(T2)` of `Re Ψ`, gives the confinement statement
  for `H`-orbits (maximal solution, `gen_continuation_periodic`, uniqueness, `conjugation`).

`IsActionNorm`, its two instances and `exit_ball` are in `Stability/Setting`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Stability

open KAM.Weighted KAM.Canonical

variable {n : ℕ}

private theorem isOpen_realStrip' (D : Set (Fin n → ℝ)) (ϱ : ℝ) : IsOpen (realStrip D ϱ) :=
  isOpen_univ.prod (isOpen_realNbhd D ϱ)

section Stopped

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Forward first-exit argument: if on every initial segment of `J` staying in the open set `V`
(as long as `P` holds) the curve stays in the closed set `C ⊆ V`, it never leaves `V` while `P`
holds. -/
private theorem stay_forward {z : ℝ → E} {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J)
    (hz : ContinuousOn z J) {V C : Set E} (hV : IsOpen V) (hC : IsClosed C) (hCV : C ⊆ V)
    (hz0 : z 0 ∈ V) {P : ℝ → Prop} (hP : ∀ t t', 0 ≤ t' → t' ≤ t → P t → P t')
    (hstep : ∀ t ∈ J, 0 ≤ t → P t → (∀ τ ∈ Icc (0 : ℝ) t, z τ ∈ V) →
      ∀ τ ∈ Icc (0 : ℝ) t, z τ ∈ C) :
    ∀ t ∈ J, 0 ≤ t → P t → ∀ τ ∈ Icc (0 : ℝ) t, z τ ∈ V := by
  have key : ∀ t₁ ∈ J, 0 ≤ t₁ → P t₁ → z t₁ ∈ V := by
    intro t₁ ht₁ ht₁0 hPt₁
    by_contra hnot
    have hsub : Icc (0 : ℝ) t₁ ⊆ J := hJ.out h0 ht₁
    have hzc : ContinuousOn z (Icc 0 t₁) := hz.mono hsub
    rcases KAM.ODE.gen_exit (ordConnected_Icc) ⟨le_rfl, ht₁0⟩ hzc hV hz0 with
      ⟨-, hall⟩ | ⟨-, tstar, hleast, hpos, htJ, hIco, -, -⟩
    · exact hnot (hall t₁ ⟨ht₁0, le_rfl⟩ ht₁0)
    · have hnotV : z tstar ∉ V := hleast.1.2.2
      have hts1 : tstar ≤ t₁ := htJ.2
      have hIcoC : ∀ τ ∈ Ico (0 : ℝ) tstar, z τ ∈ C := by
        intro τ hτ
        have hτJ : τ ∈ J := hsub ⟨hτ.1, hτ.2.le.trans hts1⟩
        refine hstep τ hτJ hτ.1 (hP t₁ τ hτ.1 (hτ.2.le.trans hts1) hPt₁) (fun σ hσ => ?_) τ
          ⟨hτ.1, le_rfl⟩
        exact hIco σ ⟨hσ.1, lt_of_le_of_lt hσ.2 hτ.2⟩
      have hcl : tstar ∈ closure (Ico (0 : ℝ) tstar) := by
        rw [closure_Ico hpos.ne]
        exact ⟨hpos.le, le_rfl⟩
      have hcw : ContinuousWithinAt z (Ico 0 tstar) tstar :=
        (hzc tstar htJ).mono (fun τ hτ => ⟨hτ.1, hτ.2.le.trans hts1⟩)
      have hmem := hcw.mem_closure_image hcl
      have hsubC : closure (z '' Ico 0 tstar) ⊆ C :=
        closure_minimal (by rintro _ ⟨τ, hτ, rfl⟩; exact hIcoC τ hτ) hC
      exact hnotV (hCV (hsubC hmem))
  intro t ht ht0 hPt τ hτ
  exact key τ (hJ.out h0 ht ⟨hτ.1, hτ.2⟩) hτ.1 (hP t τ hτ.1 hτ.2 hPt)

end Stopped

/-- `bpN:p7:stopped-extension`. -/
theorem stopped_extension {D : Set (Fin n → ℝ)} {r ϱ : ℝ} {Nrm : (Fin n → ℝ) → ℝ}
    {adm : ℝ → Prop} {H : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} (hN : IsActionNorm Nrm) (hϱ : 0 < ϱ)
    (hϱr : ϱ < r) (hadm : ∀ t t', |t'| ≤ |t| → adm t → adm t')
    (hconf : ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z, IsOrbit H D r J z → (z 0).2 ∈ D →
      ∀ t ∈ J, adm t → Nrm ((z t).2 - (z 0).2) ≤ ϱ)
    {F : (Fin n → ℝ) × (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ)}
    (hF : ∀ x ∈ realStrip D r, F x = KAM.hamiltonianVectorField (realH H) x)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0 : ℝ) ∈ J) {z : ℝ → (Fin n → ℝ) × (Fin n → ℝ)}
    (hz : ∀ t ∈ J, HasDerivAt z (F (z t)) t) (hz0 : (z 0).2 ∈ D) :
    ∀ t ∈ J, adm t → Nrm ((z t).2 - (z 0).2) ≤ ϱ ∧ z t ∈ realStrip D r := by
  set I₀ := (z 0).2 with hI₀
  set V : Set ((Fin n → ℝ) × (Fin n → ℝ)) := realStrip D r with hVdef
  set C : Set ((Fin n → ℝ) × (Fin n → ℝ)) := {x | Nrm (x.2 - I₀) ≤ ϱ} with hCdef
  have hV : IsOpen V := isOpen_realStrip' D r
  have hC : IsClosed C :=
    isClosed_le (hN.continuous.comp (continuous_snd.sub continuous_const)) continuous_const
  have hCV : C ⊆ V := fun x hx =>
    ⟨mem_univ _, I₀, hz0, lt_of_le_of_lt ((hN.norm_le _).trans hx) hϱr⟩
  have hz0V : z 0 ∈ V := ⟨mem_univ _, I₀, hz0, by rw [sub_self, norm_zero]; exact hϱ.trans hϱr⟩
  have hzc : ContinuousOn z J := fun t ht => (hz t ht).continuousAt.continuousWithinAt
  -- orbit property on a segment of `J` inside `V`
  have horb : ∀ a b : ℝ, a ≤ 0 → 0 ≤ b → Icc a b ⊆ J → (∀ τ ∈ Icc a b, z τ ∈ V) →
      ∀ τ ∈ Icc a b, adm τ → Nrm ((z τ).2 - I₀) ≤ ϱ := by
    intro a b ha hb hsub hV' τ hτ hadmτ
    have horbit : IsOrbit H D r (Icc a b) z := fun σ hσ =>
      ⟨hV' σ hσ, by rw [← hF _ (hV' σ hσ)]; exact hz σ (hsub hσ)⟩
    exact hconf (Icc a b) ordConnected_Icc ⟨ha, hb⟩ z horbit hz0 τ hτ hadmτ
  have hadmmono : ∀ t t', |t'| ≤ |t| → adm t → adm t' := hadm
  intro t ht hadmt
  rcases le_total 0 t with hpos | hneg
  · have hstay := stay_forward hJ h0 hzc hV hC hCV hz0V (P := adm)
      (fun t t' h0' h1 => hadmmono t t'
        (by rw [abs_of_nonneg h0', abs_of_nonneg (h0'.trans h1)]; exact h1))
      (fun t' ht' h0' hP' hVt' τ hτ => by
        have hsub : Icc (0 : ℝ) t' ⊆ J := hJ.out h0 ht'
        exact horb 0 t' le_rfl h0' hsub hVt' τ hτ
          (hadmmono t' τ (by rw [abs_of_nonneg hτ.1, abs_of_nonneg h0']; exact hτ.2) hP'))
    have hVall := hstay t ht hpos hadmt
    have hsub : Icc (0 : ℝ) t ⊆ J := hJ.out h0 ht
    exact ⟨horb 0 t le_rfl hpos hsub hVall t ⟨hpos, le_rfl⟩ hadmt, hVall t ⟨hpos, le_rfl⟩⟩
  · have hJ' : (Neg.neg ⁻¹' J).OrdConnected := by
      refine ⟨fun a ha b hb c hc => ?_⟩
      have := hJ.out (x := -b) (y := -a) hb ha
      exact this ⟨by linarith [hc.2], by linarith [hc.1]⟩
    have hz'c : ContinuousOn (fun s => z (-s)) (Neg.neg ⁻¹' J) :=
      hzc.comp continuous_neg.continuousOn (fun s hs => hs)
    have hneg' : ∀ s t' : ℝ, 0 ≤ t' → t' ≤ s → adm (-s) → adm (-t') := fun s t' h0' h1 =>
      hadmmono (-s) (-t')
        (by rw [abs_neg, abs_neg, abs_of_nonneg h0', abs_of_nonneg (h0'.trans h1)]; exact h1)
    have hstay := stay_forward (z := fun s => z (-s)) hJ' (by simpa using h0) hz'c hV hC hCV
      (by simpa using hz0V) (P := fun s => adm (-s)) hneg'
      (fun s hs h0' hP' hVs τ hτ => by
        have hsub : Icc (-s) 0 ⊆ J := by
          intro σ hσ
          have := hJ.out (x := -s) (y := 0) (by simpa using hs) h0
          exact this hσ
        have hmem : ∀ σ ∈ Icc (-s) 0, z σ ∈ V := fun σ hσ => by
          simpa using hVs (-σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
        have := horb (-s) 0 (by linarith) le_rfl hsub hmem (-τ)
          ⟨by linarith [hτ.2], by linarith [hτ.1]⟩ (by simpa using hneg' s τ hτ.1 hτ.2 hP')
        simpa [hCdef] using this)
    have htJ : -t ∈ Neg.neg ⁻¹' J := by simpa using ht
    have hVall := hstay (-t) htJ (by linarith) (by simpa using hadmt)
    have hsub : Icc t 0 ⊆ J := hJ.out ht h0
    have hmem : ∀ σ ∈ Icc t 0, z σ ∈ V := fun σ hσ => by
      simpa using hVall (-σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    exact ⟨horb t 0 hneg le_rfl hsub hmem t ⟨le_rfl, hneg⟩ hadmt, hmem t ⟨le_rfl, hneg⟩⟩

/-- `bpN:p7:transfer`. The time bound `T : D → (0, ∞]` is the predicate `adm I t` ("`|t| ≤ T(I)`"),
which must be symmetric-monotone in `|t|`. -/
theorem transfer {D : Set (Fin n → ℝ)} {r s r' s' d ϱ : ℝ} {Nrm : (Fin n → ℝ) → ℝ}
    {adm : (Fin n → ℝ) → ℝ → Prop} {H H' : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {Ψ : (Fin n → ℂ) × (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hs : 0 < s) (hs' : 0 < s')
    (hN : IsActionNorm Nrm) (hadm : ∀ I t t', |t'| ≤ |t| → adm I t → adm I t')
    (hH : InClass (cpx D) r s H) (hHr : RealOn (Dom n (cpx D) r s) H)
    (hH' : InClass (cpx D) r' s' H') (hH'r : RealOn (Dom n (cpx D) r' s') H')
    (hΨ : DifferentiableOn ℂ Ψ (Dom n (cpx D) r' s'))
    (hΨmap : MapsTo Ψ (Dom n (cpx D) r' s') (Dom n (cpx D) r s))
    (hΨreal : ∀ x : (Fin n → ℝ) × (Fin n → ℝ), KAM.realInclusion₂ n x ∈ Dom n (cpx D) r' s' →
      Ψ (KAM.realInclusion₂ n x) ∈ range (KAM.realInclusion₂ n))
    (hΨsympl : ∀ z ∈ Dom n (cpx D) r' s', ∀ v w,
      symplFormC (fderiv ℂ Ψ z v) (fderiv ℂ Ψ z w) = symplFormC v w)
    (hconj : ∀ z ∈ Dom n (cpx D) r' s', H' z = H (Ψ z))
    -- (T1)
    (hT1 : ∀ x ∈ realStrip D r', Nrm ((reMap Ψ x).2 - x.2) ≤ d)
    -- (T2)
    (hT2 : ∀ y : (Fin n → ℝ) × (Fin n → ℝ), y.2 ∈ D → ∃ x ∈ realStrip D r', reMap Ψ x = y)
    -- (T3)
    (hϱ : 0 < ϱ) (hdϱ : d + ϱ < r')
    (hT3 : ∀ Iy ∈ D, ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z', IsOrbit H' D r' J z' →
      Nrm ((z' 0).2 - Iy) ≤ d → ∀ t ∈ J, adm Iy t → Nrm ((z' t).2 - (z' 0).2) ≤ ϱ) :
    ∀ J : Set ℝ, J.OrdConnected → (0 : ℝ) ∈ J → ∀ z, IsOrbit H D r J z → (z 0).2 ∈ D →
      ∀ t ∈ J, adm (z 0).2 t → Nrm ((z t).2 - (z 0).2) ≤ ϱ + 2 * d := by
  intro J hJ h0 z hz hzD t ht hadmt
  have hsys := real_system hs hH hHr
  have hsys' := real_system hs' hH' hH'r
  have hW : IsOpen (realStrip D r) := isOpen_realStrip' D r
  have hW' : IsOpen (realStrip D r') := isOpen_realStrip' D r'
  set Iy := (z 0).2 with hIy
  obtain ⟨x, hxW, hxy⟩ := hT2 (z 0) hzD
  have hd1 : Nrm ((z 0).2 - x.2) ≤ d := by simpa [hxy] using hT1 x hxW
  have hd2 : Nrm (x.2 - Iy) ≤ d := by
    have := hN.neg ((z 0).2 - x.2)
    rw [neg_sub] at this
    rw [hIy, this]; exact hd1
  obtain ⟨⟨Tm, Tp, z', hmax⟩, -⟩ := KAM.ODE.gen_maximal hW' hsys'.2.2.2.1 hxW
  have hz' : IsOrbit H' D r' (KAM.ODE.eIoo Tm Tp) z' := hmax.isSolution
  have hz'0 : z' 0 = x := hmax.init
  have h0m : (0 : ℝ) ∈ KAM.ODE.eIoo Tm Tp := KAM.ODE.zero_mem_eIoo hmax
  have hbd : ∀ σ ∈ KAM.ODE.eIoo Tm Tp, adm Iy σ → Nrm ((z' σ).2 - x.2) ≤ ϱ := fun σ hσ hσa => by
    have := hT3 Iy hzD (KAM.ODE.eIoo Tm Tp) (KAM.ODE.ordConnected_eIoo _ _) h0m z' hz'
      (by rw [hz'0]; exact hd2) σ hσ hσa
    rwa [hz'0] at this
  -- the compact set
  set K : Set (Fin n → ℝ) := {I | Nrm (I - x.2) ≤ ϱ} with hKdef
  have hKc : IsClosed K :=
    isClosed_le (hN.continuous.comp (continuous_id.sub continuous_const)) continuous_const
  have hK : IsCompact K := by
    refine (isCompact_closedBall x.2 ϱ).of_isClosed_subset hKc fun I hI => ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (hN.norm_le _).trans hI
  have hKU : K ⊆ realNbhd D r' := fun I hI => by
    refine ⟨Iy, hzD, ?_⟩
    have h1 : ‖I - Iy‖ ≤ ‖I - x.2‖ + ‖x.2 - Iy‖ := by
      calc ‖I - Iy‖ = ‖(I - x.2) + (x.2 - Iy)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have h2 : ‖I - x.2‖ ≤ ϱ := (hN.norm_le _).trans hI
    have h3 : ‖x.2 - Iy‖ ≤ d := (hN.norm_le _).trans hd2
    linarith
  have hcont := KAM.ODE.gen_continuation_periodic (isOpen_realNbhd D r') hsys'.2.2.2.1
    hsys'.2.2.2.2.1 hmax hK hKU
  -- the time `t` lies in the maximal interval
  have hTin : t ∈ KAM.ODE.eIoo Tm Tp := by
    rcases lt_trichotomy t 0 with hlt | heq | hgt
    · refine ⟨?_, lt_of_lt_of_le (by exact_mod_cast hlt) hmax.pos_lt.le⟩
      by_contra hnot
      rw [not_lt] at hnot
      have hbot := hcont.2 ⟨0, le_rfl, hmax.neg_lt, fun σ hσTm hσ0 => by
        have hσm : σ ∈ KAM.ODE.eIoo Tm Tp :=
          ⟨hσTm, lt_of_le_of_lt (by exact_mod_cast hσ0) hmax.pos_lt⟩
        have htσ : t ≤ σ := by
          have := EReal.coe_le_coe_iff.1 (hnot.trans hσTm.le)
          exact this
        exact hbd σ hσm (hadm Iy t σ (by rw [abs_of_nonpos hσ0, abs_of_neg hlt]; linarith) hadmt)⟩
      rw [hbot] at hnot
      exact absurd hnot (by simp)
    · subst heq
      exact h0m
    · refine ⟨lt_of_le_of_lt hmax.neg_lt.le (by exact_mod_cast hgt), ?_⟩
      by_contra hnot
      rw [not_lt] at hnot
      have htop := hcont.1 ⟨0, le_rfl, hmax.pos_lt, fun σ hσ0 hσTp => by
        have hσm : σ ∈ KAM.ODE.eIoo Tm Tp :=
          ⟨lt_of_lt_of_le hmax.neg_lt (by exact_mod_cast hσ0), hσTp⟩
        have hσt : σ ≤ t := EReal.coe_le_coe_iff.1 (hσTp.le.trans hnot)
        exact hbd σ hσm (hadm Iy t σ (by rw [abs_of_nonneg hσ0, abs_of_pos hgt]; exact hσt) hadmt)⟩
      rw [htop] at hnot
      exact absurd hnot (by simp)
  -- uniqueness of the `H`-orbit
  have hconjo := conjugation hs hs' hH hHr hH' hH'r hΨ hΨmap hΨreal hΨsympl hconj hz'
  have heq := KAM.ODE.gen_uniqueness_inter hW hsys.2.2.2.1 hJ (KAM.ODE.ordConnected_eIoo Tm Tp)
    (t₀ := 0) ⟨h0, h0m⟩ hz hconjo (by rw [hz'0, hxy]) ⟨ht, hTin⟩
  have ht1 := hT1 (z' t) (hz' t hTin).1
  have ht2 := hbd t hTin hadmt
  have hsplit : (z t).2 - (z 0).2 =
      (((z t).2 - (z' t).2) + ((z' t).2 - x.2)) + -((z 0).2 - x.2) := by abel
  have hzt : (z t).2 - (z' t).2 = (reMap Ψ (z' t)).2 - (z' t).2 := by rw [heq]
  rw [hsplit]
  calc Nrm ((((z t).2 - (z' t).2) + ((z' t).2 - x.2)) + -((z 0).2 - x.2))
      ≤ Nrm (((z t).2 - (z' t).2) + ((z' t).2 - x.2)) + Nrm (-((z 0).2 - x.2)) := hN.add_le _ _
    _ ≤ (Nrm ((z t).2 - (z' t).2) + Nrm ((z' t).2 - x.2)) + Nrm (-((z 0).2 - x.2)) := by
        gcongr; exact hN.add_le _ _
    _ ≤ (d + ϱ) + d := by
        rw [hN.neg, hzt]
        gcongr
    _ = ϱ + 2 * d := by ring

end KAM.Stability

end
