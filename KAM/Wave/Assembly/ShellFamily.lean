/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.ShellClose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W8: invariance and continuity on one shell, patched continuity, family injectivity
(blueprint `bpW:w8:shell-inv`, `bpW:w8:patch-cont`, `bpW:w8:injective`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint labels `bpW:w8:shell-inv`, `bpW:w8:patch`, `bpW:w8:patch-cont`,
`bpW:w8:injective` (milestone W8).

For the source family `w8HF hm = (w8HW hm n)_n` (initial perturbation of `bpW:w5:initial` on every
shell), with `Γ = w8GammaW (w8HF hm)`, `ν = w8NuW (w8HF hm)`, `K = w8KW w8AA (w8HF hm)`:
* `w8_shellInv` (Lemma `bpW:w8:shell-inv` (i)): clause (4) of `nlw2` for `K^{(n)}_ξ` and
  `ν^{(n)}_*(ξ)`, from `bpW:w6:tori` (iii) via W8-ASM's `w8_shellInv_of_birk` (W3
  `bpW:w3:transport-tori-weak`);
* `w8_shellInvCont` (Lemma `bpW:w8:shell-inv` (ii)): `(ξ, θ) ↦ K^{(n)}_ξ(θ)` is continuous on
  `Γ_n × ℝ²`;
* `w8_patchContK` (Lemma `bpW:w8:patch-cont`, Step `stepW:w8:pc-K`);
* `w8_patchEmb`, `w8_patchInv`: clauses (3) (embedding) and (4) for the patched `K`, `ν`;
* **`w8_injective`** (Proposition `bpW:w8:injective`): clause (6) of `nlw2`.
-/

@[expose] public noncomputable section

open Set Real Complex

namespace KAM.Wave

open KAM

local macro "w8tori" hm:term:max n:term:max : term =>
  `((w8HW $hm $n).w6Tori (w8_toriData $hm $n).1 (w8_toriData $hm $n).2.1
    (w8_toriData $hm $n).2.2.1 (w8_toriData $hm $n).2.2.2.1 (w8_toriData $hm $n).2.2.2.2)

/-- `ι_{p → p-1} ι_{p+1 → p} = ι_{p+1 → p-1}` on `𝔚` (`a = p = 1`). -/
theorem w8_birkEmbed_comp (y : BirkSpace) :
    birkEmbed 1 1 (1 - 1) (by norm_num) (birkEmbed 1 (1 + 1) 1 (by norm_num) y) =
      birkEmbed 1 (1 + 1) (1 - 1) (by norm_num) y := by
  ext l
  have hr : ellWeight 1 (1 - 1) l.2 / ellWeight 1 1 l.2 *
      (ellWeight 1 1 l.2 / ellWeight 1 (1 + 1) l.2) =
      ellWeight 1 (1 - 1) l.2 / ellWeight 1 (1 + 1) l.2 :=
    div_mul_div_cancel₀ (ellWeight_pos 1 1 l.2).ne'
  simp only [birkEmbed_apply, embedRatio]
  rw [← mul_assoc, ← RCLike.ofReal_mul, hr]

variable {m : ℝ} (hm : 0 < m)

local notation "𝔱" => w8T0W m hm

/-- The source family of shell bundles. -/
abbrev w8HF : ∀ n, W8ShellPrep m hm n (w6InP m hm) (w6InX m hm) := fun n => w8HW hm n

/-- `ν^{(n)}_* = ω^{(n)}_*/(2π)` is W6's `ν_*` of the shell iteration. -/
theorem w8ShellNu_eq (n : ℕ) (ξ : Fin 2 → ℝ) :
    w8ShellNu (w8HW hm n) ξ = (w8HW hm n).w6NuStar (w8Eps0W m hm n) ξ := by
  funext i
  show (2 * π)⁻¹ * w8ShellOmega (w8HW hm n) ξ i = _ / (2 * π)
  rw [div_eq_inv_mul]
  rfl

/-- **Invariance on one shell** (blueprint `bpW:w8:shell-inv` (i)): for `ξ ∈ Γ_n`, real `θ`,
`j ≥ 1`, with `K = K^{(n)}_ξ` and `ν = ν^{(n)}_*(ξ)`, the two `HasDerivAt` statements of clause (4)
of `nlw2` hold. -/
theorem w8_shellInv (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n))
    (θ : Fin 2 → ℝ) (j : ℕ+) :
    HasDerivAt (fun t : ℝ => coeff (w8Kshell w8AA (w8HW hm n) ξ
        (θ + t • w8ShellNu (w8HW hm n) ξ)).1 j)
      (lam m hm j * coeff (w8Kshell w8AA (w8HW hm n) ξ θ).2 j) 0 ∧
    HasDerivAt (fun t : ℝ => coeff (w8Kshell w8AA (w8HW hm n) ξ
        (θ + t • w8ShellNu (w8HW hm n) ξ)).2 j)
      (-(lam m hm j * coeff (w8Kshell w8AA (w8HW hm n) ξ θ).1 j) -
        cubicGrad m hm (w8Kshell w8AA (w8HW hm n) ξ θ).1 j) 0 := by
  set H := w8HW hm n
  set ν := w8ShellNu H ξ
  obtain ⟨hd, -, -, -, -⟩ := (w8tori hm n).1 ξ hξ
  have hinv := (w8tori hm n).2.2.2.1 ξ hξ
  set D : (Fin 2 → ℝ) → BirkSpace := fun θ' =>
    fderiv ℂ (fun z => H.w6TorusBk (w8Eps0W m hm n) z ξ) (aaOfReal θ') (aaOfReal ν)
  have hder : ∀ θ' : Fin 2 → ℝ, HasDerivAt (fun t : ℝ => w8Psi hm n ξ (θ' + t • ν)) (D θ') 0 :=
      fun θ' => by
    have hz := w6_real_mem_strip_half θ'
    have hFd := ((hd.differentiableAt ((isOpen_complexStrip 2 _).mem_nhds hz)).hasFDerivAt)
    have hlC : HasDerivAt (fun s : ℝ => aaOfReal (θ' + s • ν)) (aaOfReal ν) 0 := by
      refine hasDerivAt_pi.2 fun i => ?_
      have := (((hasDerivAt_id (0 : ℝ)).mul_const (ν i)).const_add (θ' i)).ofReal_comp
      simpa [aaOfReal, mul_comm] using this
    exact (hFd.restrictScalars ℝ).comp_hasDerivAt_of_eq (x := (0 : ℝ)) hlC (by simp)
  have heq : ∀ θ', birkEmbed 1 1 (1 - 1) (by linarith) (D θ') =
      birkXLam m hm (w8Psi hm n ξ θ') + birkEmbed 1 1 (1 - 1) (by linarith)
        (birkRestField m hm zero_le_one (by norm_num : (1 / 2 : ℝ) ≤ 1)
          ⟨w8Psi hm n ξ θ', (w8Psi_ball hm n hξ θ').2.2.2.1⟩) := fun θ' => by
    have h := hinv θ' (w8Psi_ball hm n hξ θ').2.2.2.1
    rw [← w8ShellNu_eq] at h
    refine h.trans ?_
    congr 1
    show _ = birkEmbed 1 1 (1 - 1) _ (birkEmbed 1 (1 + 1) 1 _ _ + birkEmbed 1 (1 + 1) 1 _ _ +
      birkEmbed 1 (1 + 1) 1 _ _)
    rw [← map_add, ← map_add, w8_birkEmbed_comp]
    rfl
  rw [w8Kshell_eq]
  exact w8_shellInv_of_birk ν (w8Psi hm n ξ) D (fun θ' => (w8Psi_ball hm n hξ θ').2.2.2.2.1)
    (fun θ' => (w8Psi_ball hm n hξ θ').2.2.2.1) (fun θ' => (w8Psi_ball hm n hξ θ').2.2.2.2.2.1)
    hder heq θ j

/-- **Continuity on one shell** (blueprint `bpW:w8:shell-inv` (ii)): `(ξ, θ) ↦ K^{(n)}_ξ(θ)` is
continuous on `Γ_n × ℝ²`. -/
theorem w8_shellInvCont (n : ℕ) :
    ContinuousOn (Function.uncurry (w8Kshell w8AA (w8HW hm n)))
      (w8ShellGamma (w8HW hm n) ×ˢ univ) :=
  w8_shellInvCont_of_birk (Ψ := fun ξ θ => w8Psi hm n ξ θ) ((w8tori hm n).2.1)
    (fun _ hξ θ => (w8Psi_ball hm n hξ θ).2.2.2.2.1)
    (fun _ hξ θ => (w8Psi_ball hm n hξ θ).2.2.2.1)
    (fun _ hξ θ => (w8Psi_ball hm n hξ θ).2.2.2.2.2.1)

/-- **Continuity of the patched `K`** (blueprint `bpW:w8:patch-cont`, Step `stepW:w8:pc-K`). -/
theorem w8_patchContK :
    ContinuousOn (Function.uncurry (w8KW w8AA (w8HF hm))) (w8GammaW (w8HF hm) ×ˢ univ) :=
  w8_patchContK_of_pieces (w8HF hm) fun n => w8_shellInvCont hm n

/-- For `I ∈ Γ_n`: `K_I = K^{(n)}_I` and `ν(I) = ν^{(n)}_*(I)` (Lemma `bpW:w8:patch-local`). -/
theorem w8_patch_of_mem {n : ℕ} {I : Fin 2 → ℝ} (hI : I ∈ w8Gammas (w8HF hm) n) :
    w8KW w8AA (w8HF hm) I = w8Kshell w8AA (w8HW hm n) I ∧
      w8NuW (w8HF hm) I = w8ShellNu (w8HW hm n) I := by
  obtain ⟨-, -, -, -, h⟩ := w8_patchLocal (w8HF hm) (fun n => w8Kshell w8AA (w8HW hm n))
  obtain ⟨-, h1, h2⟩ := h n I hI
  exact ⟨h2, h1⟩

/-- Clause (3), embedding (blueprint `bpW:w8:nlw2-proof`, Step `stepW:w8:p-emb`). -/
theorem w8_patchEmb :
    ∀ I ∈ w8GammaW (w8HF hm), IsAnalyticTorusEmbedding (w8KW w8AA (w8HF hm) I) := by
  intro I hI
  obtain ⟨n, hn⟩ := mem_iUnion.1 hI
  rw [(w8_patch_of_mem hm hn).1]
  exact w8_shellEmbedding hm n hn

/-- Clause (4) for the patched family (blueprint `bpW:w8:nlw2-proof`, Step `stepW:w8:p-inv`). -/
theorem w8_patchInv : ∀ I ∈ w8GammaW (w8HF hm), ∀ (θ : Fin 2 → ℝ) (j : ℕ+),
    HasDerivAt (fun t : ℝ => coeff (w8KW w8AA (w8HF hm) I (θ + t • w8NuW (w8HF hm) I)).1 j)
      (lam m hm j * coeff (w8KW w8AA (w8HF hm) I θ).2 j) 0 ∧
    HasDerivAt (fun t : ℝ => coeff (w8KW w8AA (w8HF hm) I (θ + t • w8NuW (w8HF hm) I)).2 j)
      (-(lam m hm j * coeff (w8KW w8AA (w8HF hm) I θ).1 j) -
        cubicGrad m hm (w8KW w8AA (w8HF hm) I θ).1 j) 0 := by
  intro I hI θ j
  obtain ⟨n, hn⟩ := mem_iUnion.1 hI
  rw [(w8_patch_of_mem hm hn).1, (w8_patch_of_mem hm hn).2]
  exact w8_shellInv hm n hn θ j

theorem w8TK_continuous_real (n : ℕ) {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm n)) :
    Continuous fun θ : Fin 2 → ℝ => w8TK hm n (aaOfReal θ) ξ := by
  have hc : Continuous aaOfReal := by unfold aaOfReal; fun_prop
  refine continuous_iff_continuousAt.2 fun θ => ?_
  have hz := w6_real_mem_strip_half θ
  exact ((w8TK_differentiableOn hm n hξ).differentiableAt
    ((isOpen_complexStrip 2 _).mem_nhds hz)).continuousAt.comp hc.continuousAt

/-- Step `stepW:w8:in-freq` of `bpW:w8:injective`: two shell tori carrying the same orbit have the
same frequency (Lemma `bpW:w8:winding`, via `bpW:w8:torus-shape` (i), (ii)). -/
theorem w8_shell_freq_eq {n n' : ℕ} {I I' : Fin 2 → ℝ} (hI : I ∈ w8ShellGamma (w8HW hm n))
    (hI' : I' ∈ w8ShellGamma (w8HW hm n')) {ν ν' θ θ' : Fin 2 → ℝ}
    (horb : ∀ t : ℝ, w8Psi hm n I (θ + t • ν) = w8Psi hm n' I' (θ' + t • ν')) : ν = ν' := by
  have hcont : ∀ {k : ℕ} {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm k)),
      Continuous (w8Yact hm k ξ) ∧ Continuous (w8Xang hm k ξ) := fun {k ξ} hξ => by
    have hT := w8TK_continuous_real hm k hξ
    refine ⟨continuous_pi fun i => ?_, (continuous_pi fun i => ?_).sub continuous_id⟩
    · exact Complex.continuous_re.comp ((continuous_apply i).comp
        (continuous_fst.comp (continuous_snd.comp hT)))
    · exact Complex.continuous_re.comp ((continuous_apply i).comp (continuous_fst.comp hT))
  have ha : ∀ {k : ℕ} {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm k)),
      Continuous fun θ : Fin 2 → ℝ => fun i => Real.sqrt (ξ i + w8Yact hm k ξ θ i) :=
    fun hξ => continuous_pi fun i => Real.continuous_sqrt.comp
      (continuous_const.add ((continuous_apply i).comp (hcont hξ).1))
  have hXb : ∀ {k : ℕ} {ξ : Fin 2 → ℝ} (hξ : ξ ∈ w8ShellGamma (w8HW hm k)),
      ∃ B, ∀ θ i, |w8Xang hm k ξ θ i| ≤ B := fun {k ξ} hξ =>
    ⟨w8ShellEtor m hm k, fun θ i =>
      (norm_le_pi_norm (w8Xang hm k ξ θ) i).trans (w8_torusShape_bounds hm k hξ θ).1⟩
  exact w8_freq_eq_of_shape (fun i w => birkCoord 1 1 w (true, modeIdx i)) (ha hI) (ha hI')
    (hcont hI).2 (hcont hI').2 (fun θ i => w8_sqrt_pos hm n hI θ i)
    (fun θ i => w8_sqrt_pos hm n' hI' θ i) (hXb hI) (hXb hI')
    (fun θ i => w8_coord_true hm n hI θ i) (fun θ i => w8_coord_true hm n' hI' θ i) horb

/-- **Family injectivity** (blueprint `bpW:w8:injective`): for `I, I' ∈ Γ` and real `θ, θ'`,
`K_I(θ) = K_{I'}(θ')` implies `I = I'` and `θ - θ' ∈ ℤ²`. This is clause (6) of `nlw2`. -/
theorem w8_injective :
    ∀ I ∈ w8GammaW (w8HF hm), ∀ I' ∈ w8GammaW (w8HF hm), ∀ θ θ' : Fin 2 → ℝ,
      w8KW w8AA (w8HF hm) I θ = w8KW w8AA (w8HF hm) I' θ' →
        I = I' ∧ ∃ k : Fin 2 → ℤ, θ - θ' = fun i => (k i : ℝ) := by
  refine w8_injective_of_pieces hm (w8_patchEmb hm) (w8_patchInv hm) ?_ (w8_nuInjective _)
  intro I hI I' hI' θ θ' horb
  obtain ⟨n, hn⟩ := mem_iUnion.1 hI
  obtain ⟨n', hn'⟩ := mem_iUnion.1 hI'
  obtain ⟨hK, hν⟩ := w8_patch_of_mem hm hn
  obtain ⟨hK', hν'⟩ := w8_patch_of_mem hm hn'
  rw [hK, hK', hν, hν'] at horb
  rw [hν, hν']
  refine w8_shell_freq_eq hm hn hn' (θ := θ) (θ' := θ') fun t => ?_
  have h := horb t
  rw [w8Kshell_eq, w8Kshell_eq] at h
  obtain ⟨-, -, -, -, -, hb, hr⟩ := w8Psi_ball hm n hn (θ + t • w8ShellNu (w8HW hm n) I)
  obtain ⟨-, -, -, -, -, hb', hr'⟩ := w8Psi_ball hm n' hn' (θ' + t • w8ShellNu (w8HW hm n') I')
  exact w8KOfBirk_eq_of_eq hb hb' hr hr' h

end KAM.Wave

end
