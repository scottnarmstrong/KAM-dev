/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.FreqShell
public import KAM.Wave.Assembly.NuInj
public import KAM.Wave.Birkhoff.MainBallReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# W8: shell embeddings, the patched family, its regularity and frequency injectivity
(blueprint `bpW:w8:Kshell`, `bpW:w8:patch`, `bpW:w8:patch-local`, `bpW:w8:patch-cont`,
`bpW:w8:nu-injective`)

Blueprint labels `bpW:w8:Kshell`, `bpW:w8:patch`, `bpW:w8:patch-local`,
`bpW:w8:patch-cont`, `bpW:w8:nu-injective` (milestone W8).

The shell data are a family `H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)` of prep-step bundles
(for the source, `Ps n` is the initial perturbation of `bpW:w5:initial` for shell `n`,
`w8ShellPrep_of_initial`). Then `Γ_n = w8ShellGamma (H n)`, `ν^{(n)}_* = w8ShellNu (H n)`, and:

* `w8GammaW H = Γ = ⋃ Γ_n`, `w8NuW H = ν` (W8-PREP's `w8PatchSet`, `w8PatchNu`, Definition
  `bpW:w8:patch`); `w8_patchLocal` (Lemma `bpW:w8:patch-local`);
* `w8_patchCont` (Lemma `bpW:w8:patch-cont`, parts not involving `K`): `Γ` Borel,
  `Γ ⊆ {I | (∀ i, 0 < I_i) ∧ r(I) < r₀}`, `ν` continuous on `Γ`;
* `w8_nuInjective` (Lemma `bpW:w8:nu-injective`): `ν` is injective on `Γ`;
* `bpW:w8:Kshell`: `w8KOfBirk m hm Ψ θ = Γ^ℝ(𝒵⁻¹Ψ(θ))` for a torus `Ψ` in Birkhoff coordinates
  (W3's `birkGammaR`; the transport `τ_E` is the identity, since W3's `BirkReal` and the frozen
  `WaveSpace` are the same weighted `E_{1,1}`; `𝒵⁻¹` on real points is W3's `birkPi`; totalized by
  `0` off `B^E_{r₁}`), and `w8Kshell A H ξ θ = K^{(n)}_ξ(θ)` with
  `Ψ̃^{(n)}_ξ = 𝒜_ξ ∘ Φ_P ∘ Φ_*` for an action–angle map `A` (W5's `𝒜_ξ` of
  `bpW:w5:action-angle`, a parameter here: it is not in this base). `w8KW A H` is the
  patched `K`; its continuity on `Γ × ℝ²` is
  `w8_patchContK_of_pieces` (hypothesis-taking variant: per shell it is `bpW:w8:shell-inv` (ii),
  which needs `𝒜_ξ`).
-/

@[expose] public noncomputable section

open Set Real

namespace KAM.Wave

/-! ### Shell embeddings (`bpW:w8:Kshell`) -/

/-- `K(θ) = τ_E Γ^ℝ(𝒵⁻¹ Ψ(θ))` for a torus `Ψ : ℝ² → 𝔚` in Birkhoff coordinates (`τ_E = id` in
weighted coordinates; `𝒵⁻¹` of a real point is `birkPi`); `0` where `𝒵⁻¹Ψ(θ) ∉ B^E_{r₁}`
(blueprint `bpW:w8:Kshell`). -/
def w8KOfBirk (m : ℝ) (hm : 0 < m) (Ψ : (Fin 2 → ℝ) → BirkSpace) (θ : Fin 2 → ℝ) : WaveSpace := by
  classical
  exact if h : birkPi (Ψ θ) ∈ birkRealBall1 m 1 then
    birkGammaR m hm zero_le_one (by norm_num) ⟨birkPi (Ψ θ), h⟩ else 0

/-- `w8KOfBirk` is `Γ^ℝ(𝒵⁻¹Ψ(θ))` on `B^E_{r₁}`. -/
theorem w8KOfBirk_of_mem {m : ℝ} {hm : 0 < m} {Ψ : (Fin 2 → ℝ) → BirkSpace} {θ : Fin 2 → ℝ}
    (h : birkPi (Ψ θ) ∈ birkRealBall1 m 1) :
    w8KOfBirk m hm Ψ θ = birkGammaR m hm zero_le_one (by norm_num) ⟨birkPi (Ψ θ), h⟩ := by
  unfold w8KOfBirk; simp only [h, ↓reduceDIte]

/-- Step `stepW:w8:se-per` (blueprint `bpW:w8:shell-embedding`): a periodic Birkhoff torus gives a
periodic `K`. -/
theorem w8KOfBirk_periodic {m : ℝ} {hm : 0 < m} {Ψ : (Fin 2 → ℝ) → BirkSpace}
    {θ : Fin 2 → ℝ} {k : Fin 2 → ℤ} (h : Ψ (θ + fun i => (k i : ℝ)) = Ψ θ) :
    w8KOfBirk m hm Ψ (θ + fun i => (k i : ℝ)) = w8KOfBirk m hm Ψ θ := by
  unfold w8KOfBirk; rw [h]

/-- **Shell embeddings** (blueprint `bpW:w8:Kshell`): `K^{(n)}_ξ(θ) = τ_E Γ^ℝ(𝒵⁻¹ Ψ̃^{(n)}_ξ(θ))`,
`Ψ̃^{(n)}_ξ(θ) = 𝒜_ξ(Φ^{(n)}_P(Φ^{(n)}_*(θ)))`, for the action–angle map `A ξ = 𝒜_ξ` (parameter;
W5's `bpW:w5:action-angle`). -/
def w8Kshell {m : ℝ} {hm : 0 < m} {n : ℕ} {P : (Fin 2 → ℝ) → KamPhase → ℂ}
    {X : (Fin 2 → ℝ) → KamPhase → KamPhase} (A : (Fin 2 → ℝ) → KamPhase → BirkSpace)
    (H : W8ShellPrep m hm n P X) (ξ θ : Fin 2 → ℝ) : WaveSpace :=
  w8KOfBirk m hm (fun θ' => A ξ (w8ShellTorusKam H (fun i => (θ' i : ℂ)) ξ)) θ

/-! ### The patched family (`bpW:w8:patch`, `bpW:w8:patch-local`, `bpW:w8:patch-cont`,
`bpW:w8:nu-injective`) -/

variable {m : ℝ} {hm : 0 < m} {Ps : ℕ → (Fin 2 → ℝ) → KamPhase → ℂ}
  {Xs : ℕ → (Fin 2 → ℝ) → KamPhase → KamPhase}

local notation "𝔱" => w8T0W m hm

/-- The pieces `Γ_n` of the shell iterations. -/
def w8Gammas (H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)) : ℕ → Set (Fin 2 → ℝ) :=
  fun n => w8ShellGamma (H n)

/-- The pieces `ν^{(n)}_*` of the shell iterations. -/
def w8Nus (H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)) : ℕ → (Fin 2 → ℝ) → Fin 2 → ℝ :=
  fun n => w8ShellNu (H n)

/-- `Γ = ⋃_n Γ_n` (blueprint `bpW:w8:patch`). -/
def w8GammaW (H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)) : Set (Fin 2 → ℝ) :=
  w8PatchSet (w8Gammas H)

/-- The patched frequency map `ν` (blueprint `bpW:w8:patch`). -/
def w8NuW (H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)) : (Fin 2 → ℝ) → Fin 2 → ℝ :=
  w8PatchNu 𝔱 (w8Gammas H) (w8Nus H)

/-- The patched embeddings `K` (blueprint `bpW:w8:patch`), for the action–angle map `A`. -/
def w8KW (A : (Fin 2 → ℝ) → KamPhase → BirkSpace) (H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)) :
    (Fin 2 → ℝ) → (Fin 2 → ℝ) → WaveSpace :=
  w8PatchK 𝔱 (w8Gammas H) fun n => w8Kshell A (H n)

theorem w8Gammas_subset (H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)) (n : ℕ) :
    w8Gammas H n ⊆ w8Pi 𝔱 n :=
  w8ShellGamma_subset_Pi (H n)

/-- `(2π) ν^{(n)}_* = ω^{(n)}_*`. -/
theorem w8ShellNu_smul {n : ℕ} {P : (Fin 2 → ℝ) → KamPhase → ℂ}
    {X : (Fin 2 → ℝ) → KamPhase → KamPhase} (H : W8ShellPrep m hm n P X) (ξ : Fin 2 → ℝ) :
    (2 * π) • w8ShellNu H ξ = w8ShellOmega H ξ := by
  unfold w8ShellNu
  rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

/-- **Locality of the patching** (blueprint `bpW:w8:patch-local`) for the shell iterations: the
`O_n = Π_n` are open and pairwise disjoint, `Γ_n ⊆ O_n`, `Γ ∩ O_n = Γ_n`, and for `I ∈ Γ_n`:
`n(I) = n`, `ν(I) = ν^{(n)}_*(I)`, `K_I = K^{(n)}_I`. -/
theorem w8_patchLocal (H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)) {E : Type*} [Zero E]
    (Ks : ℕ → (Fin 2 → ℝ) → (Fin 2 → ℝ) → E) :
    (∀ n, IsOpen (w8Pi 𝔱 n)) ∧ (∀ n n', n ≠ n' → Disjoint (w8Pi 𝔱 n) (w8Pi 𝔱 n')) ∧
      (∀ n, w8Gammas H n ⊆ w8Pi 𝔱 n) ∧ (∀ n, w8GammaW H ∩ w8Pi 𝔱 n = w8Gammas H n) ∧
      ∀ n, ∀ I ∈ w8Gammas H n, w8ShellIdx 𝔱 I = n ∧ w8NuW H I = w8Nus H n I ∧
        w8PatchK 𝔱 (w8Gammas H) Ks I = Ks n I :=
  w8Patch_local (w8Gammas_subset H) (w8T0_pos hm _) (w8Nus H) Ks

/-- **Regularity of the patched family** (blueprint `bpW:w8:patch-cont`, Steps
`stepW:w8:pc-borel`, `stepW:w8:pc-incl`, `stepW:w8:pc-nu`): `Γ` is Borel,
`Γ ⊆ {I | (∀ i, 0 < I_i) ∧ r(I) < r₀}`, and `ν` is continuous on `Γ`. The continuity of `K` on
`Γ × ℝ²` (Step `stepW:w8:pc-K`) is `w8_patchContK_of_pieces`. -/
theorem w8_patchCont (H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)) :
    MeasurableSet (w8GammaW H) ∧
      w8GammaW H ⊆ {I | (∀ i, 0 < I i) ∧ Real.sqrt (I 0 + I 1) < w8R0 m hm (w8Upstream m hm)} ∧
      ContinuousOn (w8NuW H) (w8GammaW H) :=
  ⟨measurableSet_w8PatchSet_of_pieces fun n => (w8_freqShell (H n)).2.2.2.2.2,
    w8PatchSet_subset (w8Gammas_subset H) (w8T0_pos hm _),
    continuousOn_w8PatchNu_of_pieces (w8Gammas_subset H) (w8T0_pos hm _) fun n =>
      (w8_freqShell (H n)).2.2.2.2.1⟩

/-- Step `stepW:w8:pc-K` of `bpW:w8:patch-cont` for the shell iterations
(hypothesis-taking variant: the hypothesis is `bpW:w8:shell-inv` (ii) for every shell, which
needs W5's `bpW:w5:action-angle`). -/
theorem w8_patchContK_of_pieces (H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)) {E : Type*} [Zero E]
    [TopologicalSpace E] {Ks : ℕ → (Fin 2 → ℝ) → (Fin 2 → ℝ) → E}
    (hK : ∀ n, ContinuousOn (Function.uncurry (Ks n)) (w8Gammas H n ×ˢ univ)) :
    ContinuousOn (Function.uncurry (w8PatchK 𝔱 (w8Gammas H) Ks)) (w8GammaW H ×ˢ univ) :=
  continuousOn_w8PatchK_of_pieces (w8Gammas_subset H) (w8T0_pos hm _) hK

/-- **The frequency map is injective on `Γ`** (blueprint `bpW:w8:nu-injective`): if `I, I' ∈ Γ` and
`ν(I) = ν(I')`, then `I = I'`. -/
theorem w8_nuInjective (H : ∀ n, W8ShellPrep m hm n (Ps n) (Xs n)) :
    InjOn (w8NuW H) (w8GammaW H) := by
  refine w8PatchNu_injOn_of_pieces hm (w8T0_pos hm _) (w8Gammas_subset H) (fun n ξ hξ ξ' hξ' => ?_)
    fun n ξ hξ => ?_
  · show 7 / (8 * measLA m hm) * ‖ξ - ξ'‖ ≤
      ‖(2 * π) • w8ShellNu (H n) ξ - (2 * π) • w8ShellNu (H n) ξ'‖
    rw [w8ShellNu_smul, w8ShellNu_smul]
    exact (w8_freqShell (H n)).2.1 ξ hξ ξ' hξ'
  · show ‖(2 * π) • w8ShellNu (H n) ξ - omegaTan m hm ξ‖ ≤ w8alpha 𝔱 n / (70 * measLA m hm)
    rw [w8ShellNu_smul]
    obtain ⟨h1, h2, -⟩ := (w8_freqShell (H n)).2.2.1
    exact (h1 ξ hξ).trans h2

end KAM.Wave

end
