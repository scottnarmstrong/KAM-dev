/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Assembly.ShellGeom

/-!
# W8: the patched family (blueprint `bpW:w8:patch`, `bpW:w8:patch-local`, `bpW:w8:patch-cont`)

Off the frontier: source-faithful infrastructure used by several nodes. The dependency graph is
still being built. Blueprint labels `bpW:w8:patch`, `bpW:w8:patch-local`, `bpW:w8:boundaries`,
`bpW:w8:patch-cont` (milestone W8).

The single-shell objects `Γ_n = Π^{(n)}_*`, `ν^{(n)}_*`, `K^{(n)}` are outputs of the W6 iteration
(Definition `bpW:w8:shell-iter`), which has no Lean form yet. The patching of Definition
`bpW:w8:patch` is therefore stated for arbitrary families `Γs n`, `νs n`, `Ks n` indexed by the
shell number: `n(I)` (`w8ShellIdx`), `Γ = ⋃ Γ_n` (`w8PatchSet`), `ν` (`w8PatchNu`), `K`
(`w8PatchK`). The construction property `Γ_n ⊆ Π_n` of `bpW:w8:shell-iter` (`Π^{(n)}_* ⊆ Π_{-1} =
Π_n ∖ Ξ`) is the only assumption of the locality lemmas (`w8Patch_local`, Lemma
`bpW:w8:patch-local`).

The regularity lemmas `measurableSet_w8PatchSet_of_pieces`, `continuousOn_w8PatchNu_of_pieces`,
`continuousOn_w8PatchK_of_pieces` are the patching step of Lemma `bpW:w8:patch-cont` for arbitrary
pieces: they are conditional helpers whose hypotheses are the per-shell regularity, which for the
shell iteration is W6's (Lemma `bpW:w8:freq-shell` (iv), Lemma `bpW:w8:shell-inv` (ii)); they do
not stand in for `bpW:w8:patch-cont` itself. The inclusion
`Γ ⊆ {I | (∀ i, 0 < I i) ∧ r(I) < √(2 t₀)}` (`w8PatchSet_subset`) needs only `Γ_n ⊆ Π_n`.
-/

@[expose] public noncomputable section

open Set

namespace KAM.Wave

/-- `n(I)`: the index `n` with `I ∈ R_n` (`0` if there is none) (blueprint `bpW:w8:patch`). -/
def w8ShellIdx (t0 : ℝ) (I : Fin 2 → ℝ) : ℕ := by
  classical
  exact if h : ∃ n, I ∈ w8Rn t0 n then Nat.find h else 0

/-- The patched parameter set `Γ = ⋃_n Γ_n` (blueprint `bpW:w8:patch`). -/
def w8PatchSet (Γs : ℕ → Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ) := ⋃ n, Γs n

/-- The patched frequency map: `ν(I) = ν^{(n(I))}(I)` on `Γ`, `0` elsewhere
(blueprint `bpW:w8:patch`). -/
def w8PatchNu (t0 : ℝ) (Γs : ℕ → Set (Fin 2 → ℝ)) (νs : ℕ → (Fin 2 → ℝ) → Fin 2 → ℝ)
    (I : Fin 2 → ℝ) : Fin 2 → ℝ := by
  classical
  exact if I ∈ w8PatchSet Γs then νs (w8ShellIdx t0 I) I else 0

/-- The patched embeddings: `K_I = K^{(n(I))}_I` on `Γ`, `0` elsewhere (blueprint `bpW:w8:patch`).
-/
def w8PatchK {E : Type*} [Zero E] (t0 : ℝ) (Γs : ℕ → Set (Fin 2 → ℝ))
    (Ks : ℕ → (Fin 2 → ℝ) → (Fin 2 → ℝ) → E) (I : Fin 2 → ℝ) : (Fin 2 → ℝ) → E := by
  classical
  exact if I ∈ w8PatchSet Γs then Ks (w8ShellIdx t0 I) I else 0

variable {t0 : ℝ} {Γs : ℕ → Set (Fin 2 → ℝ)}

/-- `n(I) = n` for `I ∈ R_n` (W7 `bpW:w7:shell-geom` (i): the shells are disjoint). -/
theorem w8ShellIdx_eq (ht : 0 < t0) {I : Fin 2 → ℝ} {n : ℕ} (hI : I ∈ w8Rn t0 n) :
    w8ShellIdx t0 I = n := by
  classical
  unfold w8ShellIdx
  split_ifs with h
  · by_contra hne
    exact Set.disjoint_left.1 (w8Rn_disjoint ht hne) (Nat.find_spec h) hI
  · exact absurd ⟨n, hI⟩ h

section Local

variable (hΓ : ∀ n, Γs n ⊆ w8Pi t0 n)
include hΓ

/-- `Γ ∩ O_n = Γ_n` for `O_n = Π_n` (blueprint `bpW:w8:patch-local`, Step `stepW:w8:pl-id`). -/
theorem w8PatchSet_inter_w8Pi (ht : 0 < t0) (n : ℕ) : w8PatchSet Γs ∩ w8Pi t0 n = Γs n := by
  ext I
  refine ⟨fun ⟨hI, hIn⟩ => ?_, fun hI => ⟨mem_iUnion.2 ⟨n, hI⟩, hΓ n hI⟩⟩
  obtain ⟨n', hn'⟩ := mem_iUnion.1 hI
  by_cases h : n' = n
  · exact h ▸ hn'
  · exact absurd hIn (Set.disjoint_left.1 (w8Pi_disjoint ht h) (hΓ n' hn'))

/-- For `I ∈ Γ_n`: `n(I) = n`. -/
theorem w8ShellIdx_of_mem (ht : 0 < t0) {n : ℕ} {I : Fin 2 → ℝ} (hI : I ∈ Γs n) :
    w8ShellIdx t0 I = n :=
  w8ShellIdx_eq ht (w8Pi_subset_Rn n (hΓ n hI))

/-- For `I ∈ Γ_n`: `ν(I) = ν^{(n)}(I)` (blueprint `bpW:w8:patch-local`). -/
theorem w8PatchNu_of_mem (ht : 0 < t0) (νs : ℕ → (Fin 2 → ℝ) → Fin 2 → ℝ) {n : ℕ}
    {I : Fin 2 → ℝ} (hI : I ∈ Γs n) : w8PatchNu t0 Γs νs I = νs n I := by
  classical
  have hm : I ∈ w8PatchSet Γs := mem_iUnion.2 ⟨n, hI⟩
  unfold w8PatchNu
  simp only [hm, ↓reduceIte, w8ShellIdx_of_mem hΓ ht hI]

/-- For `I ∈ Γ_n`: `K_I = K^{(n)}_I` (blueprint `bpW:w8:patch-local`). -/
theorem w8PatchK_of_mem {E : Type*} [Zero E] (ht : 0 < t0)
    (Ks : ℕ → (Fin 2 → ℝ) → (Fin 2 → ℝ) → E) {n : ℕ} {I : Fin 2 → ℝ} (hI : I ∈ Γs n) :
    w8PatchK t0 Γs Ks I = Ks n I := by
  classical
  have hm : I ∈ w8PatchSet Γs := mem_iUnion.2 ⟨n, hI⟩
  unfold w8PatchK
  simp only [hm, ↓reduceIte, w8ShellIdx_of_mem hΓ ht hI]

/-- **Locality of the patching** (blueprint `bpW:w8:patch-local`), for families with
`Γ_n ⊆ Π_n`: the `O_n = Π_n` are open and pairwise disjoint, `Γ_n ⊆ O_n`, `Γ ∩ O_n = Γ_n`, and
on `Γ_n`: `n(I) = n`, `ν(I) = ν^{(n)}(I)`, `K_I = K^{(n)}_I`. -/
theorem w8Patch_local {E : Type*} [Zero E] (ht : 0 < t0) (νs : ℕ → (Fin 2 → ℝ) → Fin 2 → ℝ)
    (Ks : ℕ → (Fin 2 → ℝ) → (Fin 2 → ℝ) → E) :
    (∀ n, IsOpen (w8Pi t0 n)) ∧ (∀ n n', n ≠ n' → Disjoint (w8Pi t0 n) (w8Pi t0 n')) ∧
      (∀ n, Γs n ⊆ w8Pi t0 n) ∧ (∀ n, w8PatchSet Γs ∩ w8Pi t0 n = Γs n) ∧
      ∀ n, ∀ I ∈ Γs n, w8ShellIdx t0 I = n ∧ w8PatchNu t0 Γs νs I = νs n I ∧
        w8PatchK t0 Γs Ks I = Ks n I :=
  ⟨w8Pi_isOpen ht, fun _ _ h => w8Pi_disjoint ht h, hΓ, w8PatchSet_inter_w8Pi hΓ ht,
    fun _ _ hI => ⟨w8ShellIdx_of_mem hΓ ht hI, w8PatchNu_of_mem hΓ ht νs hI,
      w8PatchK_of_mem hΓ ht Ks hI⟩⟩

/-- (blueprint `bpW:w8:patch-cont`, Step `stepW:w8:pc-incl`) `Γ ⊆ (0, t₀)²`, hence
`Γ ⊆ {I | (∀ i, 0 < I i) ∧ √(I₀ + I₁) < √(2 t₀)}`. -/
theorem w8PatchSet_subset (ht : 0 < t0) :
    w8PatchSet Γs ⊆ {I | (∀ i, 0 < I i) ∧ Real.sqrt (I 0 + I 1) < Real.sqrt (2 * t0)} := by
  intro I hI
  obtain ⟨n, hn⟩ := mem_iUnion.1 hI
  have hbox : ∀ i, 0 < I i ∧ I i < t0 := fun i => by
    have := (w8Pi_subset_Rn n (hΓ n hn)).1 i (mem_univ i)
    exact ⟨this.1, this.2.trans_le (w8tn_le ht n)⟩
  refine ⟨fun i => (hbox i).1, Real.sqrt_lt_sqrt ?_ ?_⟩
  · linarith [(hbox 0).1, (hbox 1).1]
  · linarith [(hbox 0).2, (hbox 1).2]

/-- Patching step of `bpW:w8:patch-cont` (Step `stepW:w8:pc-nu`), for arbitrary pieces: if each
`ν^{(n)}` is continuous on `Γ_n`, then `ν` is continuous on `Γ` (conditional helper). -/
theorem continuousOn_w8PatchNu_of_pieces (ht : 0 < t0) {νs : ℕ → (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hν : ∀ n, ContinuousOn (νs n) (Γs n)) :
    ContinuousOn (w8PatchNu t0 Γs νs) (w8PatchSet Γs) := by
  refine w8ext_continuousOn_of_local fun I hI => ?_
  obtain ⟨n, hn⟩ := mem_iUnion.1 hI
  refine ⟨w8Pi t0 n, w8Pi_isOpen ht n, hΓ n hn, νs n, ?_, fun J hJ => ?_⟩
  · rw [w8PatchSet_inter_w8Pi hΓ ht n]; exact hν n
  · rw [w8PatchSet_inter_w8Pi hΓ ht n] at hJ
    exact w8PatchNu_of_mem hΓ ht νs hJ

/-- Patching step of `bpW:w8:patch-cont` (Step `stepW:w8:pc-K`), for arbitrary pieces: if each
`(I, θ) ↦ K^{(n)}_I(θ)` is continuous on `Γ_n × ℝ²`, then `(I, θ) ↦ K_I(θ)` is continuous on
`Γ × ℝ²` (conditional helper). -/
theorem continuousOn_w8PatchK_of_pieces {E : Type*} [Zero E] [TopologicalSpace E] (ht : 0 < t0)
    {Ks : ℕ → (Fin 2 → ℝ) → (Fin 2 → ℝ) → E}
    (hK : ∀ n, ContinuousOn (Function.uncurry (Ks n)) (Γs n ×ˢ univ)) :
    ContinuousOn (Function.uncurry (w8PatchK t0 Γs Ks)) (w8PatchSet Γs ×ˢ univ) := by
  refine w8ext_continuousOn_of_local fun z hz => ?_
  obtain ⟨n, hn⟩ := mem_iUnion.1 hz.1
  have hinter : w8PatchSet Γs ×ˢ (univ : Set (Fin 2 → ℝ)) ∩ w8Pi t0 n ×ˢ univ =
      Γs n ×ˢ univ := by
    rw [prod_inter_prod, inter_univ, w8PatchSet_inter_w8Pi hΓ ht n]
  refine ⟨w8Pi t0 n ×ˢ univ, (w8Pi_isOpen ht n).prod isOpen_univ, ⟨hΓ n hn, mem_univ _⟩,
    Function.uncurry (Ks n), ?_, fun w hw => ?_⟩
  · rw [hinter]; exact hK n
  · rw [hinter] at hw
    show w8PatchK t0 Γs Ks w.1 w.2 = Ks n w.1 w.2
    rw [w8PatchK_of_mem hΓ ht Ks hw.1]

end Local

/-- Patching step of `bpW:w8:patch-cont` (Step `stepW:w8:pc-borel`): a countable union of Borel
pieces is Borel. -/
theorem measurableSet_w8PatchSet_of_pieces (hmeas : ∀ n, MeasurableSet (Γs n)) :
    MeasurableSet (w8PatchSet Γs) :=
  MeasurableSet.iUnion hmeas

end KAM.Wave

end
