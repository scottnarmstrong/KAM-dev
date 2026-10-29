/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.ODE.Exit
public import KAM.ODE.Continuation
public import KAM.ODE.Hamiltonian
public import KAM.Strip.RealRestriction
public import KAM.Frozen.Defs.ActionNbhd
public import KAM.Frozen.Defs.ComplexStrip
public import KAM.Frozen.Defs.RealHamiltonian
public import KAM.Frozen.Defs.InvarianceError
public import KAM.Frozen.Defs.IsPrimaryOnStrip
public import KAM.Frozen.Defs.IsRealOnReals
public import KAM.Frozen.Iso.Defs.BorderedHessian

/-!
# Part 5 setting: standing data, patches, constants and torus outputs

Definitions and structures only; there is no theorem in this module.

* Notation of `bpI:p3:setting` and `bpI:p3:constants`: `toC` (the inclusion `ι : ℝⁿ → ℂⁿ`),
  `realAct` (`U`), `realPart` (`Re h ∘ ι`), `totalH` (`H = h + f`), `rhoInf` (`ρ∞`), `fractD`
  (`𝔇`), `P2` (phase space).
* The premises of I-HEAD, packaged: `BaseData`, `HeadData`, `PerturbData`.
* A chart patch of Part 3 as consumed by Part 5 (`EnergyPatch`, with `Q`, `O`, `Omega`, `K`), its
  constants (`PatchConst`, `bpI:p5:patch-const`) and the consequences of `ε < ε₀` (`Smallness`,
  `bpI:p5:eps0`).
* The output (T1)-(T4) of `bpI:p3:tori` for one torus (`TorusOutput`), the standing data of the
  graph and separation sections (`GraphData`, `SepSetting`) and the sets `graphSet`, `levelSet`,
  `sepRegion`.
* The interface to Part 3 (`ChartCover`, `ToriExistence`): standing structures that Part 5
  consumes and never produces.
-/

@[expose] public noncomputable section

open Set Metric

namespace KAM.Iso.Confinement

open KAM

/-- The real vector `x` read in `ℂⁿ` (`ι` of the blueprint); definitionally `realInclusion n x`. -/
abbrev toC {n : ℕ} (x : Fin n → ℝ) : Fin n → ℂ := fun i => (x i : ℂ)

example {n : ℕ} (x : Fin n → ℝ) : toC x = realInclusion n x := rfl

/-- `{I ∈ ℝ² : ι I ∈ B_{r₀}}` (the blueprint's `U`). -/
def realAct (B : Set (Fin 2 → ℝ)) (r₀ : ℝ) : Set (Fin 2 → ℝ) := {I | toC I ∈ actionNbhd B r₀}

/-- `I ↦ Re h(ι I)`, the real part of `h` on real actions (first chart coordinate). -/
def realPart (h : (Fin 2 → ℂ) → ℂ) (I : Fin 2 → ℝ) : ℝ := (h (toC I)).re

/-- `H = h + f` as a function on `ℂ² × ℂ²` (the Hamiltonian of Part 3 and of I-G1). -/
def totalH (h : (Fin 2 → ℂ) → ℂ) (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ) :
    (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ := fun z => h z.2 + f z

/-- `ρ_∞ = s/8` with `s = min {s₀, 1}` (`bpI:p3:constants`). -/
def rhoInf (s₀ : ℝ) : ℝ := min s₀ 1 / 8

/-- `𝔇 = T_{s/2} × B_{r₀/2}` (`bpI:p3:constants`). -/
def fractD (B : Set (Fin 2 → ℝ)) (s₀ r₀ : ℝ) : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ)) :=
  complexStrip 2 (min s₀ 1 / 2) ×ˢ actionNbhd B (r₀ / 2)

/-- Premises of I-HEAD on `(B, s₀, r₀, h)` that every Part 5 lemma about `H_ℝ` uses. -/
structure BaseData (B : Set (Fin 2 → ℝ)) (s₀ r₀ : ℝ) (h : (Fin 2 → ℂ) → ℂ) : Prop where
  hs : 0 < s₀
  hr : 0 < r₀
  holo : DifferentiableOn ℂ h (actionNbhd B r₀)
  real : ∀ I : Fin 2 → ℝ, toC I ∈ actionNbhd B r₀ → (h (toC I)).im = 0

/-- The source premises of I-HEAD on `(B, s₀, r₀, h, B', η)`, verbatim (frozen binders `hB hBb hBne
hs hr hh hhreal hiso hB' hcompact hinside hη`). -/
structure HeadData (B : Set (Fin 2 → ℝ)) (s₀ r₀ : ℝ) (h : (Fin 2 → ℂ) → ℂ)
    (B' : Set (Fin 2 → ℝ)) (η : ℝ) : Prop extends BaseData B s₀ r₀ h where
  isOpen : IsOpen B
  bounded : Bornology.IsBounded B
  nonempty : B.Nonempty
  iso : ∀ I : Fin 2 → ℝ, toC I ∈ actionNbhd B r₀ → (borderedHessian h I).det ≠ 0
  isOpen' : IsOpen B'
  compact : IsCompact (closure B')
  inside : closure B' ⊆ B
  hη : 0 < η

/-- The premises of I-HEAD on `(f, ε)` except the smallness `ε < ε₀` (frozen binders: the four
hypotheses on `f`, `0 ≤ ε`, and the bound `‖f z‖ ≤ ε`). -/
structure PerturbData (B : Set (Fin 2 → ℝ)) (s₀ r₀ : ℝ)
    (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ) (ε : ℝ) : Prop where
  holo : DifferentiableOn ℂ f (complexStrip 2 s₀ ×ˢ actionNbhd B r₀)
  periodic : ∀ z ∈ complexStrip 2 s₀ ×ˢ actionNbhd B r₀, ∀ k : Fin 2 → ℤ,
    f (z.1 + (fun i => (k i : ℂ)), z.2) = f z
  real : ∀ θ I : Fin 2 → ℝ, toC I ∈ actionNbhd B r₀ → (f (toC θ, toC I)).im = 0
  nonneg : 0 ≤ ε
  bound : ∀ z ∈ complexStrip 2 s₀ ×ˢ actionNbhd B r₀, ‖f z‖ ≤ ε

/-- A patch of Part 3 (`bpI:p3:patch`, `chart`, `patch-rays`) in the form Part 5 consumes: the
chart `Φ = (hR, m)` on `W`, its inverse `Ψ`, the window `δE, δm, ρc` and the two ray slopes.
TYPING DATA, produced by Part 3's `chartCover_exists`; `hR = realPart h`. -/
structure EnergyPatch (hR : (Fin 2 → ℝ) → ℝ) (B : Set (Fin 2 → ℝ)) (η₁ : ℝ) where
  c : Fin 2 → ℝ
  W : Set (Fin 2 → ℝ)
  m : (Fin 2 → ℝ) → ℝ
  Ψ : ℝ × ℝ → (Fin 2 → ℝ)
  δE : ℝ
  δm : ℝ
  ρc : ℝ
  mPlus : ℝ
  mMinus : ℝ
  δE_pos : 0 < δE
  δm_pos : 0 < δm
  ρc_pos : 0 < ρc
  isOpen_W : IsOpen W
  W_subset_B : W ⊆ B
  W_subset_ball : W ⊆ ball c (η₁ / 4)
  hR_contDiffOn : ContDiffOn ℝ 1 hR W
  m_contDiffOn : ContDiffOn ℝ 1 m W
  isOpen_V : IsOpen ((fun I => (hR I, m I)) '' W)
  Ψ_contDiffOn : ContDiffOn ℝ 1 Ψ ((fun I => (hR I, m I)) '' W)
  Ψ_mem : ∀ v ∈ (fun I => (hR I, m I)) '' W, Ψ v ∈ W
  Ψ_left : ∀ I ∈ W, Ψ (hR I, m I) = I
  Ψ_right : ∀ v ∈ (fun I => (hR I, m I)) '' W, (hR (Ψ v), m (Ψ v)) = v
  Q_subset : Icc (hR c - δE) (hR c + δE) ×ˢ Icc (-δm) δm ⊆ (fun I => (hR I, m I)) '' W
  ρc_le : ρc ≤ η₁ / 4
  ball_subset : ball c ρc ⊆ W
  ball_h : ∀ I ∈ ball c ρc, |hR I - hR c| < δE / 2
  ball_m : ∀ I ∈ ball c ρc, |m I| < δm / 4
  mPlus_mem : mPlus ∈ Ioo (δm / 2) δm
  mMinus_mem : mMinus ∈ Ioo (-δm) (-(δm / 2))

variable {hR : (Fin 2 → ℝ) → ℝ} {B : Set (Fin 2 → ℝ)} {η₁ : ℝ}

/-- `Q = [E_c - δE, E_c + δE] × [-δm, δm]`. -/
def EnergyPatch.Q (p : EnergyPatch hR B η₁) : Set (ℝ × ℝ) :=
  Icc (hR p.c - p.δE) (hR p.c + p.δE) ×ˢ Icc (-p.δm) p.δm

/-- `O = (E_c - δE, E_c + δE) × (-δm, δm)`. -/
def EnergyPatch.O (p : EnergyPatch hR B η₁) : Set (ℝ × ℝ) :=
  Ioo (hR p.c - p.δE) (hR p.c + p.δE) ×ˢ Ioo (-p.δm) p.δm

/-- `Ω = Φ⁻¹(O)` (open, `⊆ W`). -/
def EnergyPatch.Omega (p : EnergyPatch hR B η₁) : Set (Fin 2 → ℝ) :=
  {I | I ∈ p.W ∧ (hR I, p.m I) ∈ p.O}

/-- `𝒦 = Φ⁻¹(Q)` (compact, `⊆ W`). -/
def EnergyPatch.K (p : EnergyPatch hR B η₁) : Set (Fin 2 → ℝ) :=
  {I | I ∈ p.W ∧ (hR I, p.m I) ∈ p.Q}

/-- Patch constants (`bpI:p5:patch-const`): `𝒩 = cthickening r 𝒦`, `L_m`, `L_Φ`, `κ`; chosen
once per patch (`patchConst_exists`). -/
structure PatchConst (p : EnergyPatch hR B η₁) (r Lm LΦ κ : ℝ) : Prop where
  r_pos : 0 < r
  r_le_one : r ≤ 1
  thick_subset : cthickening r p.K ⊆ p.W
  Lm_ge : 1 ≤ Lm
  Lm_bound : ∀ I ∈ cthickening r p.K, ‖fderiv ℝ p.m I‖ ≤ Lm
  LΦ_ge : 1 ≤ LΦ
  LΦ_bound : ∀ v ∈ p.Q, ‖fderiv ℝ p.Ψ v‖ ≤ LΦ
  κ_pos : 0 < κ
  κ_le_quarter : κ ≤ p.δm / 4
  κ_le_plus : κ ≤ p.δm - p.mPlus
  κ_le_minus : κ ≤ p.δm + p.mMinus

/-- The consequences of `ε < ε₀` used downstream (`bpI:p5:eps0`). -/
structure Smallness (p : EnergyPatch hR B η₁) (r Lm LΦ κ F₁ C_K ρinf ε : ℝ) : Prop where
  nonneg : 0 ≤ ε
  le_one : ε ≤ 1
  lt_dE : ε < p.δE / 4
  lt_rho : 8 * C_K * ε < ρinf
  lt_r : C_K * ε < r
  lt_kappa : Lm * C_K * ε < κ
  lt_Phi : 2 * F₁ * LΦ * ε < 1

/-- Phase space `ℝ² × ℝ²` (angles first), with the max norm. -/
abbrev P2 := (Fin 2 → ℝ) × (Fin 2 → ℝ)

/-! ## The output of Part 3 for one torus and the graph data -/

/-- The output (T1)-(T4) of `bpI:p3:tori` for ONE torus `K = K_±` with base point `I = I_±` and
frequency `ωt = ωt_±`, at energy `E`, for `H = h + f` (`ρ∞ = rhoInf s₀`, `u = (K θ).1 - θ`,
`v = (K θ).2 - ι I`). The position clauses (T5)-(T7) enter through `GraphData` and the patch. -/
structure TorusOutput (h : (Fin 2 → ℂ) → ℂ) (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ)
    (ε C_K s₀ E : ℝ) (K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (I ωt : Fin 2 → ℝ) : Prop where
  holo : DifferentiableOn ℂ K (complexStrip 2 (rhoInf s₀))
  primary : IsPrimaryOnStrip K (rhoInf s₀)
  real : IsRealOnReals K
  invariant : ∀ θ ∈ complexStrip 2 (rhoInf s₀), invarianceError (totalH h f) K ωt θ = 0
  energy : ∀ θ ∈ complexStrip 2 (rhoInf s₀), totalH h f (K θ) = (E : ℂ)
  close : ∀ θ ∈ complexStrip 2 (rhoInf s₀), ‖K θ - (θ, toC I)‖ ≤ C_K * ε
  du : ∀ θ ∈ complexStrip 2 (rhoInf s₀ / 2),
    ‖fderiv ℂ (fun θ => (K θ).1 - θ) θ‖ ≤ 4 * C_K * ε / rhoInf s₀
  dv : ∀ θ ∈ complexStrip 2 (rhoInf s₀ / 2),
    ‖fderiv ℂ (fun θ => (K θ).2 - toC I) θ‖ ≤ 4 * C_K * ε / rhoInf s₀

/-- Typing data for one torus graph (conclusions (b), (c) of the graph lemma and the position of
its base point in the patch). `Cε = C_K ε`. -/
structure GraphData {hR : (Fin 2 → ℝ) → ℝ} {B : Set (Fin 2 → ℝ)} {η₁ : ℝ}
    (p : EnergyPatch hR B η₁) (H : P2 → ℝ) (E Cε : ℝ) (Y : (Fin 2 → ℝ) → (Fin 2 → ℝ))
    (I : Fin 2 → ℝ) (mσ : ℝ) : Prop where
  continuous : Continuous Y
  near : ∀ φ, ‖Y φ - I‖ ≤ Cε
  energy : ∀ φ, H (φ, Y φ) = E
  base_mem : I ∈ p.K
  base_slope : p.m I = mσ

/-! ## The separation setting -/

/-- Standing data of `§sec-sep`, the blueprint's "keep the notation of `§graph`": the typing data
of one patch, its constants, the smallness, and the two torus graphs `Y₊, Y₋` (base points
`I₊, I₋`) at energy `E`. Prop-structure; assembled in `confinement_main_of_tori` from
`torus_graph`, `torus_graph_mem`, the patch and `ToriExistence`; never produced by a theorem of
this section. -/
structure SepSetting (B : Set (Fin 2 → ℝ)) (s₀ r₀ : ℝ) (h : (Fin 2 → ℂ) → ℂ)
    (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ) (ε η₁ F₁ C_K : ℝ)
    (p : EnergyPatch (realPart h) B η₁) (r Lm LΦ κ E : ℝ)
    (Yp Ym : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (Ip Im : Fin 2 → ℝ) : Prop where
  base : BaseData B s₀ r₀ h
  perturb : PerturbData B s₀ r₀ f ε
  dbound : ∀ z ∈ fractD B s₀ r₀, ‖fderiv ℂ f z‖ ≤ F₁ * ε
  pconst : PatchConst p r Lm LΦ κ
  small : Smallness p r Lm LΦ κ F₁ C_K (rhoInf s₀) ε
  plus : GraphData p (realHamiltonian h f) E (C_K * ε) Yp Ip p.mPlus
  minus : GraphData p (realHamiltonian h f) E (C_K * ε) Ym Im p.mMinus

/-- `𝒯 = {(φ, Y φ)}`. -/
def graphSet (Y : (Fin 2 → ℝ) → (Fin 2 → ℝ)) : Set P2 := {z | z.2 = Y z.1}

/-- `G = {H_ℝ = E}`. -/
def levelSet (H : P2 → ℝ) (E : ℝ) : Set P2 := {z | H z = E}

/-- `𝒱 = {(φ, I) : I ∈ Ω, μ₋(φ) < m(I) < μ₊(φ)}`, `μ_± = m ∘ Y_±`. -/
def sepRegion {hR : (Fin 2 → ℝ) → ℝ} {B : Set (Fin 2 → ℝ)} {η₁ : ℝ} (p : EnergyPatch hR B η₁)
    (Yp Ym : (Fin 2 → ℝ) → (Fin 2 → ℝ)) : Set P2 :=
  {z | z.2 ∈ p.Omega ∧ p.m (Ym z.1) < p.m z.2 ∧ p.m z.2 < p.m (Yp z.1)}

/-! ## Interface to Part 3 -/

/-- Finite chart cover of `closure B'` by patches of `§p3:sec-charts`, the slope data of the rays,
and the derivative constant `F₁` of `bpI:p3:hypothesis-d`. -/
structure ChartCover (B : Set (Fin 2 → ℝ)) (s₀ r₀ : ℝ) (h : (Fin 2 → ℂ) → ℂ)
    (B' : Set (Fin 2 → ℝ)) (η η₁ F₁ : ℝ) (patches : Set (EnergyPatch (realPart h) B η₁)) :
    Prop where
  finite : patches.Finite
  cover : closure B' ⊆ ⋃ p ∈ patches, ball p.c p.ρc
  η₁_pos : 0 < η₁
  η₁_le : η₁ ≤ η
  F₁_pos : 0 < F₁
  dbound : ∀ (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ) (ε : ℝ), PerturbData B s₀ r₀ f ε → ε ≤ 1 →
    ∀ z ∈ fractD B s₀ r₀, ‖fderiv ℂ f z‖ ≤ F₁ * ε

/-- `bpI:p3:tori` for every `f, ε < ε₁`, `I₀ ∈ closure B'`, `E` with `|E - h(I₀)| ≤ ε`: a patch
`j` with `‖I₀ - c_j‖ < ρ_j` and the two tori of (T1)-(T4), with base points
`I_± = Φ_j⁻¹(E, m_±)` (T7). WAITS FOR THE SEAL OF I-G1 (`KAM.Iso.isoenergetic_kam`). -/
structure ToriExistence (B : Set (Fin 2 → ℝ)) (s₀ r₀ : ℝ) (h : (Fin 2 → ℂ) → ℂ)
    (B' : Set (Fin 2 → ℝ)) (η₁ : ℝ) (patches : Set (EnergyPatch (realPart h) B η₁))
    (ε₁ C_K : ℝ) : Prop where
  ε₁_pos : 0 < ε₁
  ε₁_le_one : ε₁ ≤ 1
  CK_pos : 0 < C_K
  tori : ∀ (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ) (ε : ℝ), PerturbData B s₀ r₀ f ε → ε < ε₁ →
    ∀ I₀ ∈ closure B', ∀ E : ℝ, |E - realPart h I₀| ≤ ε →
      ∃ p ∈ patches, ‖I₀ - p.c‖ < p.ρc ∧
        ∃ (Kp Km : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (Ip Im ωp ωm : Fin 2 → ℝ),
          TorusOutput h f ε C_K s₀ E Kp Ip ωp ∧ Ip = p.Ψ (E, p.mPlus) ∧
          TorusOutput h f ε C_K s₀ E Km Im ωm ∧ Im = p.Ψ (E, p.mMinus)

end KAM.Iso.Confinement
