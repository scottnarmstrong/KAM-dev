/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Application.LambdaDrift.Poisson

/-!
# The Lie remainder identities of orders 1 and 2

Design `docs/campaign/design/HD11964-PILOT.md` §6.2 (and §10 item 3). For a Hamiltonian `H = h + P`
whose part `h` does not depend on the angle `θ_k` (for LP's chart, the Kepler part `h(Λ)`), the
approximate integrals of the action `I_k`

* `F₁ = I_k + D_k χ₁` and
* `F₂ = I_k + D_k χ₁ + D_k χ₂ − ½ {D_k χ₁, χ₁}`

(the truncated Lie series `exp(L_{−χ₁}) exp(L_{−χ₂}) I_k`, `L_χ G = {G, χ}`) have the rates

* `{F₁, H} = −D_k r₁ + {D_k χ₁, P}`,
* `{F₂, H} = −D_k r₁ − D_k r₂ + {D_k r₁, χ₁} + {D_k χ₂, P} − ½ {{D_k χ₁, χ₁}, P}`,

with the residuals of the homological equations `r₁ = P − {χ₁, h}` and
`r₂ = {P − ½ {χ₁, h}, χ₁} − {χ₂, h}`.
These are identities: no relation between `χ₁, χ₂` and `h, P` is assumed. When the generators solve
`ω·∂_λ χ₁ = Π_S P` and `ω·∂_λ χ₂ = Π_S {P − ½ Π_S P, χ₁}`, the residuals are Fourier tails, the
bracket terms are of order `μ`·tail, `μ³` and `μ³`, and a certificate bounds every term with
relative accuracy `O(1)`: no `O(μ)` cancellation is left to the kernel.

The proof uses only the calculus of `Poisson.lean`: antisymmetry, `{I_k, G} = −D_k G`, the
derivation rule of `D_k`, and the Jacobi identity (for `{{D_k χ₁, χ₁}, h}`). Smoothness is assumed
on an open set and used pointwise.

## Main results

* `approxIntegral₁`, `approxIntegral₂`, `residual₁`, `residual₂`.
* `pb_approxIntegral₁`, `pb_approxIntegral₂`: the identities.
* `abs_pb_approxIntegral₂_le`: the bound a cell check certifies, term by term.
-/

@[expose] public noncomputable section

open Set Filter Topology KAM KAM.Planetary
open scoped ContDiff

namespace KAM.Application.LambdaDrift

variable {d : ℕ}

/-- The order-1 approximate integral of the action `I_k = w.2 k`: `F = I_k + D_k χ₁`. -/
def approxIntegral₁ (k : Fin d) (χ₁ : Phase d → ℝ) : Phase d → ℝ :=
  fun y => y.2 k + dirDeriv (angleDir k) χ₁ y

/-- The order-2 approximate integral of the action `I_k = w.2 k` (the truncated Lie series
`exp(L_{-χ₁}) exp(L_{-χ₂}) I_k`): `F = I_k + D_k χ₁ + D_k χ₂ − ½ {D_k χ₁, χ₁}`. -/
def approxIntegral₂ (k : Fin d) (χ₁ χ₂ : Phase d → ℝ) : Phase d → ℝ :=
  fun y => y.2 k + dirDeriv (angleDir k) χ₁ y + dirDeriv (angleDir k) χ₂ y -
    pb (dirDeriv (angleDir k) χ₁) χ₁ y / 2

/-- The order-1 residual `r₁ = P − {χ₁, h}` (for `h = h(Λ)`, `{χ₁, h} = ω·∂_λ χ₁`). -/
def residual₁ (h P χ₁ : Phase d → ℝ) : Phase d → ℝ := fun y => P y - pb χ₁ h y

/-- The order-2 residual `r₂ = {P − ½ {χ₁, h}, χ₁} − {χ₂, h}`. -/
def residual₂ (h P χ₁ χ₂ : Phase d → ℝ) : Phase d → ℝ :=
  fun y => pb (fun z => P z - pb χ₁ h z / 2) χ₁ y - pb χ₂ h y

/-- The action coordinate as a continuous linear map. -/
private def momCLM (k : Fin d) : Phase d →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) k).comp (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin d → ℝ))

private theorem hasFDerivAt_mom (k : Fin d) (w : Phase d) :
    HasFDerivAt (fun y : Phase d => y.2 k) (momCLM k) w :=
  (momCLM k).hasFDerivAt

/-- An angle-independent `h` has no bracket with anything through `D_k h`. -/
private theorem pb_dirDeriv_eq_zero {h a : Phase d → ℝ} {v : Phase d}
    (hh : ∀ y, fderiv ℝ h y v = 0) (y : Phase d) : pb a (dirDeriv v h) y = 0 := by
  have h0 : dirDeriv v h = fun _ => (0 : ℝ) := funext hh
  refine pb_eq_zero_of_fderiv_eq_zero ?_
  rw [h0]
  exact fderiv_const_apply 0

/-- For an angle-independent `h`: `{D_v a, h} = D_v {a, h}`. -/
private theorem pb_dirDeriv_left {h a : Phase d → ℝ} {v : Phase d} (hh : ∀ y, fderiv ℝ h y v = 0)
    {y : Phase d} (ha : ContDiffAt ℝ ∞ a y) (hhs : ContDiffAt ℝ ∞ h y) :
    pb (dirDeriv v a) h y = dirDeriv v (pb a h) y := by
  rw [dirDeriv_pb ha hhs, pb_dirDeriv_eq_zero hh, add_zero]

/-- `D_v (f − g) = D_v f − D_v g` at a point of differentiability. -/
private theorem dirDeriv_sub {f g : Phase d → ℝ} {y : Phase d} (v : Phase d)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    dirDeriv v (fun z => f z - g z) y = dirDeriv v f y - dirDeriv v g y := by
  show fderiv ℝ (f - g) y v = _
  rw [(hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv]
  rfl

/-- `D_v (f − g/2) = D_v f − D_v g / 2` at a point of differentiability. -/
private theorem dirDeriv_sub_half {f g : Phase d → ℝ} {y : Phase d} (v : Phase d)
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    dirDeriv v (fun z => f z - g z / 2) y = dirDeriv v f y - dirDeriv v g y / 2 := by
  have he : (fun z => f z - g z / 2) = fun z => f z - (1 / 2 : ℝ) * g z := by
    funext z; ring
  have hd : HasFDerivAt (fun z => f z - (1 / 2 : ℝ) * g z)
      (fderiv ℝ f y - (1 / 2 : ℝ) • fderiv ℝ g y) y :=
    hf.hasFDerivAt.sub (hg.hasFDerivAt.const_mul (1 / 2 : ℝ))
  rw [he]
  show fderiv ℝ (fun z => f z - (1 / 2 : ℝ) * g z) y v = _
  rw [hd.fderiv]
  show fderiv ℝ f y v - (1 / 2 : ℝ) * fderiv ℝ g y v = _
  unfold dirDeriv
  ring

/-- `{f − g, b} = {f, b} − {g, b}` at a point of differentiability. -/
private theorem pb_sub_left {f g b : Phase d → ℝ} {y : Phase d} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) : pb (fun z => f z - g z) b y = pb f b y - pb g b y := by
  show pb (f - g) b y = _
  rw [pb_of_hasFDerivAt (hf.hasFDerivAt.sub hg.hasFDerivAt)]
  rfl

/-- `{f − g/2, b} = {f, b} − {g, b} / 2` at a point of differentiability. -/
private theorem pb_sub_half_left {f g b : Phase d → ℝ} {y : Phase d}
    (hf : DifferentiableAt ℝ f y) (hg : DifferentiableAt ℝ g y) :
    pb (fun z => f z - g z / 2) b y = pb f b y - pb g b y / 2 := by
  have he : (fun z => f z - g z / 2) = fun z => f z - (1 / 2 : ℝ) * g z := by
    funext z; ring
  have hd : HasFDerivAt (fun z => f z - (1 / 2 : ℝ) * g z)
      (fderiv ℝ f y - (1 / 2 : ℝ) • fderiv ℝ g y) y :=
    hf.hasFDerivAt.sub (hg.hasFDerivAt.const_mul (1 / 2 : ℝ))
  rw [he, pb_of_hasFDerivAt hd]
  show fderiv ℝ f y (hamiltonianVectorField b y) -
      (1 / 2 : ℝ) * fderiv ℝ g y (hamiltonianVectorField b y) = _
  unfold pb
  ring

/-- The `k`-th action component of `X_{h + P}` for an angle-independent `h`: `−D_k P`. -/
private theorem hamiltonianVectorField_add_snd {h P : Phase d → ℝ} {k : Fin d} {y : Phase d}
    (hh : ∀ y, fderiv ℝ h y (angleDir k) = 0) (hhd : DifferentiableAt ℝ h y)
    (hPd : DifferentiableAt ℝ P y) :
    (hamiltonianVectorField (fun z => h z + P z) y).2 k = -dirDeriv (angleDir k) P y := by
  rw [hamiltonianVectorField_snd]
  show -fderiv ℝ (h + P) y (angleDir k) = _
  rw [(hhd.hasFDerivAt.add hPd.hasFDerivAt).fderiv]
  show -(fderiv ℝ h y (angleDir k) + fderiv ℝ P y (angleDir k)) = _
  rw [hh y, zero_add]
  rfl

/-- **The order-1 Lie remainder identity.** For `H = h + P` with `h` independent of the angle `k`,
and `h, P, χ₁` smooth on an open `O`: `{I_k + D_k χ₁, H} = −D_k r₁ + {D_k χ₁, P}` on `O`. -/
theorem pb_approxIntegral₁ {k : Fin d} {h P χ₁ : Phase d → ℝ} {O : Set (Phase d)}
    (hO : IsOpen O) (hh : ∀ y, fderiv ℝ h y (angleDir k) = 0)
    (hhs : ContDiffOn ℝ ∞ h O) (hPs : ContDiffOn ℝ ∞ P O) (h₁ : ContDiffOn ℝ ∞ χ₁ O)
    {w : Phase d} (hw : w ∈ O) :
    pb (approxIntegral₁ k χ₁) (fun y => h y + P y) w =
      -dirDeriv (angleDir k) (residual₁ h P χ₁) w + pb (dirDeriv (angleDir k) χ₁) P w := by
  have sh := hhs.contDiffAt (hO.mem_nhds hw)
  have sP := hPs.contDiffAt (hO.mem_nhds hw)
  have s1 := h₁.contDiffAt (hO.mem_nhds hw)
  have sD1 := contDiffAt_dirDeriv (angleDir k) s1
  have sc := contDiffAt_pb s1 sh
  have hF : HasFDerivAt (approxIntegral₁ k χ₁)
      (momCLM k + fderiv ℝ (dirDeriv (angleDir k) χ₁) w) w :=
    (hasFDerivAt_mom k w).add (differentiableAt_of_contDiffAt sD1).hasFDerivAt
  have e0 : pb (approxIntegral₁ k χ₁) (fun y => h y + P y) w =
      (hamiltonianVectorField (fun y => h y + P y) w).2 k +
        pb (dirDeriv (angleDir k) χ₁) (fun y => h y + P y) w := by
    rw [pb_of_hasFDerivAt hF]
    rfl
  have e1 := hamiltonianVectorField_add_snd hh (differentiableAt_of_contDiffAt sh)
    (differentiableAt_of_contDiffAt sP) (k := k) (y := w)
  have e2 := pb_add_right (a := dirDeriv (angleDir k) χ₁) (differentiableAt_of_contDiffAt sh)
    (differentiableAt_of_contDiffAt sP)
  have e3 := pb_dirDeriv_left hh s1 sh
  have e4 : dirDeriv (angleDir k) (residual₁ h P χ₁) w =
      dirDeriv (angleDir k) P w - dirDeriv (angleDir k) (pb χ₁ h) w :=
    dirDeriv_sub (angleDir k) (differentiableAt_of_contDiffAt sP)
      (differentiableAt_of_contDiffAt sc)
  rw [e0, e1, e2, e3, e4]
  ring

/-- **The order-2 Lie remainder identity** (design §6.2). For `H = h + P` with `h` independent of
the angle `k`, and `h, P, χ₁, χ₂` smooth on an open `O`, at every `w ∈ O`:
`{F, H} = −D_k r₁ − D_k r₂ + {D_k r₁, χ₁} + {D_k χ₂, P} − ½ {{D_k χ₁, χ₁}, P}`
for `F = approxIntegral₂ k χ₁ χ₂`. -/
theorem pb_approxIntegral₂ {k : Fin d} {h P χ₁ χ₂ : Phase d → ℝ} {O : Set (Phase d)}
    (hO : IsOpen O) (hh : ∀ y, fderiv ℝ h y (angleDir k) = 0)
    (hhs : ContDiffOn ℝ ∞ h O) (hPs : ContDiffOn ℝ ∞ P O)
    (h₁ : ContDiffOn ℝ ∞ χ₁ O) (h₂ : ContDiffOn ℝ ∞ χ₂ O) {w : Phase d} (hw : w ∈ O) :
    pb (approxIntegral₂ k χ₁ χ₂) (fun y => h y + P y) w =
      -dirDeriv (angleDir k) (residual₁ h P χ₁) w - dirDeriv (angleDir k) (residual₂ h P χ₁ χ₂) w +
        pb (dirDeriv (angleDir k) (residual₁ h P χ₁)) χ₁ w + pb (dirDeriv (angleDir k) χ₂) P w -
        pb (pb (dirDeriv (angleDir k) χ₁) χ₁) P w / 2 := by
  -- smoothness on `O`
  have sm : ∀ {f : Phase d → ℝ}, ContDiffOn ℝ ∞ f O → ∀ y ∈ O, ContDiffAt ℝ ∞ f y :=
    fun hf y hy => hf.contDiffAt (hO.mem_nhds hy)
  have sh := sm hhs
  have sP := sm hPs
  have s1 := sm h₁
  have s2 := sm h₂
  have dd : ∀ {f : Phase d → ℝ} {y : Phase d}, ContDiffAt ℝ ∞ f y → DifferentiableAt ℝ f y :=
    fun hf => differentiableAt_of_contDiffAt hf
  have sD1 : ∀ y ∈ O, ContDiffAt ℝ ∞ (dirDeriv (angleDir k) χ₁) y :=
    fun y hy => contDiffAt_dirDeriv _ (s1 y hy)
  have sD2 : ∀ y ∈ O, ContDiffAt ℝ ∞ (dirDeriv (angleDir k) χ₂) y :=
    fun y hy => contDiffAt_dirDeriv _ (s2 y hy)
  have sc : ∀ y ∈ O, ContDiffAt ℝ ∞ (pb χ₁ h) y := fun y hy => contDiffAt_pb (s1 y hy) (sh y hy)
  have sc2 : ∀ y ∈ O, ContDiffAt ℝ ∞ (pb χ₂ h) y := fun y hy => contDiffAt_pb (s2 y hy) (sh y hy)
  have sB : ∀ y ∈ O, ContDiffAt ℝ ∞ (pb (dirDeriv (angleDir k) χ₁) χ₁) y :=
    fun y hy => contDiffAt_pb (sD1 y hy) (s1 y hy)
  have sDP : ∀ y ∈ O, ContDiffAt ℝ ∞ (dirDeriv (angleDir k) P) y :=
    fun y hy => contDiffAt_dirDeriv _ (sP y hy)
  have sDc : ∀ y ∈ O, ContDiffAt ℝ ∞ (dirDeriv (angleDir k) (pb χ₁ h)) y :=
    fun y hy => contDiffAt_dirDeriv _ (sc y hy)
  have sg : ∀ y ∈ O, ContDiffAt ℝ ∞ (fun z => P z - pb χ₁ h z / 2) y :=
    fun y hy => (sP y hy).sub ((sc y hy).div_const 2)
  have hOw : O ∈ 𝓝 w := hO.mem_nhds hw
  -- the left side, through the derivative of `F`
  have hF : HasFDerivAt (approxIntegral₂ k χ₁ χ₂)
      (momCLM k + fderiv ℝ (dirDeriv (angleDir k) χ₁) w +
        fderiv ℝ (dirDeriv (angleDir k) χ₂) w -
        (1 / 2 : ℝ) • fderiv ℝ (pb (dirDeriv (angleDir k) χ₁) χ₁) w) w := by
    have he : approxIntegral₂ k χ₁ χ₂ = fun y => y.2 k + dirDeriv (angleDir k) χ₁ y +
        dirDeriv (angleDir k) χ₂ y - (1 / 2 : ℝ) * pb (dirDeriv (angleDir k) χ₁) χ₁ y := by
      funext y; simp only [approxIntegral₂]; ring
    rw [he]
    exact (((hasFDerivAt_mom k w).add (dd (sD1 w hw)).hasFDerivAt).add
      (dd (sD2 w hw)).hasFDerivAt).sub ((dd (sB w hw)).hasFDerivAt.const_mul (1 / 2 : ℝ))
  have e0 : pb (approxIntegral₂ k χ₁ χ₂) (fun y => h y + P y) w =
      (hamiltonianVectorField (fun y => h y + P y) w).2 k +
        pb (dirDeriv (angleDir k) χ₁) (fun y => h y + P y) w +
        pb (dirDeriv (angleDir k) χ₂) (fun y => h y + P y) w -
        (1 / 2 : ℝ) * pb (pb (dirDeriv (angleDir k) χ₁) χ₁) (fun y => h y + P y) w := by
    rw [pb_of_hasFDerivAt hF]
    rfl
  have e1 := hamiltonianVectorField_add_snd hh (dd (sh w hw)) (dd (sP w hw)) (k := k)
  have e2 := pb_add_right (a := dirDeriv (angleDir k) χ₁) (dd (sh w hw)) (dd (sP w hw))
  have e3 := pb_add_right (a := dirDeriv (angleDir k) χ₂) (dd (sh w hw)) (dd (sP w hw))
  have e4 := pb_add_right (a := pb (dirDeriv (angleDir k) χ₁) χ₁) (dd (sh w hw)) (dd (sP w hw))
  -- `{D_k χ, h} = D_k {χ, h}`, on `O`
  have e5 := pb_dirDeriv_left hh (s1 w hw) (sh w hw)
  have e6 := pb_dirDeriv_left hh (s2 w hw) (sh w hw)
  -- Jacobi for `{{D_k χ₁, χ₁}, h}`, then `{D_k χ₁, h} = D_k {χ₁, h}` near `w`
  have e7 := pb_jacobi (sD1 w hw) (s1 w hw) (sh w hw)
  have e8 : pb (pb (dirDeriv (angleDir k) χ₁) h) χ₁ w =
      pb (dirDeriv (angleDir k) (pb χ₁ h)) χ₁ w :=
    pb_congr_left (Filter.mem_of_superset hOw fun y hy => pb_dirDeriv_left hh (s1 y hy) (sh y hy))
  -- the residuals
  have e9 : dirDeriv (angleDir k) (residual₁ h P χ₁) w =
      dirDeriv (angleDir k) P w - dirDeriv (angleDir k) (pb χ₁ h) w :=
    dirDeriv_sub _ (dd (sP w hw)) (dd (sc w hw))
  have e10 : pb (dirDeriv (angleDir k) (residual₁ h P χ₁)) χ₁ w =
      pb (dirDeriv (angleDir k) P) χ₁ w - pb (dirDeriv (angleDir k) (pb χ₁ h)) χ₁ w := by
    have hev : dirDeriv (angleDir k) (residual₁ h P χ₁) =ᶠ[𝓝 w]
        fun y => dirDeriv (angleDir k) P y - dirDeriv (angleDir k) (pb χ₁ h) y :=
      Filter.mem_of_superset hOw fun y hy => dirDeriv_sub _ (dd (sP y hy)) (dd (sc y hy))
    rw [pb_congr_left hev]
    exact pb_sub_left (dd (sDP w hw)) (dd (sDc w hw))
  have e11 : dirDeriv (angleDir k) (residual₂ h P χ₁ χ₂) w =
      dirDeriv (angleDir k) (pb (fun z => P z - pb χ₁ h z / 2) χ₁) w -
        dirDeriv (angleDir k) (pb χ₂ h) w :=
    dirDeriv_sub _ (dd (contDiffAt_pb (sg w hw) (s1 w hw))) (dd (sc2 w hw))
  have e12 := dirDeriv_pb (sg w hw) (s1 w hw) (angleDir k)
  have e13 : pb (dirDeriv (angleDir k) (fun z => P z - pb χ₁ h z / 2)) χ₁ w =
      pb (dirDeriv (angleDir k) P) χ₁ w - pb (dirDeriv (angleDir k) (pb χ₁ h)) χ₁ w / 2 := by
    have hev : dirDeriv (angleDir k) (fun z => P z - pb χ₁ h z / 2) =ᶠ[𝓝 w]
        fun y => dirDeriv (angleDir k) P y - dirDeriv (angleDir k) (pb χ₁ h) y / 2 :=
      Filter.mem_of_superset hOw fun y hy => dirDeriv_sub_half _ (dd (sP y hy)) (dd (sc y hy))
    rw [pb_congr_left hev]
    exact pb_sub_half_left (dd (sDP w hw)) (dd (sDc w hw))
  have e14 : pb (fun z => P z - pb χ₁ h z / 2) (dirDeriv (angleDir k) χ₁) w =
      pb P (dirDeriv (angleDir k) χ₁) w - pb (pb χ₁ h) (dirDeriv (angleDir k) χ₁) w / 2 :=
    pb_sub_half_left (dd (sP w hw)) (dd (sc w hw))
  -- antisymmetry
  have e15 := pb_antisymm (dirDeriv (angleDir k) χ₁) P w
  have e16 := pb_antisymm (dirDeriv (angleDir k) χ₁) (pb χ₁ h) w
  rw [e0, e1, e2, e3, e4, e9, e10, e11, e12, e13, e14]
  linarith [e5, e6, e7, e8, e15, e16]

/-- **The bound a cell check certifies** (design §6.3): term-by-term bounds on the right side of the
order-2 identity bound the rate `|{F, H}|`. -/
theorem abs_pb_approxIntegral₂_le {k : Fin d} {h P χ₁ χ₂ : Phase d → ℝ} {O : Set (Phase d)}
    (hO : IsOpen O) (hh : ∀ y, fderiv ℝ h y (angleDir k) = 0)
    (hhs : ContDiffOn ℝ ∞ h O) (hPs : ContDiffOn ℝ ∞ P O)
    (h₁ : ContDiffOn ℝ ∞ χ₁ O) (h₂ : ContDiffOn ℝ ∞ χ₂ O) {w : Phase d} (hw : w ∈ O)
    {a₁ a₂ a₃ a₄ a₅ : ℝ}
    (b₁ : |dirDeriv (angleDir k) (residual₁ h P χ₁) w| ≤ a₁)
    (b₂ : |dirDeriv (angleDir k) (residual₂ h P χ₁ χ₂) w| ≤ a₂)
    (b₃ : |pb (dirDeriv (angleDir k) (residual₁ h P χ₁)) χ₁ w| ≤ a₃)
    (b₄ : |pb (dirDeriv (angleDir k) χ₂) P w| ≤ a₄)
    (b₅ : |pb (pb (dirDeriv (angleDir k) χ₁) χ₁) P w| ≤ a₅) :
    |pb (approxIntegral₂ k χ₁ χ₂) (fun y => h y + P y) w| ≤ a₁ + a₂ + a₃ + a₄ + a₅ / 2 := by
  rw [pb_approxIntegral₂ hO hh hhs hPs h₁ h₂ hw]
  rw [abs_le] at b₁ b₂ b₃ b₄ b₅ ⊢
  constructor <;> linarith [b₁.1, b₁.2, b₂.1, b₂.2, b₃.1, b₃.2, b₄.1, b₄.2, b₅.1, b₅.2]

/-- The range of `F − I_k`: by definition, `D_k χ₁ + D_k χ₂ − ½ {D_k χ₁, χ₁}`. -/
theorem approxIntegral₂_sub (k : Fin d) (χ₁ χ₂ : Phase d → ℝ) (y : Phase d) :
    approxIntegral₂ k χ₁ χ₂ y - y.2 k = dirDeriv (angleDir k) χ₁ y +
      dirDeriv (angleDir k) χ₂ y - pb (dirDeriv (angleDir k) χ₁) χ₁ y / 2 := by
  unfold approxIntegral₂
  ring

end KAM.Application.LambdaDrift

end
