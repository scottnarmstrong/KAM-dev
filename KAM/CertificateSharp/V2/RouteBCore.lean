/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.RouteBCert
public import KAM.CertificateSharp.V2.RouteACore
public import KAM.CertificateSharp.V2.RefinedFacts

/-!
# The tests of route B

The numbers of a route-B run (`KAM.Sharp2.RouteB.NumB`) split into those the theorem fixes from the
certificate's parameters (`τ, ρ, ρ∞, γ̄`, the cap `σ_K - μ/2` of `DK`, the iso fields
`Θ = σω |ω*|`, `y₀ = M σ_N`) and those the certificate chooses, `RunBWit`: `X⋆`, the schedule
ratio `a`, the decay bound `ȳ`, the prefix, the ratios, the budgets, the stage-0 weights, the
small-divisor constants and the caps. `RunBWit.num` assembles them, at the Hamiltonian data
`M₁, M₂, M_h2` (frozen: `M`; refined: the claimed bounds), with `c_Th = 2M₁`, `c_DTh = 2M₂`.

* `finalB`: the smallness `c1B e < γ⁴ ρ^{4τ}`, the displacements `c2B, c3B · e ≤ disp γ² ρ^{2τ}` and
  the room of the ray, for the route-B branch `iso_g1_branch_B`;
* `finalBF`: the same with `max {C₂♯, C₃♯}` added, for the wrapper `iso_g1_v2B_frozen`;
* `refinedBCore`, `frozenBCore`: the numerical tests of the two variants. As for route A, `Θ` is
  the rational `σω · boxNormUp box`, and the theorems are applied at `σh = Θ/‖ω*‖ ≥ σω`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2

open KAM KAM.Certificate KAM.Sharp2 KAM.Sharp2.RouteB KAM.Sharp.Engine

/-- The numbers of a route-B run chosen by the certificate. -/
structure RunBWit where
  /-- The majorant `X⋆` of the initial normalized error. -/
  Xs : ℚ
  /-- The number of prefix stages. -/
  kp : ℕ
  /-- The schedule ratio `a > 1` and the decay bound `ȳ ∈ (0, 1)`. -/
  a : ℚ
  ybar : ℚ
  /-- The ratios `ϑ, ϑ_ξ, ϑ_Ω, q, ϑ_N, ϑ_ω`. -/
  θ : ℚ
  θξ : ℚ
  θΩ : ℚ
  q : ℚ
  θN : ℚ
  θω : ℚ
  /-- The torsion slack `t_s` and the local torsion budget `b_F`. -/
  ts : ℚ
  bF : ℚ
  /-- Option L10. -/
  selfcons : Bool
  /-- The stage-0 weights. -/
  lam0 : ℚ
  lamW0 : ℚ
  ePer0 : ℚ
  /-- The small-divisor constants: at `δ_s`, at the split bite, at `min r_s 1`, in the tail. -/
  c : List ℚ
  c' : List ℚ
  cbar : List ℚ
  ctail : ℚ
  cbtail : ℚ
  /-- The caps of `|B|`, `|⟨T⟩⁻¹|`, `|Lᵀ|`, `|N|`, `|Nᵀ|`. -/
  sB : ℚ
  sT : ℚ
  sLt : ℚ
  sN : ℚ
  sNt : ℚ
  /-- The number of explicit terms of `ζ(2, 2^τ)` in the classical constants. -/
  J : ℕ

/-- The rational numbers of the run, at the Hamiltonian data `M₁, M₂, M_h2`. -/
def RunBWit.num (w : RunBWit) (p : CertParams) (box : FreqBox) (M1 M2 Mh2 : ℚ) : NumBQ :=
  { τ := p.tau, ρ := p.rho, ρinf := p.rhoInf, γb := p.γbar, M1 := M1, M2 := M2, cTh := 2 * M1,
    cDTh := 2 * M2, sK := p.σK - p.μ / 2, sLt := w.sLt, sB := w.sB, sN := w.sN, sNt := w.sNt,
    sT := w.sT, ts := w.ts, bF := w.bF, θ := w.θ, θξ := w.θξ, θΩ := w.θΩ, q := w.q, θN := w.θN,
    θω := w.θω, a := w.a, ybar := w.ybar, kp := w.kp, c := w.c, c' := w.c', cbar := w.cbar,
    ctail := w.ctail, cbtail := w.cbtail, selfcons := w.selfcons, lam0 := w.lam0,
    lamW0 := w.lamW0, ePer0 := w.ePer0, iso := true, Θ := p.σω * boxNormUp box,
    y0 := p.M * w.sN, Mh2 := Mh2 }

/-- The final comparisons of the route-B branch. -/
def finalB (Q : NumBQ) (n : ℕ) (p : CertParams) (box : FreqBox) (iLt iNt Xs : ℚ) : Bool :=
  decide (Q.c1Q iLt iNt Xs * p.err < p.γ ^ 4 * p.rho ^ (4 * p.tau)) &&
    decide (max (Q.c2Q n iLt iNt Xs) (Q.c3Q n iLt iNt Xs) * p.err ≤
      p.disp * (p.γ ^ 2 * p.rho ^ (2 * p.tau))) &&
    decide (p.disp < (p.σω - p.s) * freqNormLo box)

/-- The final comparisons of the wrapper `iso_g1_v2B_frozen`: `C₂♯`, `C₃♯` enter. -/
def finalBF (Q : NumBQ) (n : ℕ) (p : CertParams) (box : FreqBox) (iLt iNt Xs : ℚ) : Bool :=
  finalB Q n p box iLt iNt Xs &&
    decide (max (sharpIsoC2Q n p.tau (cRRQ n p.tau) p.M p.σK p.σB p.σT p.γbar p.rho p.rhoInf)
        (sharpIsoC3Q n p.tau (cRRQ n p.tau) p.M p.σK p.σB p.σT p.γbar p.rho p.rhoInf) * p.err ≤
      p.disp * (p.γ ^ 2 * p.rho ^ (2 * p.tau)))

/-- The witness of route B at the refined data. -/
structure RefinedBWit where
  /-- The numbers of the run. -/
  core : RunBWit
  /-- The claimed bounds on `H` and the frame (`bT` is not used by route B). -/
  R : RefClaim
  /-- The last coordinate of the frequency. -/
  κ : ℚ
  /-- The witnesses at `δ_s`, at the split bite and at `min r_s 1`, `s < kp`. -/
  sites : BSites

/-- The rational numbers of the refined run. -/
def RefinedBWit.num (w : RefinedBWit) (p : CertParams) (box : FreqBox) : NumBQ :=
  w.core.num p box w.R.dx w.R.d2x w.R.d2h

/-- The numerical test of route B at the refined data. -/
def refinedBCore (n : ℕ) (p : CertParams) (box : FreqBox) (w : RefinedBWit) : Bool :=
  let Q := w.num p box
  decide (0 < w.core.Xs) && Q.wfOk n && Q.fitsOk w.R.bL w.R.bNt &&
    Q.initOk w.R.bL w.R.bN w.R.bNt p.σT p.μ &&
    Q.okB n (Q.capBQ p.σT p.μ p.nuRay) (NumBQ.initBQ w.R.bL w.R.bN w.R.bNt p.σK p.σB p.μ)
      (p.μ / 2) w.core.Xs &&
    Q.sitesOk n w.core.J box w.κ p.γ w.sites && Q.tailOk n w.core.J &&
    finalB Q n p box w.R.bL w.R.bNt w.core.Xs

/-- The default initial values `defaultInitB` at the parameters. -/
def defaultIB (n : ℕ) (p : CertParams) : ℚ × ℚ × ℚ :=
  (2 * n * (p.σK - p.μ), (p.σK - p.μ) * (p.σB - p.μ), 2 * n * (p.σK - p.μ) * (p.σB - p.μ))

/-- The numerical test of route B at the frozen data: `M₁ = M₂ = M_h2 = M`, the default initial
values, classical constants at every site. -/
def frozenBCore (n : ℕ) (p : CertParams) (box : FreqBox) (w : RunBWit) : Bool :=
  let Q := w.num p box p.M p.M p.M
  let I := defaultIB n p
  decide (0 < w.Xs) && decide (p.μ < p.σK) && decide (p.μ < p.σB) &&
    decide (p.σB - p.μ < w.sB) && Q.wfOk n && Q.fitsOk I.1 I.2.2 &&
    Q.initOk I.1 I.2.1 I.2.2 p.σT p.μ &&
    Q.okB n (Q.capBQ p.σT p.μ p.nuRay) (NumBQ.initBQ I.1 I.2.1 I.2.2 p.σK p.σB p.μ) (p.μ / 2)
      w.Xs &&
    Q.sitesOk n w.J box 0 p.γ [] && Q.tailOk n w.J && finalBF Q n p box I.1 I.2.2 w.Xs

end KAM.CertificateSharp.V2

end
