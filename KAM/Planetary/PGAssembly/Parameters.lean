/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.Scales
public import KAM.Planetary.PGMeasure.Setting
public import KAM.Planetary.Hamiltonian.Diophantine

/-!
# P Part 5: the geometric parameters (`bpP:p5:params`, `bpP:p5:kset`)

`PGParameters` collects the explicit parameters of `bpP:p5:params`; `params` evaluates them at
`(r, mu)` from the data-only scales `pgScales`. `checkedCore` is the Diophantine part of the inner
core, `pgActionDomain` the joined action domain, `pgD0` the early parameter set of `bpP:p5:kset`
(owned here, after `pgActionDomain`, per design finding F8) and `admissible` the range of `(r, mu)`.
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-PAR.
-/

@[expose] public noncomputable section

namespace KAM.Planetary

variable {a b : ℕ}

/-- All entries are explicit functions of r,mu and data-only chosen constants. -/
structure PGParameters where
  Kbar : ℝ
  t : ℝ
  l1 : ℝ
  l2 : ℝ
  l2top : ℝ
  ell : ℝ
  rho : ℝ
  gammaBar : ℝ
  rhoBar : ℝ
  gamma1 : ℝ
  gamma2 : ℝ
  rhoHat : ℝ
  Ehat : ℝ
  rK : ℝ

def params (d : PGData a b) (r mu : ℝ) : PGParameters :=
  let s := pgScales d
  let p := pgAnalytic d
  let Kbar := 30/pgWidth d*Real.log (1/r)
  let l1 := s.k1*r^(5/2:ℝ)
  let gammaBar := s.G*max (Real.sqrt (p.LP*mu)*Kbar^(pgTau a b+1/2)*r^(-5/2:ℝ))
    (r^(5/2:ℝ)*Kbar^(pgTau a b+1))
  let rhoHat := min (s.k0*r^(5/2:ℝ)/(3*kam_c1 d*(pgK0 d s)^(pgTau a b+1))) (l1/2)
  let Ehat := (kam_c1 d)^2*r^5/rhoHat^2
  ⟨Kbar,Real.sqrt r,l1,r^2/2,r^2/2-2*l1,r^2/2-3*l1,l1/2,gammaBar,
    gammaBar/(2*p.M0*Kbar^(pgTau a b+1)),s.k0*r^(5/2:ℝ),mu*s.k0*r^(5/2:ℝ),rhoHat,Ehat,
    32*Ehat*rhoHat⟩

def checkedCore (d : PGData a b) (r mu : ℝ) : Set (Fin a → ℝ) :=
  innerCore d.V (Real.sqrt r) ∩
    {I | KAM.IsDiophantine (params d r mu).gammaBar (pgTau a b) (fastFrequency d.H0 I)}

def pgActionDomain (d : PGData a b) (r mu : ℝ) : Set (Fin (a+b) → ℝ) :=
  joinedActions (checkedCore d r mu) (actionShell b (params d r mu).l1 (params d r mu).l2top)

/- Owner: KAM/Planetary/PGAssembly/Parameters.lean; after pgActionDomain. -/
def pgD0 (d : PGData a b) (r mu : ℝ) : Set (Fin (a+b) → ℝ) :=
  {J ∈ pgActionDomain d r mu | ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) ∈
    twoScaleDiophantine a b (params d r mu).gamma1 (params d r mu).gamma2 (pgTau a b)}

def admissible (d : PGData a b) (R r mu : ℝ) : Prop :=
  0 < r ∧ r < R ∧ 0 < mu ∧ mu < d.mu0 ∧ mu < r^6/(Real.log (1/r))^(2*pgTau a b+2)

end KAM.Planetary

end
