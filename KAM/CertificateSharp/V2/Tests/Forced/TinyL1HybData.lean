/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyWitness
public import KAM.CertificateSharp.V2.RouteAL1Core
public import KAM.CertificateSharp.Hybrid.RestartQ

/-!
# The forced toy `Tiny` through the ℓ¹ entry and the hybrid restart (data)

Emitted by `scripts/certifier/forced/forced_l1hyb.py Tiny` (the producers `forced_l1.py`,
`forced_hybrid.py`; fixtures `scripts/certifier/fixtures/forced-toy/Tiny_l1.json`,
`Tiny_hybrid.json`):

* `msF`, `mvF`: the compositions of the first derivatives of `H` and of `H` along `K` at the full
  stage (those of `checkInvariance` and `checkEnergy`), literals of the Python mirror, re-proved
  by their own kernel runs and read by `checkL1E` and `hybCompOk`;
* `l1Wit`: route A with the ℓ¹ entry on the strip `ρ' = 1/10` (`L1.routeAL1`), `X⋆ = 1830`;
* `hybWit`: the hybrid restart (`Hybrid.routeHybrid`) with the Newton step `hybDK` of a finer
  Picard torus (2 terms), restarted error `5.36e-15` against the base `4.1e-12`, and the
  route-A′ run of `refinedWitR` at the restart numbers (`ρ₁ = ρ`: the base run's sites).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

def msF_0 : CertModel FB :=
  ⟨1, ⟨[ft (-2) (-2) 0 1013935145229165, ft (-2) (-1) 0 29928547687251668,
    ft (-2) 0 0 14710790057318543, ft (-1) (-1) 0 (-7922816251317046211617),
    ft (-1) 0 0 (-3961408125658523105809), ft 0 (-1) 0 (-28914612542022505), ft 0 0 0 (-1),
    ft 0 1 0 28914612542022503, ft 1 0 0 3961408125658523105808, ft 1 1 0 7922816251317046211616,
    ft 2 0 0 (-14710790057318544), ft 2 1 0 (-29928547687251670), ft 2 2 0 (-1013935145229166)]⟩,
    ⟨66292172118507⟩⟩

def msF_1 : CertModel FB :=
  ⟨1, ⟨[ft (-2) (-2) 0 1013935145229165, ft (-2) (-1) 0 29421580114637086,
    ft (-1) (-1) 0 (-7922816251317046211617), ft 0 (-1) 0 (-29421580114637087), ft 0 0 0 0,
    ft 0 1 0 29421580114637086, ft 1 1 0 7922816251317046211616, ft 2 1 0 (-29421580114637087),
    ft 2 2 0 (-1013935145229166)]⟩,
    ⟨53985214395079⟩⟩

def msF_2 : CertModel FB :=
  ⟨0, ⟨[ft (-2) (-1) 38973091048052686 0, ft (-2) 0 (-63389044357667609) 0,
    ft (-1) (-1) (-8962824246025385806208) 0, ft (-1) 0 34139549870706519354982 0,
    ft 0 (-1) (-28914612542022504) 0, ft 0 0 (-9193298914542448669155068535) 0,
    ft 0 1 (-28914612542022504) 0, ft 1 0 34139549870706519354982 0,
    ft 1 1 (-8962824246025385806208) 0, ft 2 0 (-63389044357667609) 0,
    ft 2 1 38973091048052686 0]⟩,
    ⟨722⟩⟩

def msF_3 : CertModel FB :=
  ⟨0, ⟨[ft 0 0 79228162514264337593543950336 0]⟩,
    ⟨4⟩⟩

/-- the composed first derivatives along `K` (full stage) -/
def msF : List (CertModel FB) :=
  [msF_0, msF_1, msF_2, msF_3]

def mvF_0 : CertModel FB :=
  ⟨0, ⟨[ft (-4) (-2) 9585 0, ft (-4) (-1) (-31182) 0, ft (-4) 0 25358 0,
    ft (-3) (-2) (-4408898987) 0, ft (-3) (-1) 23964567507 0, ft (-3) 0 (-27314446940) 0,
    ft (-2) (-2) 66548347415474 0, ft (-2) (-1) 23132 0, ft (-2) 0 (-14226) 0, ft (-2) 1 23134 0,
    ft (-1) (-2) 3271016039 0, ft (-1) (-1) (-105053332258) 0, ft (-1) 0 (-83146103758) 0,
    ft (-1) 1 (-5288359340) 0, ft 0 (-2) 5276 0, ft 0 (-1) (-31184) 0, ft 0 0 (-3) 0,
    ft 0 1 (-31184) 0, ft 0 2 5276 0, ft 1 (-1) (-5288359340) 0, ft 1 0 (-83146103758) 0,
    ft 1 1 (-105053332258) 0, ft 1 2 3271016039 0, ft 2 (-1) 23134 0, ft 2 0 (-14226) 0,
    ft 2 1 23132 0, ft 2 2 66548347415474 0, ft 3 0 (-27314446940) 0, ft 3 1 23964567507 0,
    ft 3 2 (-4408898987) 0, ft 4 0 25358 0, ft 4 1 (-31182) 0, ft 4 2 9585 0]⟩,
    ⟨66292172126714⟩⟩

/-- the composed energy along `K` (full stage) -/
def mvF : List (CertModel FB) :=
  [mvF_0]

/-- The ℓ¹ claim (`checkL1Claim`). -/
def l1Claim : L1.L1Claim :=
  { W1 := ⟨((1 : ℚ) / 10), ((468614054363 : ℚ) / 250000000000)⟩, WT := ⟨((401 : ℚ) / 4800),
    ((105643940417 : ℚ) / 62500000000)⟩, aE := ((29781 : ℚ) / 10000000000000000),
    aLt := ((5001 : ℚ) / 5000), aNt := ((10139 : ℚ) / 10000), nuK := ((5001 : ℚ) / 5000),
    nuN := ((10139 : ℚ) / 10000), t1 := ((2521 : ℚ) / 2500) }

/-- The run of the ℓ¹ entry on the strip `ρ'` (tight caps). -/
def l1Run : FrozenWit :=
  { Xs := (1830 : ℚ), kp := 3, th := ((1 : ℚ) / 8), c := [((1213 : ℚ) / 100000),
    ((117 : ℚ) / 10000), ((47 : ℚ) / 4000)], cbar := [((2217 : ℚ) / 100000), ((1673 : ℚ) / 100000),
    ((1307 : ℚ) / 100000)], ctail := ((8165357 : ℚ) / 100000000),
    sB := ((102002417 : ℚ) / 100000000), sT := ((23012551 : ℚ) / 20000000),
    sLt := ((50050807 : ℚ) / 50000000), sN := ((800823 : ℚ) / 800000),
    sNt := ((2502599 : ℚ) / 2500000), t := ((100141499 : ℚ) / 100000000), J := 20 }

/-- The certified small-divisor sites of the bites of the strip `ρ'`. -/
def l1Sites : List (Option BiteWit × Option BiteWit) :=
  [(some ⟨((101849 : ℚ) / 125000), 7, 8, ((267691 : ℚ) / 500)⟩, some ⟨((285179 : ℚ) / 1000000), 4,
    8, ((48473 : ℚ) / 1000)⟩), (some ⟨((903561 : ℚ) / 1000000), 8, 8, ((199383 : ℚ) / 100)⟩,
    some ⟨((265187 : ℚ) / 500000), 5, 8, ((107703 : ℚ) / 1000)⟩), (some ⟨((237877 : ℚ) / 250000), 9,
    8, ((803547 : ℚ) / 100)⟩, some ⟨((723293 : ℚ) / 1000000), 6, 8, ((250349 : ℚ) / 1000)⟩)]

/-- C6's refined run on the strip `ρ'`, with the base claim. -/
def l1Base : RefinedWit :=
  { core := l1Run, R := Rclaim, κ := ((1000000 : ℚ) / 1000001), sites := l1Sites }

/-- The entry record. -/
def l1Entry : KAM.Sharp2.Examples.EntryQ :=
  { aN := ((45407 : ℚ) / 62500), aL := ((46029 : ℚ) / 62500), t1 := ((2521 : ℚ) / 2500),
    tR := ((1001 : ℚ) / 1000), G0 := ((15991 : ℚ) / 12500), Gρ := ((733199 : ℚ) / 1000000),
    frame := some (((5001 : ℚ) / 5000), ((10139 : ℚ) / 10000)), ei := ((3679 : ℚ) / 10000) }

/-- **The witness of route A with the ℓ¹ entry.** -/
def l1Wit : L1.L1Wit :=
  { base := l1Base, L := l1Claim, E := l1Entry, g0 := ⟨37, ((2818 : ℚ) / 3125),
    ((319819 : ℚ) / 250000)⟩, gρ := ⟨2, ((266879 : ℚ) / 500000), ((366599 : ℚ) / 500000)⟩ }

/-- The Newton step `ΔK̂` (`K' - K̂`, `K'` the finer Picard torus). -/
def hybDK : CertEmbedding ℚ :=
  ⟨[-1, 0], [⟨(0 : ℚ), [([2, 2], ⟨(0 : ℚ),
    ((-324399950126887 : ℚ) / 79228162514264337593543950336)⟩)]⟩, ⟨(0 : ℚ), []⟩], [0, 0], [⟨(0 : ℚ),
    [([2, 2], ⟨((286757960022141 : ℚ) / 39614081257132168796771975168), (0 : ℚ)⟩)]⟩,
    ⟨((-1 : ℚ) / 19807040628566084398385987584), []⟩]⟩

/-- The step claims `(S1)–(S7)`. -/
def hybClaims : Hybrid.StepNumQ :=
  { d0 := ((67011 : ℚ) / 200000000000000000), dinf := ((37353 : ℚ) / 2500000000000000000),
    d1 := ((168417 : ℚ) / 20000000000000000), d1t := ((229473 : ℚ) / 50000000000000000),
    d0R := ((144791 : ℚ) / 10000000000000000000), d1R := ((181949 : ℚ) / 500000000000000000),
    d1tR := ((198329 : ℚ) / 1000000000000000000), lE := ((536103 : ℚ) / 100000000000000000000),
    dE0 := ((1987878787879 : ℚ) / 5000000000000000000000), o0 := ((125393 : ℚ) / 50000000000000000),
    dE0R := ((1987878787879 : ℚ) / 5000000000000000000000),
    o0R := ((181997 : ℚ) / 1000000000000000000), o1 := ((593019 : ℚ) / 1000000000000000000000),
    o1R := ((245543 : ℚ) / 5000000000000000000000) }

/-- The step data (format v1 `step`). -/
def hybStep : Hybrid.HybStep :=
  { dK := hybDK, s1 := ((1000001 : ℚ) / 1000000), W1 := ⟨((1 : ℚ) / 8),
    ((1096640120341 : ℚ) / 500000000000)⟩, Winf := ⟨((1 : ℚ) / 800),
    ((40315396237 : ℚ) / 40000000000)⟩, WT := ⟨((167 : ℚ) / 1600),
    ((1926697772439 : ℚ) / 1000000000000)⟩, cl := hybClaims,
    lH := ((836809 : ℚ) / 1000000000000000000000), dw := (0 : ℚ) }

/-- The restart parameters (format v1 `restart.params1`). -/
def hybParams1 : CertParams :=
  { tau := 1, rho := ((1 : ℚ) / 8), rhoInf := ((1 : ℚ) / 800), M := ((57 : ℚ) / 50),
    σK := ((20599999980168417 : ℚ) / 20000000000000000), σB := ((514999999507 : ℚ) / 500000000000),
    σT := ((231999999909 : ℚ) / 200000000000), μ := ((9999999 : ℚ) / 1000000000),
    γbar := ((100000 : ℚ) / 1000001), σω := (2 : ℚ), nuRay := ((1 : ℚ) / 10000000),
    γ := ((100000 : ℚ) / 1000001), s := ((1000001 : ℚ) / 1000000),
    err := ((2681 : ℚ) / 500000000000000000), E0 := (0 : ℚ),
    disp := ((6553 : ℚ) / 10000000000000000) }

/-- The transferred refined claim of the restart (format v1 `witness1.base.R`). -/
def hybClaim1 : RefClaim :=
  { dh := ((141 : ℚ) / 125), dx := ((1001 : ℚ) / 1000), d2x := ((1169 : ℚ) / 1000000),
    d2h := ((1001 : ℚ) / 1000), bL := ((200200000001 : ℚ) / 200000000000),
    bN := ((1001000000023 : ℚ) / 1000000000000), bNt := ((1001000000019 : ℚ) / 1000000000000),
    bT := ((1001000000511 : ℚ) / 1000000000000) }

/-- The restarted route-A′ run (format v1 `restart.witness1`): the base run `refinedWitR` with the
transferred claim (its sites are the base run's). -/
def hybWit1 : RefinedWitR :=
  { refinedWitR with base := { refinedWitR.base with R := hybClaim1 } }

/-- **The hybrid witness.** -/
def hybWit : Hybrid.HybWit :=
  { R0 := Rclaim, step := hybStep, p1 := hybParams1, w1 := hybWit1 }

end KAM.CertificateSharp.V2.Forced.Tiny

end
