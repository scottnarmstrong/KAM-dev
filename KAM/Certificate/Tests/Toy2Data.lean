/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Tests.ToyLit

/-!
# Data of the toy certificate T2

Emitted by `scripts/spin_orbit/toy_lean_cert.py` from
`certificates/so-toys/T2.json` (SO-PYALIGN); `toyT2Cert` is the whole certificate.
-/

@[expose] public section

namespace KAM.Certificate

def toyT2Params : CertParams :=
  {tau := 1,rho := 9,rhoInf := 1,M := (297 / 100),σK := (297 / 100),σB := (297 / 100),σT := (297 /
  100),μ := (1 / 100),γbar := (1 / 42),σω := 3,nuRay := (49 / 100),γ := (1 / 42),s := 2,err := (1 /
  3118000000000000000000000000000000000000000),E0 := 0,disp := (94223 /
  5000000000000000000000000000000) }

def toyT2Ham : HamExpr 2 :=
  .add (.action 1) (.mul (.const (1 / 2)) (.pow (.action 0) 2))

def toyT2WeightH : CertWeight :=
  ⟨(451 / 50), (2052684210367924024698804359963 / 500000)⟩

def toyT2Weight : CertWeight :=
  ⟨9, (905142768046211949085245961113 / 250000)⟩

def toyT2Centre : List ℚ :=
  [(toyQ 6082472135954999579392818347337462552470881 6236000000000000000000000000000000000000000),
  (toyQ (toyNeg
  [36996467284668974887099099830234194787836029433882718902704103454427576112118352916161]) (toyNat
  [77775392000000000000000000000000000000000000000000000000000000000000000000000000000000]))]

def toyT2Radius : List ℚ :=
  [(1 / 50), (1 / 50)]

def toyT2Box : FreqBox :=
  [((toyQ 6082472135954999579392818347337462552470881
  12472000000000000000000000000000000000000000), (1 /
  12472000000000000000000000000000000000000000)), ((1 / 2), 0)]

def toyT2Emb : CertEmbedding ℚ :=
  ⟨[0, 0], [⟨0, []⟩, ⟨0, []⟩], [0, 0], [⟨(toyQ 6082472135954999579392818347337462552470881
  6236000000000000000000000000000000000000000), []⟩, ⟨(toyQ (toyNeg
  [36996467284668974887099099830234194787836029433882718902704103454427576112118352916161]) (toyNat
  [77775392000000000000000000000000000000000000000000000000000000000000000000000000000000])), []⟩]⟩

def toyT2Wit : Witnesses ℚ :=
  ⟨[], [], []⟩

def toyT2GramInv : List (List (CertPoly ℚ)) :=
  [[⟨[([0, 0], ⟨1, 0⟩)]⟩, ⟨[]⟩], [⟨[]⟩, ⟨[([0, 0], ⟨1, 0⟩)]⟩]]

def toyT2TorsInv : List (List (CC ℚ)) :=
  [[⟨1, 0⟩, ⟨(toyQ (-6082472135954999579392818347337462552470881)
  6236000000000000000000000000000000000000000), 0⟩, ⟨0, 0⟩], [⟨(toyQ
  (-6082472135954999579392818347337462552470881) 6236000000000000000000000000000000000000000), 0⟩,
  ⟨(toyQ (toyPos
  [36996467284668974887099099830234194787836029433882718902704103454427576112118352916161]) (toyNat
  [38887696000000000000000000000000000000000000000000000000000000000000000000000000000000])), 0⟩,
  ⟨1, 0⟩], [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

def toyT2CfgFull : ModelConfig ℚ :=
  ⟨1000000, 24, 8, fun _ _ => none, []⟩

def toyT2CfgLow : ModelConfig ℚ :=
  ⟨1000000, 24, 8, fun _ _ => none, []⟩

def toyT2Pi : PiEnclosure ℚ :=
  ⟨(toyQ 3314427442226971084353063282817081764744359895236591237306
  1055015021899892426313124618802400368315005057525634765625), (toyQ
  216697700653013966585122908521505070030082
  351320353613017790980061478122677445326342010498046875), 4, 4⟩

/-- lower end of the enclosure of `5^(1/2)` -/
def toyT2RootLo : ℚ :=
  (toyQ 27950849718747371205114670859140952943 12500000000000000000000000000000000000)

/-- upper end of the enclosure of `5^(1/2)` -/
def toyT2RootHi : ℚ :=
  (toyQ 2236067977499789696409173668731276235441 1000000000000000000000000000000000000000)

def toyT2AlgCoeffs : List (List ℚ) :=
  [[(3039 / 6236), (1 / 6236)], [(1 / 2)]]

/-- The whole certificate. -/
def toyT2Cert : TorusCertificate 2 ℚ where
  params := toyT2Params
  ham := toyT2Ham
  weightH := toyT2WeightH
  centre := toyT2Centre
  radius := toyT2Radius
  freqBox := toyT2Box
  emb := toyT2Emb
  weight := toyT2Weight
  wit := toyT2Wit
  gramInv := toyT2GramInv
  torsInv := toyT2TorsInv
  cfgFull := toyT2CfgFull
  cfgLow := toyT2CfgLow
  piEnc := toyT2Pi
  expHalvings := 8
  expOrder := 24

end KAM.Certificate
