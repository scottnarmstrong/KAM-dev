/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Powers
public import KAM.EffectiveStability.SJSU.Ledger.H.Inputs99
public import KAM.EffectiveStability.SJSU.Ledger.H.Tables15

/-!
# The Horner-stage ledger as `HData` (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The Horner-stage ledger of `SJSU18-O2`. -/
def sjsuHD : HData where
  P := ⟨320, 139, 82⟩
  CT := 9
  CP := 30
  M := 9
  Nmax := 18
  ns := sjsuNs
  T := fun n => (sjsuTlist.lookup n).getD LitD.dflt
  Tc := fun n => (sjsuTclist.lookup n).getD Cl.dflt
  Pw := fun j k => (sjsuPwlist.lookup (j, k)).getD LitD.dflt
  Pc := fun j k => (sjsuPclist.lookup (j, k)).getD Cl.dflt
  V := fun k => (sjsuVlist.lookup k).getD LitD.dflt
  Vc := fun k => (sjsuVclist.lookup k).getD Cl.dflt
  H := fun k => (sjsuHlist.lookup k).getD LitD.dflt
  Hc := fun k => (sjsuHclist.lookup k).getD Cl.dflt
  Tdat := sjsuTdat
  Bdat := sjsuBdat

/-- The `U` parameters of a block. -/
def sjsuUp (n1 m3 : Nat) : List (Nat × UPrm) := (sjsuUP.lookup (n1, m3)).getD []

/-- The `V` parameters of a block. -/
def sjsuVp (n1 m3 : Nat) : List (Nat × OPrm) := (sjsuVP.lookup (n1, m3)).getD []

/-- The `h` parameters. -/
def sjsuHp (m : Nat × Nat × Nat) : OPrm := (sjsuHP.lookup m).getD OPrm.dflt

/-- The witness and power parameters. -/
def sjsuSq (j : Nat) : SqPrm := (sjsuSQ.lookup j).getD SqPrm.dflt

def sjsuIv (j : Nat) : IvPrm := (sjsuIV.lookup j).getD IvPrm.dflt

def sjsuPp (j : Nat) (k : Int) : OPrm := (sjsuPP.lookup (j, k)).getD OPrm.dflt


end KAM.EffectiveStability.SJSU

end
