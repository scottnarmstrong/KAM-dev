/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.TinyData
public import KAM.CertificateSharp.V2.RouteAll

/-!
# The witnesses of the forced toy `Tiny` (definitions only)

The refined claim `Rclaim`, the route-A witness `refinedWit`, the route-B witness `refinedBWit` and
the L8′
witness `refinedWitR`, as forced_witness.py chose them. The mutation modules `TinyMut*` change one
input
of them; the passing checks are in the opt-in `kernel-tests/CertificateSharp/V2/ForcedRoutes.lean`.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.Tiny

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2

/-- The refined claim (bounds on `H` and the frame). -/
def Rclaim : RefClaim :=
  { dh := (141 / 125), dx := (1001 / 1000), d2x := (1169 / 1000000), d2h := (1001 / 1000),
    bL := (1001 / 1000), bN := (1001 / 1000), bNt := (1001 / 1000), bT := (1001 / 1000) }

/-- The refined route-A witness of `Tiny`. -/
def refinedWit : RefinedWit where
  core :=
    { Xs := (382), kp := 3, th := (1 / 8),
      c := [(1249 / 100000), (1177 / 100000), (1169 / 100000)],
      cbar := [(291 / 12500), (371 / 20000), (1389 / 100000)], ctail := (1021567 / 12500000),
      sB := (6376861 / 6250000), sT := (115601901 / 100000000), sLt := (2002329 / 2000000),
      sN := (100138857 / 100000000), sNt := (10014649 / 10000000), t := (100494123 / 100000000),
      J := 20 }
  R := Rclaim
  κ := (1000000 / 1000001)
  sites :=
    [(some ⟨(773227 / 1000000), 6, 8, (9044 / 25)⟩,
      some ⟨(26037 / 125000), 4, 8, (171071 / 5000)⟩),
     (some ⟨(220053 / 250000), 7, 8, (25697 / 20)⟩,
      some ⟨(113319 / 250000), 5, 8, (21287 / 250)⟩),
     (some ⟨(469567 / 500000), 9, 8, (507257 / 100)⟩,
      some ⟨(668659 / 1000000), 6, 8, (36741 / 200)⟩)]

/-- The refined route-B witness of `Tiny`. -/
def refinedBWit : RefinedBWit where
  core :=
    { Xs := (19 / 31250), kp := 2, a := 2, ybar := 1 / 2, θ := 1 / 16, θξ := 1 / 8, θΩ := 1 / 8,
      q := 1 / 8, θN := 1 / 8, θω := 1 / 8, ts := 1 / 10, bF := (103 / 100000000),
      selfcons := false, lam0 := (103124897 / 50000000000), lamW0 := (206043751 / 100000000000),
      ePer0 := (206043751 / 100000000000), c := [(1249 / 100000), (1177 / 100000)],
      c' := [(1177 / 100000), (1169 / 100000)], cbar := [(291 / 12500), (371 / 20000)],
      ctail := (410399 / 5000000), cbtail := (857079 / 10000000), sB := (102010641 / 100000000),
      sT := (57501847 / 50000000), sLt := (100110271 / 100000000), sN := (20022119 / 20000000),
      sNt := (100110717 / 100000000), J := 20 }
  R := Rclaim
  κ := (1000000 / 1000001)
  sites :=
    [(some ⟨(773227 / 1000000), 6, 8, (9044 / 25)⟩,
      some ⟨(220053 / 250000), 7, 8, (25697 / 20)⟩,
      some ⟨(26037 / 125000), 4, 8, (171071 / 5000)⟩),
     (some ⟨(220053 / 250000), 7, 8, (25697 / 20)⟩,
      some ⟨(469567 / 500000), 9, 8, (507257 / 100)⟩,
      some ⟨(113319 / 250000), 5, 8, (21287 / 250)⟩)]

/-- The witness of route A with lever L8′. -/
def refinedWitR : RefinedWitR where
  base := { refinedWit with core := { refinedWit.core with Xs := (191) } }
  bF := (1 / 1000)
  bT := (1 / 1000)

end KAM.CertificateSharp.V2.Forced.Tiny

end
