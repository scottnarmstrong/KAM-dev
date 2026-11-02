/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import HD11964.CellCauchy
public import HD11964.ChiHD
public import HD11964.ChiRot
public import HD11964.ChiSmooth
public import HD11964.Cover
public import HD11964.CoverPlan
public import HD11964.Generator
public import HD11964.Glue
public import HD11964.Homological
public import HD11964.ParamIntegral
public import HD11964.NoCrossing
public import HD11964.NoCrossingObs
public import HD11964.ReducedRange
public import HD11964.TailAniso
public import HD11964.TailBound
public import HD11964.TailSum
public import HD11964.Threshold

/-!
# HD 11964 (application package root)

The modules of the HD 11964 application (decision D51; opt-in, outside the core build). Phase 2,
part A: the action box, `B = Λ_c` and the data of LP-LIFT (`HD11964.Threshold`); the certificate
region `R(d)` and no orbit crossing given the certificate's bounds on it (`HD11964.NoCrossing`). The
bridge from a certified Λ-drift to no orbit crossing is in the core (`KAM.Application.LambdaDrift`).
Phase 2, the cover: the cover lemma for affine cells (`HD11964.Cover`) and the fitted 50-cell plan
of `R(1/500)` with its decided check (`HD11964.CoverPlan`). The pieces of the cell check
(HD11964-LEMMAS): the Cauchy bound for the slow derivatives (`HD11964.CellCauchy`), the exact
generator and its certified remainder (`HD11964.Generator`), and the consumer glue to
`noCrossing_of_regionBounds` (`HD11964.Glue`). The generator's smoothness and the order-2
homological equation (HD11964-CHI): smooth parametric integrals (`HD11964.ParamIntegral`), `χ*`
smooth on angle-saturated sets (`HD11964.ChiSmooth`), `{χ*, h} = Π_S P` and the pure tails
(`HD11964.Homological`), and the HD 11964 instance (`HD11964.ChiHD`). The rotation invariance of
`F` and the tails (HD11964-ROT): `hFrot` for HD 11964 and the assembled no-crossing statement from
the cell bounds (`HD11964.ChiRot`), the tail weight of a box mode set (`HD11964.TailSum`), and the
tails `T₁`, `T₂` from Fourier decay on a strip (`HD11964.TailBound`) and on an anisotropic strip
(`HD11964.TailAniso`).

The reduced-mass bridge (scoping note §4): the reduced Delaunay actions and the analytic range of
`G - Λ` on `R(r)` (`HD11964.ReducedRange`), and no orbit crossing with the first exit driven by
them (`HD11964.NoCrossingObs`).
-/
