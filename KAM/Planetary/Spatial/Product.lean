/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.Spatial.Product.Defs
public import KAM.Planetary.Spatial.Product.Chart
public import KAM.Planetary.Spatial.Product.Deficit
public import KAM.Planetary.Spatial.Product.Split

/-!
# The n-body spatial product chart (facade)

Package LP-SP-PROD, `LP:MAIN L17 (533–578)` for `n` bodies, track LP, non-frozen. Facade importing
the modules of `KAM/Planetary/Spatial/Product/`:

* `Defs`: layout `Phase (n + (n + n))`, block maps, `spatialPoincareProd`, domain and region;
* `Chart`: analyticity, symplecticity, lattice periodicity, image, injectivity mod the lattice,
  local analytic diffeomorphism;
* `Deficit`: (45) summed, the fixed-plane deficit identity `C_{e₃} = Σ (Γ_i + Z_i)`;
* `Split`: the exact split `H_μ = −Σ ν_i³/(2 I_i²) + μ fSpatial`.

The statement surface is proposed in docs/tracks/LP/FREEZE-PROPOSAL.md.
-/
