/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.V2.Tests.Forced.MicroRotTransform
public import KAM.SpinOrbit.Rotated

/-!
# `MicroRot` uses the lunar client's change of variables

The generic shear `shearMap` of `KAM/CertificateSharp/LinearShear.lean` is the lunar client's
`soRotMap` (`shearMap_eq_soRotMap`, `shearMapInv_eq_soRotMapInv`), so `MicroRot` is `Micro` in the
rotated variables of the lunar client (`H_eq_soRot`, `K_eq_soRot`). The generic covariance
`hamiltonianVectorFieldℂ_comp` gives `X_{H ∘ soRotMap} = soRotMapInv ∘ X_H ∘ soRotMap` for every
`H` (`hamiltonianVectorFieldℂ_comp_soRotMap`), and recovers the lunar client's
`hamiltonianVectorFieldℂ_soRotHC` (`soRotHC_field`).
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced.MicroRot

open KAM KAM.Certificate KAM.CertificateSharp.Linear KAM.SpinOrbit

theorem shearMap_eq_soRotMap : shearMap = soRotMap := rfl

theorem shearMapInv_eq_soRotMapInv : shearMapInv = soRotMapInv := rfl

/-- `MicroRot.H = Micro.H ∘ soRotMap`. -/
theorem H_eq_soRot : cert.H = Micro.cert.H ∘ soRotMap := H_eq

/-- `MicroRot.K = soRotMapInv ∘ Micro.K ∘ S`. -/
theorem K_eq_soRot : cert.K = soRotMapInv ∘ Micro.cert.K ∘ shearAngle := K_eq

/-- The vector field of any Hamiltonian in the lunar client's rotated variables. -/
theorem hamiltonianVectorFieldℂ_comp_soRotMap (H : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ)
    (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    hamiltonianVectorFieldℂ (H ∘ soRotMap) z =
      soRotMapInv (hamiltonianVectorFieldℂ H (soRotMap z)) :=
  hamiltonianVectorFieldℂ_comp shearCLE_isSymplectic H z

/-- The lunar client's `hamiltonianVectorFieldℂ_soRotHC`, from the generic covariance. -/
theorem soRotHC_field (z : (Fin 2 → ℂ) × (Fin 2 → ℂ)) :
    hamiltonianVectorFieldℂ soRotHC z =
      soRotMapInv (hamiltonianVectorFieldℂ soHC (soRotMap z)) :=
  hamiltonianVectorFieldℂ_comp_soRotMap soHC z

end KAM.CertificateSharp.V2.Forced.MicroRot

end
