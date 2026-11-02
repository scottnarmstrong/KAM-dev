/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Defs

/-!
# The black box's output depends only on the fields it reads

`CertifiedTorus c ωstar` reads a certificate only through `params`, the Hamiltonian `ham`, the
domain's `weightH`, `centre` and `radius`, and the embedding's denotation `K`. The soundness
theorems' hypotheses add `freqBox`. So a torus certified for one certificate is certified for every
certificate that agrees with it on these fields. This is the bridge from a generated copy of a
certificate (in another namespace, or without advice and witnesses) to the original. It compares
only these fields, never the advice books, which the black box does not read.

* `certifiedTorus_congr`: the two statements are equivalent;
* `certifiedTorus_congr_emb`: the same, for one backend with equal embeddings;
* `certifiedTorus_transfer`: the soundness theorem's form (every `ωstar` of the box that is
  Diophantine) carried from one certificate to the other.
-/

@[expose] public section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate

variable {n : ℕ} {α β : Type} [CertArith α] [CertArith β]

/-- **The black box's output depends only on the fields it reads.** -/
theorem certifiedTorus_congr {c : TorusCertificate n α} {c' : TorusCertificate n β}
    (hp : c.params = c'.params) (hh : c.ham = c'.ham) (hw : c.weightH = c'.weightH)
    (hc : c.centre = c'.centre) (hr : c.radius = c'.radius) (hK : c.K = c'.K)
    (ωstar : Fin n → ℝ) : CertifiedTorus c ωstar ↔ CertifiedTorus c' ωstar := by
  simp only [CertifiedTorus, TorusCertificate.H, TorusCertificate.D, hp, hh, hw, hc, hr, hK]

/-- `certifiedTorus_congr` for one backend, with equal embeddings. -/
theorem certifiedTorus_congr_emb {c c' : TorusCertificate n α} (hp : c.params = c'.params)
    (hh : c.ham = c'.ham) (hw : c.weightH = c'.weightH) (hc : c.centre = c'.centre)
    (hr : c.radius = c'.radius) (he : c.emb = c'.emb) (ωstar : Fin n → ℝ) :
    CertifiedTorus c ωstar ↔ CertifiedTorus c' ωstar :=
  certifiedTorus_congr hp hh hw hc hr (by simp only [TorusCertificate.K, he]) ωstar

/-- **The soundness theorem's form, carried across the congruence**: if every `ωstar` of `c`'s box
that is Diophantine for `c`'s constants gives `CertifiedTorus c ωstar`, the same holds for `c'`,
which agrees with `c` on the fields the black box and these hypotheses read. -/
theorem certifiedTorus_transfer {c : TorusCertificate n α} {c' : TorusCertificate n β}
    (hp : c.params = c'.params) (hh : c.ham = c'.ham) (hw : c.weightH = c'.weightH)
    (hc : c.centre = c'.centre) (hr : c.radius = c'.radius) (hK : c.K = c'.K)
    (hf : c.freqBox = c'.freqBox)
    (h : ∀ {ωstar : Fin n → ℝ}, FreqEncloses n c.freqBox ωstar →
      IsDiophantine (c.params.γ : ℝ) (c.params.tau : ℝ) ωstar → CertifiedTorus c ωstar)
    {ωstar : Fin n → ℝ} (hω : FreqEncloses n c'.freqBox ωstar)
    (hdio : IsDiophantine (c'.params.γ : ℝ) (c'.params.tau : ℝ) ωstar) :
    CertifiedTorus c' ωstar := by
  rw [← hf] at hω
  rw [← hp] at hdio
  exact (certifiedTorus_congr hp hh hw hc hr hK ωstar).1 (h hω hdio)

end KAM.CertificateSharp.Packed
