/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Certificate.Defs
public import KAM.Certificate.Arith.Fixed
public import KAM.CertificateSharp.Kernel.SegDefs

/-!
# Format of the forced-toy data (V2-TOOLS #6)

The backend `FB = CertFixed 96`, the Fourier term `ft k₀ k₁ re im` (mantissas at `2^-96`), and
tail-recursive Boolean equalities of model lists and model matrices with their reflection lemmas
(`eq_of_modelsBeq`, `eq_of_matBeq`, `eq_of_optModelsBeq`), used to re-prove each memoized stage
literal by one kernel run.
-/

@[expose] public section

namespace KAM.CertificateSharp.V2.Forced

open KAM.Certificate

/-- The backend of the forced toys. -/
abbrev FB : Type := CertFixed 96

/-- A Fourier term: the key `[k₀, k₁]` and the mantissas of the coefficient. -/
def ft (k₀ k₁ re im : ℤ) : CertKey × CC FB := ([k₀, k₁], ⟨⟨re⟩, ⟨im⟩⟩)

section Beq

variable {α : Type} [DecidableEq α]

/-- Tail-recursive equality of model lists. -/
def modelsBeq : List (CertModel α) → List (CertModel α) → Bool
  | [], [] => true
  | a :: as, b :: bs => a.segBeq b && modelsBeq as bs
  | _, _ => false

theorem eq_of_modelsBeq : ∀ {l l' : List (CertModel α)}, modelsBeq l l' = true → l = l'
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [modelsBeq, Bool.and_eq_true] at h
    rw [CertModel.eq_of_segBeq h.1, eq_of_modelsBeq h.2]
  | [], _ :: _, h => by simp [modelsBeq] at h
  | _ :: _, [], h => by simp [modelsBeq] at h

/-- Tail-recursive equality of model matrices (row by row). -/
def matBeq : ModelMatrix α → ModelMatrix α → Bool
  | [], [] => true
  | r :: rs, s :: ss => modelsBeq r s && matBeq rs ss
  | _, _ => false

theorem eq_of_matBeq : ∀ {A B : ModelMatrix α}, matBeq A B = true → A = B
  | [], [], _ => rfl
  | r :: rs, s :: ss, h => by
    simp only [matBeq, Bool.and_eq_true] at h
    rw [eq_of_modelsBeq h.1, eq_of_matBeq h.2]
  | [], _ :: _, h => by simp [matBeq] at h
  | _ :: _, [], h => by simp [matBeq] at h

/-- Equality of an optional model list with a literal one. -/
def optModelsBeq : Option (List (CertModel α)) → List (CertModel α) → Bool
  | some l, l' => modelsBeq l l'
  | none, _ => false

theorem eq_of_optModelsBeq {o : Option (List (CertModel α))} {l : List (CertModel α)}
    (h : optModelsBeq o l = true) : o = some l := by
  cases o with
  | none => simp [optModelsBeq] at h
  | some l₀ => rw [eq_of_modelsBeq (l := l₀) h]

end Beq

end KAM.CertificateSharp.V2.Forced

end
