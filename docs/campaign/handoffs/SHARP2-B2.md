# SHARP2-B2 handoff: refined data and geometry of the v2 theorem

Brief `/home/scott/kam-tools/briefs/SHARP2-B2.md` (Sonnet), branch `sharp-b2`. LOCAL-COMMON applies. One merge of
`sharp-b1` (B1's `SmallDiv/Defs`, for `SDConst`).

## Files
- `KAM/Sharp2/Data.lean` (84 lines): `RefData`, `RefData.ofV1`, `RefHyp`, `refHyp_ofV1`. **Signatures verbatim.**
- `KAM/Sharp2/Geometry.lean` (303): `norm_invarianceError_le_eta` (**verbatim**), and the Lagrangian-defect lemma in a
  corrected form (below). Helpers: `frame_proj`, `frame_surj`, `differentiableOn_etaN`, `etaNDeriv`,
  `fderiv_lagrangeMat_eq_etaN` (`∂_ω Ω_K = -(Dηᴺ - (Dηᴺ)ᵀ)`), `norm_etaNDeriv_sub_transpose_le`.
- `KAM.lean` regenerated.

## Design signal: `norm_lagrangeMat_le_etaN` is not provable as stated (two obstructions)
1. **`hh` carries no derivative information.** The signature has `hh : DifferentiableOn ℂ h {z | ∃ θ ∈ T_r, z = K θ}`:
   holomorphy on the image `K(T_r)`, a set with empty interior in `ℂ^{2n}`. `etaN`, `hamiltonianVectorFieldℂ` and
   `fderiv ℂ h` are defined by `fderiv` on the ambient space, so nothing follows about `Dh` or `D²h` at image points.
   The proof needs the identity `∂_ω Ω_K = -(Dηᴺ - (Dηᴺ)ᵀ)`, which uses `D²h` symmetric (`Aᵀ Ω₀ + Ω₀ A = 0`) on an
   open set around the image.
2. **`n = 0`.** The conclusion has the factor `2 * (n - 1)`; for `n = 0` the left side is `0` and the right side is
   negative whenever `c₁, γ, εN > 0`. A hypothesis `1 ≤ n` is needed (the frozen theorems all have `2 ≤ n` or `1 ≤ n`).

**Delivered instead:** `KAM.Sharp2.norm_lagrangeMat_le_etaN_of_standing`, the same conclusion, with `hh` replaced by
`hS : Standing n τ M σK σB σT 𝔅 h ω γ₀` and `hK𝔅 : ∀ θ ∈ T_r, K θ ∈ 𝔅` (as in every v1 geometry lemma), and
`hn : 1 ≤ n` added. `hG` is not needed and was dropped, `hKr` is not needed and was dropped. It uses only the
`apriori` clause of `SDConst` at the bite `s δ` on the strip `r - (1-s)δ`, Cauchy for `ηᴺ` at radius `(1-s)δ`, and
`exactness` (`⟨Ω_K⟩ = 0`). **Proposal:** replace the signature by this one (the downstream consumer already has
`Standing` and `K(T_r) ⊆ 𝔅`).

## Checks
- `lake build KAM.Sharp2.Data KAM.Sharp2.Geometry`: success.
- Signature probe `.drafts/sigcheck.lean`: the verbatim signatures of `refHyp_ofV1` and `norm_invarianceError_le_eta`
  closed by my theorems.
- `#print axioms` (probe): `refHyp_ofV1`, `norm_invarianceError_le_eta`, `norm_lagrangeMat_le_etaN_of_standing`,
  `norm_etaNDeriv_sub_transpose_le`: all `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: `check_lean_modules` PASS, frozen guard OK; only the known ABI-scratch failure. It lists
  lines over 100 characters in my two files: they are the verbatim signature and docstring lines (and a few proof
  lines I did not wrap), plus one in B1's `SmallDiv/Defs.lean`; `KAM.lean` (generated) is over 1500 lines.

## Proof notes
- Recovery: `E = L ξᴸ + N ξᴺ` exists because `P = (L N)` is injective (`PᵀΩ₀P` blocks `[[Ω_K,-I],[I,Ω_N]]`, `|Ω|≤q<1`),
  hence onto; `ηᴺ = Ω_K ξᴸ - ξᴺ`, `ηᴸ = -ξᴸ - Ω_N ξᴺ` (from `Lᵀ Ω₀ N = -I`, `Nᵀ Ω₀ L = I`).
- Sign: the blueprint writes `∂_ω Ω_K = Dηᴺ - (Dηᴺ)ᵀ`; with the repository's conventions it is the negative (norms
  unaffected).

## Uncertainties / errata
- No errata in pinned sources beyond the two signature problems above (the blueprint's sign of `∂_ω Ω_K`, harmless).
- The Lagrange lemma was not re-checked against B1's later changes to `SDConst` (only the committed `Defs.lean`).
