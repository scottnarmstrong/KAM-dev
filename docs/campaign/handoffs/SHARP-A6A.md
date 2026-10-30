# SHARP-A6A handoff: isoenergetic constants, `iso_step_small`, `border_bounds`

Branch `sharp-a6a`. All targets proved with default heartbeats; no `sorry`, no signature changed.

## Files (new)
| File | Lines | Content |
|---|---:|---|
| `KAM/Iso/Sharp/Constants.lean` | ~80 | all `def`s of `bpI:p2s:constants` (`thetaS` … `sharpIsoC3`), verbatim from the signatures |
| `KAM/Iso/Sharp/ConstantsArith.lean` | 240 | `iso_step_small`; extra `iso_consts_pos` (positivity of `iCDK, iCDw, iCE, iCDTb, iCStep, iCSum, iCStar`) |
| `KAM/Iso/Sharp/BorderBounds.lean` | ~90 | `border_bounds` |
| `KAM.lean` | | regenerated (3 new imports) |

## Approach
- `iso_step_small`: same proof as `KAM.Sharp.step_small` (reuses `KAM.Sharp.absorb`): `iCStep` has the same
  six-branch `max` chain, with `iCDK`, `iRateD`, `iCDTb`, `iCE` in place of `cDK`, `rateD`, `cDT`, `cE`.
  The nine constants are `generalize`d to reals after extracting the `max` facts (the heartbeat lesson of A2), and
  `linarith only` is used. Private `iso_consts_nonneg` is a `positivity` chain without `1 ≤ n`.
- `border_bounds`: the generic helpers `BorderSolve.norm_bordSol_le` and `norm_bordXiN_bordGL_le` (already generic
  in the bound `Z`) plus `CohData.sol` for the bound of `uᴺ = 𝓡ηᴺ` (`triU` is `cohR`) and of `𝓡 gᴸ` on `T_{r-2δ}`.
  The qualitative facts (differentiability, periodicity, `⟨gᴸ⟩ = 0`) are clause (a) of `border_solve` itself.
  `border_solve` is not modified.

## Checks
- `nice -n 5 lake build KAM.Iso.Sharp.{Constants,ConstantsArith,BorderBounds}`: succeed, no warnings from these
  files (`hμ`, `hν` of `iso_consts_pos` are named `_hμ`, `_hν`: unused, since the first `max` argument is positive).
- `sh scripts/lint_sources.sh`: `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`; only the known ABI-scratch
  failure. Two line-length warnings remain, in A3's files (`KAM/Sharp/TorsionBound.lean:25`, `TorsionPoly.lean:25`),
  not mine.
- `#print axioms` (probe `.drafts/ax.lean`, not committed) of `border_bounds`, `iso_step_small`, `iso_consts_pos`:
  `[propext, Classical.choice, Quot.sound]` each.
- **Mirror** (iso branch of `scripts/apost_sharp/thresholds.py`, package R1, Rüssmann, exact `Fraction`s, independent
  transcription of the Lean `def`s): `c_star`, `C_DK` (= `iCDK`), `C_Dw` (= `iCDw`), `C_E` (= `iCE`) are equal, and
  the four terms `2^{2a}·iCE`, `iCStep`, `iCSum/μ`, `4γ̄²·iCDw/ν` are equal to `terms['E','step','sum','nu']`
  (so `iCDTb`, the rates and `iCdK`, `iCP` are exercised). Active branch `E`, `c_star ≈ 9.164·10⁸`.
  No mismatch.

## Deviations / uncertainties / errata
- Constants file imports only `KAM.Sharp.Constants` (the signatures' `open` of Apost/Iso namespaces is not needed
  for the defs). `delta0s` is A2's inlined form.
- `border_bounds` does not use `hr` beyond `0 < r` for `norm_bordSol_le`; `hδ1` is used through `CohData.sol`.
- No errata found.

## What remains
Second half of A6 (needs A4): `iso_correction_bounds`, `iso_newton_error_bounds`, `iso_twist`, `iso_step_spec`.
