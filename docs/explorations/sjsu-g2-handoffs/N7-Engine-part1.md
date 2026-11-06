# N7-Engine part 1 (interim commit for the N8/N9a audits), recorded by kam-g2

Scope, as stated by N7 (worker g2-n3) at 17:47 UTC; N7's full handoff follows with the ledger.

- **Files:** `KAM/EffectiveStability/Tube/Engine/{Types,Spread,Lit,L1,Comb,Step,Input,Sparse,BTerm}.lean` (core,
  namespace `KAM.EffectiveStability.Tube`) and the generated observable data `KAM/EffectiveStability/SJSU/Ledger/F.lean`,
  `SJSU/Ledger/F/Part0..10.lean` (opt-in `KAMSJSU`), with their generator `scripts/sjsu/ledger/{fobs,emit}.py`
  and `scripts/sjsu/ledger/manifest-F.json`.
- **Stability:** no signature changes planned. The closure is self-contained: `Types` imports nothing from
  `Exact/Block/Witness/Horner/Powers/Deriv` (not in part 1). New N7 work goes in new files only
  (`Engine/Bracket.lean`, `SJSU/Ledger/Br/*`).
- **F is final:** `Fprm = ⟨448, 139, 82⟩`; the F-v1 even parts (`.drafts/g2/data/F-v1.json`), pruned at
  `|a|(2·10⁻⁶)^|s| < 10⁻²¹` (25,349 entries) and rounded to 80 bits; the rounded pruned literal IS the observable.
  The bracket stage repacks the F operands at the product width (`SpD.opd w S`), so the storage slot width never
  changes. Python η re-verification with this exact F: `(6.64, 2.96, 7.29)·10⁻²⁰`; model error ≤ `2.1·10⁻²⁴`.
- **Not in part 1:** `Engine/{Exact,Block,Witness,Horner,Powers,Deriv}.lean`, `SJSU/Ledger/Small/*`,
  `SJSU/Ledger/H`, the rest of `scripts/sjsu/ledger/` (the producer is still changing).
