# W6 round 2 handoff (tight delta: W6-TORI)

Branch `inp-w6t` @ d88a5e0a (+ inp-w5aa, inp merged). Round 1 `W6-audit-1.md` audited the conditional W6 at
24c56b59 and failed on F1 (iter-lemma transformation clause in ambient norms), F2 (D2, J-weighted shift) and F3 (D4,
freq-lip constants). Producer handoff: `W6-TORI-handoff.md` (TASK 1 discharge + unconditional names, D2, D4,
TASK 2 `bpW:w6:tori`, and the section W6-AUDIT1-FIX mapping F1–F3 to declarations).

## AUDIT FOCUS (delta `git diff 24c56b59..HEAD -- KAM/Wave/Iteration`)
1. F1–F3 of round 1 closed exactly as the blueprint states them (w6-iteration.tex:63–64, :237/:251–253, :305),
   with the J-weighted bound attached to the modified step's actual output H.Om0 (not a replaced frequency, not a
   premise), and the wave family using ε₁ = 3γα, ε₂ = 4ε₀ unconditionally.
2. The discharge of `W6StepSmooth` / `W6StepSmoothMod` (`StepSmoothW5`) from W5's Ψ, and that every W6 label
   previously stated as `*_of_stepSmooth` now has an unconditional source-facing theorem (names listed in the
   handoff); the helpers keep distinct names (rule 6).
3. **New label `bpW:w6:tori` (i)–(v)** (full audit of its new modules).
4. The step-0 adaptation to W5's appended conjuncts (`stepTheorem_clauses`) changes no W6 statement.

Changed or new modules:
- `KAM.Wave.Iteration.ComposeStep`
- `KAM.Wave.Iteration.FreqLipJ`
- `KAM.Wave.Iteration.IterLemma`
- `KAM.Wave.Iteration.PrepShiftJ`
- `KAM.Wave.Iteration.PrepStep`
- `KAM.Wave.Iteration.SmoothSrc`
- `KAM.Wave.Iteration.StepSmooth`
- `KAM.Wave.Iteration.StepSmoothW5`
- `KAM.Wave.Iteration.StrongConj`
- `KAM.Wave.Iteration.Tori`
- `KAM.Wave.Iteration.ToriBk`
- `KAM.Wave.Iteration.ToriBridge`
- `KAM.Wave.Iteration.ToriPrep`
