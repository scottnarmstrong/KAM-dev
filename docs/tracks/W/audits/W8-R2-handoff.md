# W8 round 2 handoff (W8 complete: W8-PREP + W8-ASM + W8-FINAL, and the provider of KAM.Wave.nlw2)

Branch `inp-wprov` (W8-FINAL inp-w8f @ dc3a9d5c + provider commit 16141d21 + inp). Round 1
`W8-audit-1.md` (branch inp-w8a) audited W8-PREP + W8-ASM and failed on F1 (w6-general constants/tori conjunct),
F2 (Kshell generic totalization), with N1 (partial labels). W8-FINAL (handoff `W8-FINAL-handoff.md`) then switched
W8 to the unconditional W6 API (W6-TORI) and completed torus-shape, shell-close, shell-embedding, shell-inv,
injective, nlw2-proof, and instantiated Kshell with the source action-angle map.

## AUDIT FOCUS
1. Round-1 F1, F2, N1 closed in the final code: `w8_w6General` (ShellIter) with ε₁ = 3γα_n, ε₂ = 4ε_{0,n} and the
   tori conjunct; the source `Kshell` (`w8Kshell w8AA (w8HW hm n)`, `w8Kshell_eq`) with ball membership proved on
   the shell carrier; every N1 label now unconditional or still explicitly partial.
2. Every `bpW:w8` label (w8-assembly.tex) at the final code, with statement fidelity and rule 6 (no conditional
   helper standing in for a label; no premise beyond the source).
3. **`KAM.Wave.nlw2_proof`** (Nlw2Proof.lean): its type must be exactly the frozen `KAM.Wave.nlw2` statement
   (`KAM/Frozen/Wave/Theorems/Nlw2.lean`, read only); it imports only frozen DEFINITIONS, never the anchor or a
   provider. Orchestrator check: Expr equality true; axioms [propext, Classical.choice, Quot.sound].
4. **Provider** `KAM.Provider.Wave.nlw2` (KAM/Provider/Wave/Nlw2.lean): statement verbatim from the frozen file,
   body `KAM.Wave.nlw2_proof hm`; quarantine (only the anchor imports it). The seal edit itself
   (anchor body `by exact KAM.Provider.Wave.nlw2 hm`) is NOT made: it awaits the owner; do not perform it.
5. Out of scope: W5 (KamStep, incl. ActionAngle*/Initial*, in their own audits), W6 (Iteration), W7.

Modules: all `KAM/Wave/Assembly/*` and `KAM/Provider/Wave/Nlw2.lean`.
