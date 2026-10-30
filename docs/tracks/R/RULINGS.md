# Track R: owner rulings

- **R1 (2026-10-30) R-HEAD approved and frozen.** *(Scott: "approve R-HEAD with Q1(d), other recommendations", on the
  review page of statement draft v0.1, claude.ai/artifact/4XdxRLmoVNzbiQAz6uPbB3, after the independent audit
  AUDIT-RUSSMANN-STATEMENT-1.)*
  - Q1 (d): the classical strong form, `∀ κ > 0`, `volume (FD \ russmannCover …) ≤ κ · volume FD` (the audit's F1
    replacement text, named `russmann_kam`; docstring updated accordingly).
  - Q2 `∃ τ > n − 1` chosen before δ, κ and f; Q3 `1 ≤ n`; Q4 the new `russmannCover` (= `kamCover` without the
    frequency clause); Q5 `IsConnected B`; Q6 Rüssmann's condition inline on the real set B; Q7 `∀ δ > 0` before
    `∃ ε₀`; Q8 names `KAM.Russmann.russmann_kam`, `KAM.Russmann.russmannCover`, provider
    `KAM.Provider.Russmann.russmann_kam`.
  - Frozen on branch `russmann` only (not `main`): `KAM/Frozen/Russmann/Defs/RussmannCover.lean` (SEALED definition)
    and `KAM/Frozen/Russmann/Theorems/RussmannKam.lean` (`DRAFT_SORRY`), provider stub
    `KAM/Provider/Russmann/RussmannKam.lean`. Bytes: the audited drafts with two changes, both shown to the owner in
    the approval exchange: the status line of each docstring ("Owner-approved …" instead of "DRAFT v0.1 (not
    approved)"), and the Q1(d) conclusion with its docstring sentence.
  - Deviations from Rus01 adopted with this ruling: D-R1–D-R5 (`statement.md` §1).
  - The branch lands on `main` only after the anchor is SEALED, kernel-replayed and audited.
