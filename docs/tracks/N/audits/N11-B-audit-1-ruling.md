# N11-B audit 1: orchestrator ruling (2026-10-28 18:50, D29 overnight mode)

Audit 1 (N11-B-audit-1.md) passes every mathematical, signature, axiom and kernel check; its only finding, F1,
is the naming policy "no reused public short name" applied to the SIGNED definitions `constants`
(`KAM.Nekhoroshev.Partial.constants` vs `KAM.Planetary.constants`) and `kappa` (vs `KAM.Apost.kappa`,
`KAM.Iso.R3bp.kappa`). The fully qualified names differ, there is no root shadowing, and both names are exact
signature requirements.

Ruling: the short-name rule governs unsigned helpers only; signed names follow the design's signature file
(same principle as the 18:47 ruling for N10-3). The orchestrator's pre-audit short-name check already exempts
signed names. N11-B is accepted on audit 1's mathematical PASS; no re-audit. N1 (handoff wording about the
earlier `constants` namespace and the missed `kappa`) is a receipt correction only.
