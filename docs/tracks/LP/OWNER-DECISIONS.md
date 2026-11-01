# Track LP: decisions for the owner

Overnight mode (2026-11-01): every item that needs the owner is logged here instead of asked. Each item states the
default kam-lp follows overnight; nothing is frozen, so every default is reversible. root-b8 presents this file
with `FREEZE-PROPOSAL.md` in the morning.

| Id | Logged (UTC) | Question | Overnight default | Status |
|---|---|---|---|---|
| OD-1 | 11-01 00:40 | Planar AMD in the statements: MAIN's `C = Σ Λ_i − |L|` (orientation-free) or the frozen signed `physicalAMD = Σ Λ_i − L`? | New `strongAMD` with `|L|` (MAIN (2)); a lemma identifies it with `physicalAMD` when `L ≥ 0`. The theorem then needs no prograde premise (MAIN L3 derives it after orienting the plane). **Audit N8 / root-b8 caution:** if the anchor instead uses the signed `physicalAMD`, the hypothesis `physicalAMD ≤ B − δ` forces `L > 0`, and the theorem is equivalent to MAIN's only through a reflection bridge (LP-MOM item 9 proves it either way). | open |
| OD-2 | 11-01 00:40 | Carrier of `pairThreshold` / `strongThreshold`: a total formula (`sInf` of the objective over the always-nonempty feasible set) with the attained-minimum characterization proved on the chamber, or a subtype `OrderedActions ν` argument? | Total `sInf` formula plus characterization (roadmap §1 allows it "after proving this characterization"). Reason: the headline then needs no proof terms inside `strongThreshold (Λ ν z₀)`. No `if`-totalization either way. **Recommended for the freeze (root-b8, 01:00):** freeze on the source carrier (an `OrderedActions ν` subtype, or explicit carrier arguments with `i < j`) with the attained-minimum characterization as its semantic unit; the total `sInf` form stays an internal helper proved equal to the carrier version (the project's rules for frozen definitions reject off-source fallback values). LP-THR exposes both, so either choice is cheap. | open |
| OD-3 | 11-01 00:40 | μ normalization `max ν = 1` (RESEARCH/STATEMENTS list). | As MAIN §1: `max_i ν_i = 1`. | open |
| OD-4 | 11-01 00:40 | τ free (τ > n − 1) with the τ = n − 1/2 corollary (exponent 1/(2n+1)). | τ free, corollary stated separately. | open |
| OD-5 | 11-01 00:40 | Crossing notion: canonical radial annuli (MAIN (9)) plus the actual-velocity osculating corollary (L16). | Both, as in roadmap §2. | open |
| OD-6 | 11-01 00:40 | LP0/LP1/LP2 are new anchors; `planetaryExponentialSafety` (P-EXP-SAFE) stays unchanged. | Yes, new anchors only; no frozen edit. | open |
| OD-7 | 11-01 00:40 | Freeze of the LP0–LP2 statements (exact elaborated text). | Not frozen overnight; proposal in `FREEZE-PROPOSAL.md` once wave 1 has elaborated the definitions. | open |
| OD-8 | 11-01 00:40 | Waves 2–4 start only after the independent proof-audit verdict (PROOF-AUDIT-1) with notes applied. | Verdict PASS WITH NOTES relayed by root-b8 at 00:50; notes applied (`source/AMENDMENTS.md`); GO for waves 2–4 under the overnight rules. | closed |
| OD-9 | 11-01 00:50 | Audit N10: the headline constant list records `A_osc μ₀ ≤ d_⋆/2` and `2 A_osc μ₀ ≤ d_pair/2` (or the conclusion keeps `d_⋆/2`, `d_pair/2` as stated). | Keep the roadmap §2 conclusion (osculating gaps `≥ d_⋆/2`, `≥ d_pair/2`); the ordering is internal to the proof. | open |
