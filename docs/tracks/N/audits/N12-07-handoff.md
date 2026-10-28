# N12-07 prover handoff (branch inp-n1207, 41b6f51; base inp-n1201; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/Averaging/Rank.lean` (186 lines). Commit on branch inp-n1207. No other file touched.

**Node:** `bpN:p12:lambda` (steps la-inj, la-cpt) = `KAM.Nekhoroshev.«lambda»`, signature verbatim from N12Signatures.lean.

**Approach:** helper namespace `KAM.Nekhoroshev.AvgRank`. `gap h (I,e) = ∑ⱼ(∑ᵢ M_ij eᵢ)² + (e·ω)²` (euclid-free form; `euclid_sq` converts).
`gap_pos` (la-inj): if gap = 0 then Mᵀe = 0 and e·ω = 0, so e is orthogonal to the range of the differential (`fderiv_apply_eq` expresses it via `avgM`) and, in the second alternative of `hrank`, of `(v,t) ↦ Dv + tω`; surjectivity (`false_of_orth`) gives |e|₂² = 0, contradicting |e|₂ = 1. Both disjuncts of the frozen `HasAveragingFrequencyRank` handled.
`gap_continuousOn` + `isCompact_sphere` + `avgG` compact (la-cpt): minimum on avgG × sphere via `IsCompact.exists_isMinOn`; `lam = √(min)`; empty case lam = 1.
`contDiffOn_freq` is re-proved locally (the one in Setting is private); no change to Setting.

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-n1207 KAM.Nekhoroshev.Averaging.Rank`: "Build completed successfully (2903 jobs)", no warnings.
- `#print axioms KAM.Nekhoroshev.«lambda»`: [propext, Classical.choice, Quot.sound].
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; reports only "KAM.lean is out of date; run scripts/gen_root_imports.py" (expected: I must not edit KAM.lean; orchestrator regenerates to include Averaging/Rank).

**Uncertainties / errata / deviations:** none. No heartbeat issues; no set_option; file well under 1500 lines. Imports only Setting and Interfaces.Norms (no provider/theorem anchor).

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-07 and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements = design signatures (lambda: surjective adjoint argument and compact positive minimum; frozen rank predicate consumed); (2) proofs sound; no added premises; (3) hygiene. Audit ONLY the Rank module.
