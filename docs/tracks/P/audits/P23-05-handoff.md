# P23-05 prover handoff (branch inp-p2305, beddbc6; base inp-n67 (N6 iterative lemma, audited); offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Planetary/Averaging/Direct.lean` (~186 lines). No other file touched.

**Declarations:** `KAM.Planetary.direct`, `KAM.Planetary.direct_step` (statements verbatim from
P23Signatures.lean; only line wrapping of one over-long line differs). Helpers: `conjExp_two`,
`divisor_two`, `bound_two`, `iterU_two` (pure arithmetic at p=2, alpha_N=2alpha/q).

**Approach:** `direct` = `homological_direct (p:=2)` with alpha_N = 2α/q (divisor α_N/conjExp 2 = α/q;
bound conjExp 2·δ/(2π α_N) = qδ/(2πα)); projections c1, c4, c9 (`homRes` is defeq `projMode Λ (truncate K f)`).
`direct_step` builds the full N `IterHyp` (p=2, α_N=2α/q, g = ∑ gj, `IsDecomp` from `hg`; δ_small from `hsmall`)
and consumes `iterative_direct_a` (differentiable, maps-to, injectivity, symplectic), `_b` (displacement),
`_c` (InClass of fp; fp = iterF and gp = iterG definitionally), `_d` (WBound, after rewriting iterU/conjExp),
`_e` (reality; reality of g from the gj by monotonicity of Dom). No premise added; no N declaration restated.

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-p2305 KAM.Planetary.Averaging.Direct`: Build completed successfully, no warnings.
- `#print axioms` direct and direct_step: [propext, Classical.choice, Quot.sound].
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK. Only complaints: one >100-char
  line (fixed afterwards, rebuilt OK) and `KAM.lean is out of date; run scripts/gen_root_imports.py` — KAM.lean is generated and
  must not be edited by me; the orchestrator should regenerate it to include Averaging/Direct.

**Uncertainties / errata / deviations:** none. No heartbeat issues; no set_option used.

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md revision 2 row P23-05 and proof plan; audits DESIGN-P23-design-audit-{1,2}.md; signatures .drafts/design/P23Signatures.lean): (1) statements = design signatures (direct, direct_step) and they consume the EXACT N declarations homological_direct and iterative_direct_a..e on the same generator/flow, never local restatements or weakenings; (2) proofs sound; (3) hygiene. Audit ONLY KAM/Planetary/Averaging/Direct.lean (compare with branch inp-n67).
