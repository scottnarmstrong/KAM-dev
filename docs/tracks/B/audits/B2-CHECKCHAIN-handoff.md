# Handoff B2-CHECKCHAIN

Files: new `KAM/EffectiveStability/OscillatorChainCheck.lean` (190 lines). Nothing else touched.

Declarations: `OscChainCert n` (data only: H Nact P steps δc εb T a b η r); `oscStepOKB` + `oscStepOKB_sound`;
`oscChainOKB` + `oscChainOKB_sound` (uses the `cartEqCheck` disjunct of `OscLieOK`); `oscDomOKB` + `oscDomOKB_sound`
(radii `r : List ℚ` read by `getD`, cast to ℝ); `checkOscChain (c : OscChainCert n) : Bool`;
`checkOscChain_sound (c) (hc : checkOscChain c = true) (w₀) (hw₀ : ∀ j, oscillatorAction w₀.2 w₀.1 j ≤ (c.a.getD j 0 : ℝ))`
: conclusion of `oscillatorChain_confinement` with `H := c.H`, `l := c.steps`, `a/b/η/r/T/εb/δc` cast from `c`.
Smoke: `harmonicChainCert` (2 zero generators, n=1), `harmonicChainCert_check : checkOscChain _ = true := by decide +kernel`,
`harmonicChainCert_zeroDrift` (via the soundness theorem).

Approach: Bool mirrors of OscStepOK/OscChainOK/OscDomOK with soundness by induction on the chain; checkOscChain
conjoins CartFits (cartFitsB), cartActOnly, chain/domain checks, positivity, and per-`i ∈ List.range n` r/b/η/drift/margin
inequalities (drift uses `oscChainBound n c.steps c.H` in ℚ); soundness unpacks and applies `oscillatorChain_confinement`.
No conclusion-shaped premises. No signature changes.

Checks: `b_build.sh … KAM.EffectiveStability.OscillatorChainCheck` succeeded, no warnings. `scripts/lint_sources.sh` OK
(frozen guard, ABI hashes, 25 tests). Line-length script: `[]`. Short-name check: OK (exit 0). Kernel check of
`checkOscChain harmonicChainCert = true` (decide +kernel): type checking 26.2 ms (profiler).
`#print axioms` of checkOscChain_sound, harmonicChainCert_check, harmonicChainCert_zeroDrift, oscChainOKB_sound:
[propext, Classical.choice, Quot.sound].

Design signals: none (default heartbeats). Errata: none. Deviations: none (OscLieOK only checked via cartEqCheck disjunct,
as requested, so the literal-equality disjunct is not accepted by the checker).

## AUDIT FOCUS (kam-b1)
Track B, program B2 (overnight D71; nothing frozen; OD-B7). Brief: /root/code/KAM-inp-b1/.drafts/B/brief-B2-CHECKCHAIN.md and
brief-B1-common.md. Combines the landed, audited B2-CHECK pattern (OscillatorCheck.lean) with the audited B2-MULTI theorem
oscillatorChain_confinement (OscillatorChain*.lean; batch 8 in landing). Check: (1) checkOscChain is a total computable
Bool over data only and encodes EVERY non-binder premise of oscillatorChain_confinement faithfully (no premise dropped,
weakened or mis-indexed; OscStepOK/OscChainOK/OscDomOK Bool mirrors and their soundness by induction; ℚ→ℝ casts;
oscChainBound in ℚ); (2) checkOscChain_sound's only hypotheses are hc and the initial chart-box condition; its conclusion
is oscillatorChain_confinement's with data from c; (3) kernel evaluation only (no native_decide/ofReduceBool);
(4) hygiene (AGENTS rules 3, 4, 7; widths ≤ 100), names, axioms. Memory rule: every lean/lake call wrapped in
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
