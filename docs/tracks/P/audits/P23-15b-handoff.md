# P23-15b prover handoff (branch inp-p2315b, d6199e6; contains inp-p2313j: the complete signed osc_iter; offloaded package run by the main orchestrator; prover on claude-10)


Branch `inp-p2315b` (worktree /root/code/KAM-inp-p2315b), includes orchestrator commit dcaffd1 (fastShift -> oscFastShift).
Both rules respected: no heartbeat override anywhere; largest file 378 lines.

## Files (all new, in KAM/Planetary/Averaging/)
- `OscillatorHyp.lean` — `OscHyp`, copied verbatim from P23Signatures.lean. DEVIATION: the design says P23-06 owns
  it, but it was not on `inp` (grep found none), so it is defined here.
- `OscillatorFiniteSched.lean` — `OSched` (three `Sched`: action/rp/rq with strip in `x`), recursive `(gᵢ,fᵢ)`
  (`seq`, `G`, `F`, `Φ`, `inc`, `U`), premise bundle `OIter`, stage data `OStepConc`.
- `OscillatorFiniteStep.lean` — `ostep_conc`: stage conclusions obtained from the COMPLETE `osc_iter` (earlier zero-mode
  increments as `gj`, same maps), `oinv_all`, `OIter.stage`.
- `OscillatorFiniteChain.lean` — telescope/chain: structure, fast-lattice law, reality, Hamiltonian identity, four
  summed displacements (`OIter.struct/ident/disp`).
- `OscillatorFiniteGen.lean` — θ-independence of `G`, `g - f̂₀` = sum of later increments (class + bound).
- `OscillatorFiniteNumerics.lean` — real inequalities (steps with factor b = 1+m, `firstEps = 293 b E²/P`).
- `OscillatorFiniteSetup.lean` — `OscGood`, `oiter_of_hyp`, `realOn_h_of_real`, `osc_E_le`.
- `OscillatorFiniteSingle.lean` — Case B (single doubled-loss step).
- `OscillatorFiniteMulti.lean`, `OscillatorFiniteCaseA.lean` — Case A (N = ⌊κ/(12 ln 2)⌋ steps), weights `oscW`, `MultiData`.
- `OscillatorFinite.lean` — facade: `osc_averaging`, `averaged_remainder` (signatures verbatim), `osc_zero_mode`.

## Approach
Following the source (P2 L198-220): Step 0 with losses (r/8, rp/8, rq/8, s/6); Case A (e^{-κ/6} ≤ 2 b y₀): N steps with
losses (·/(8N), s/(4N)), ε₁ = 293 b E²/P ≤ E/(13κ), εᵢ = ε₁ 4^{1-i}; Case B: one step with doubled losses. Each stage is
`osc_iter` on the stage domain; reality of g, f carried via the conditional reality clause; maps composed with N6-4
`telescope`. g correction (`g - f̂₀`, ≤ 400 b E²/P) and tail (`fs`, ≤ e^{-κ/6}E) kept separate. `averaged_remainder`
= `osc_averaging` with E=μ, f=μ•P, s=s₀, plus `osc_zero_mode` (class/reality of the zero mode of f from stage 0),
linearity of the zero mode, and exp(-(2πK s₀)/6) = ε⁵ for the chosen K.

## Checks
- `inp_lake_build.sh` of KAM.Planetary.Averaging.OscillatorFinite (all 11 modules): success (9164 jobs); only warnings:
  unused `hμ`, `hP` in `averaged_remainder` (signature binders kept verbatim; see uncertainties).
- `sh scripts/lint_sources.sh`: no over-long lines, check_lean_modules PASS, frozen guard OK, ABI hashes OK; the only
  message is "KAM.lean is out of date" (generated; not touched).
- `#print axioms KAM.Planetary.osc_averaging` and `...averaged_remainder`: [propext, Classical.choice, Quot.sound].
- No sorry/axiom/admit/unsafe/opaque; no maxHeartbeats.

## Design signal
The first monolithic `oscGood_multi` hit the default heartbeat limit (single declaration); fixed by splitting into
`MultiData` lemmas (`hstage`, `step_zero`, `step_succ`, `small`, `first_facts`), not by raising the budget.

## Uncertainties / observations
- `averaged_remainder`'s hypotheses `hμ : 0 < μ` and `hP : oscBound ... P 1` are unused (the proof only needs `H`; note
  `H` already carries `oscBound ... (μ•P) μ`). The `hε` upper bound `ε < exp(-1/5)` is also unused beyond `0 < ε`
  (κ ≥ 6 is in `H.budget`). Not an error, but the signature is stronger than necessary.
- `osc_averaging` / `averaged_remainder` statements were not changed; no extra premises added.
- Case B displacement uses (3/e)E ≤ 3E and 4E ≤ 9E (slack, not sharp).

## Suspected errata
None found in the pinned sources.

## Deviations
`OscHyp` defined in `OscillatorHyp.lean` (see above). New helper `coeff_const_mul_flat'` (public copy of a private
lemma of OscillatorSeriesAlgebra; no edit of that audited file).

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md row P23-15 ('osc_averaging, averaged_remainder; g correction and tail stay separate') and revision 3; audits; signatures .drafts/design/P23Signatures.lean incl. OscHyp): (1) osc_averaging, averaged_remainder (and OscHyp if signed) = signature file exactly; (2) proofs sound: osc_iter consumed exactly as signed; the N-step schedule (Case A), multi-step chain and numerics proved, not assumed; the g correction and the tail kept separate as designed; the heartbeat design signal was fixed by splitting oscGood_multi into MultiData lemmas (confirm no budget override anywhere); no added premises; (3) hygiene (no EuclideanSpace; oscFastShift naming; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/Averaging/OscillatorHyp.lean and OscillatorFinite*.lean (the M entries in the diff are rename ports).
