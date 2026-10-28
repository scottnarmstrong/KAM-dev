# N11-L2 prover handoff (branch inp-n11l2, b19962d0; offloaded package run by the main orchestrator)


**Files:** new `KAM/Nekhoroshev/Partial/Energy.lean` (535 lines, all lines <= 100 cols). Nothing else changed
(KAM.lean not regenerated: `scripts/lint_sources.sh` reports only "KAM.lean is out of date", expected until the
orchestrator regenerates; the other lint checks PASS, frozen-anchor guard and ABI hashes OK).
Commits: 1fd97529 .. final on inp-n11l2.

**Declarations:** `KAM.Nekhoroshev.energy_free` (signature copied verbatim from N11Signatures.lean L583-596,
RealFastConvex only; bpN:p11:energy-free). Graph steps ef-tube, ef-adm, ef-en(-energy/-taylor/-split),
ef-id (via L1 `energy_identity_re`), ef-C (via L1 `transverse_pairing`), ef-contra are all internal private
lemmas/steps of this module: `ef_mem_realDom_of_tube` (tube), `ef_contra` (adm/en/C/contra), `ef_arith`
(final numerics), `ef_energy`, `ef_bracket_bound`, `ef_theta_bound`, `ef_freq_lip`, `ef_taylor_segment`.
All helpers are private with `ef_` prefix (no new public names).

**Approach:** by contradiction; `exit_ball` (Part 7, euclid norm) gives first exit time ts with |ΔI|=r/4.
On [0,ts]: orbit lies in realDom(r/2) (slow margin + |I-Ic|<r/2); P := orthogonal projection onto resSpan Λ;
‖Pω(I0)‖ <= 5δ/4 (dual NearResonance + M-Lipschitz ω via hessian_real); L1's `transverse_pairing` bounds
|ω0·(ΔI-PΔI)| with B1=5ηε/(rs) (bracket on Dom(r/2,s/2) via `bracket`+`bracket_dominated`),
B2=η/(es), B3=M r/4, B4=5δ/4; Lagrange Taylor of realPart h along the fast segment + real energy
conservation give (m/2)Δ² <= A + (5δ/4)Δ + C; `ef_arith` shows this is absurd using only exp 1 >= 2
(sharper than the blueprint's 1/e<0.3679; total 0.0094 m r² < 0.0117 m r²).
Taylor/Lipschitz bodies are copies of the private Part 7 lemmas (taylor_segment, hess_lipschitz), renamed;
Hessian operator bound derived from `RealFastConvex.hessian_real` by Cauchy–Schwarz (`ef_hess_abs_le`).

**Checks:** `inp_lake_build.sh /root/code/KAM-inp-n11l2 KAM.Nekhoroshev.Partial.Energy` -> Built (3280 jobs),
no warnings in Energy.lean. `#print axioms KAM.Nekhoroshev.energy_free` ->
[propext, Classical.choice, Quot.sound]. No sorry/axiom/maxHeartbeats/EuclideanSpace; default heartbeats.

**Uncertainties / deviations / errata:** none. Statement needed no extra hypotheses. No heartbeat design signals.
Note: blueprint step ef-adm quotes M·ρ' = δ/4 through the mean-value inequality on the ball; implemented as such.
Minor: Mathlib deprecation `push_neg` avoided (`push Not`).

AUDIT FOCUS: design docs/tracks/N/design/N11-LEAN-DESIGN.md row N11-L2 (energy_free with RealFastConvex only) and its node table; both N11 design audits; signatures /root/code/KAM-inp/.drafts/design/N11Signatures.lean. Audit ONLY KAM/Nekhoroshev/Partial/Energy.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
