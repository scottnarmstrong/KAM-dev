# N11-J1 prover handoff (branch inp-n11j1, 961b2c65; contains N11-E1 (in audit) and its inputs; offloaded package run by the main orchestrator)


**Files:** new `KAM/Nekhoroshev/Partial/Preimage.lean` (~250 lines). Nothing else changed (KAM.lean untouched; lint reports it out of date, as expected).

**Declarations:** signed `KAM.Nekhoroshev.preimage` (`bpN:p11:preimage`), proved. Signature identical to N11Signatures.lean except line-wrapping (the signature line exceeded 100 columns). All other declarations are `private` (`preGaugeC/R`, `preCxCLM`, `preReCLM`, `symm_mem_Dom`, `extCx_snd_mem_base`, ...); no public helper added.

**Approach:** adaptation of `KAM.Stability.preimage` (Part 7). Gauge diag(σ⁻¹,ρ⁻¹) on `EC`/`ER` makes ν the Pi/Prod norm. Banach (`ContractingWith.exists_fixedPoint'`) on closedBall(gauge y, κ) for u ↦ gauge y − Re G(ι u); contraction 1/2 from `general_cauchy` on the OPEN complex ball of radius 1/2 (audit note: open-ball reading) plus the convex mean value inequality. The fast and slow components share the ρ scale, so ‖(Ψz−z).2‖ ≤ max(dI,dx) (`norm_snd_sub_le`). hbR, hbw are used only for λ ≠ 0 (real y lies on `b.base`). Real preimage lies in `realDom R` since ‖x.2−y.2‖ ≤ ρ/4 < R… (membership comes from the ball lemma).

**Checks:**
- `inp_lake_build.sh /root/code/KAM-inp-n11j1 KAM.Nekhoroshev.Partial.Preimage`: Build completed successfully (only a pre-existing unused-variable warning in Stability/Gradient.lean).
- `scripts/lint_sources.sh`: only failures were the >100-column signature line (since fixed, 0 lines >100 now) and "KAM.lean is out of date" (generated; not mine to edit). check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK.
- `#print axioms KAM.Nekhoroshev.preimage`: propext, Classical.choice, Quot.sound.

**Uncertainties:** none; no heartbeat overrides needed. **Errata/deviations:** none. The node table maps no further graph steps to this module.

AUDIT FOCUS: design docs/tracks/N/design/N11-LEAN-DESIGN.md row N11-J1 (preimage, positive margins; A, E1, general_cauchy and the Banach contraction) and its node table; both N11 design audits; signatures /root/code/KAM-inp/.drafts/design/N11Signatures.lean. Check whether 'positive margins' is a separate node or clause and that it is established. Audit ONLY KAM/Nekhoroshev/Partial/Preimage.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
