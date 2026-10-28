# N10-3 prover handoff (branch inp-n103, 4c45d229; offloaded package run by the main orchestrator)


**Files:** new `KAM/Nekhoroshev/Assembly/Confinement.lean` (170 lines). Imports `Assembly.Hypotheses` and
`Poschel.Theorem1`.

**Declarations (signatures verbatim):** `cf_orbit`, `cf_branch`, `confinement`.
Private helpers: `cf_mem_realNbhd`, `cf_fderiv_apply`, `cf_hess`, `cf_setting`.

**Approach:**
- `cf_setting` builds `Theorem1Setting {J | ‖J‖ ≤ R/2} r0 s1 mu B ell h f` locally from
  `hypotheses_check` and `choice_props`. The Hessian clause is bridged from `complexHessian` through
  `cf_fderiv_apply`, and the QC clause is a case split on `hc_qc`.
- `cf_branch` applies `thm1` branch (a). It takes F to be the total field of `realHamiltonian h f`
  (`realH (h+f) = realHamiltonian h f` by `rfl`, so the locality helper is not needed). The branch
  condition comes from `hc_exc`. `omega0` supplies attainment and the lower bound, and `hc_time` gives
  `Om0 ≤ √n M`. `head_time_prefactor` then gives `2T ≤ A² s1/Om0`.
- `confinement` uses `cp_rad` (the exp argument equals `c ε^-a`, and `R0/2·(…)^a = rho/2`),
  `T_pos`, and `rho ≥ 0`.

**Checks:**
- Gate build `KAM.Nekhoroshev.Assembly.Confinement`: completed successfully, no warnings in my file.
- `scripts/lint_sources.sh`: check_lean_modules PASS (880 files), FROZEN-ANCHOR GUARD OK, ABI HASHES OK.
  It also prints "KAM.lean is out of date" (generated; not edited, per rule).
- `#print axioms` of `confinement`, `cf_branch` and `cf_orbit`: `[propext, Classical.choice, Quot.sound]`.
- No lines over 100 columns, no sorry, no heartbeat options.

**Uncertainties / errata / deviations:** none. No signature changed and no extra hypotheses.

AUDIT FOCUS: design docs/tracks/N/design/N10-LEAN-DESIGN.md row N10-3 (cf_orbit, cf_branch, confinement) and its audit DESIGN-N10-design-audit-1.md; signatures /root/code/KAM-inp/.drafts/design/N10Signatures.lean; the reconciled Part 9 thm1 consumption. Audit ONLY KAM/Nekhoroshev/Assembly/Confinement.lean. Common to all: (a) every declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established; an exported lemma named after a graph node must state that node's literal conclusion; steps the design keeps internal may stay internal; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public helper short name, no root shadow, lines <= 100.
