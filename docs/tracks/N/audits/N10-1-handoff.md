# N10-1 prover handoff (branch inp-n101, 3929ba2; off inp with inp-design-n10; offloaded package run by the main orchestrator; prover on claude-12)


**Files:** new `KAM/Nekhoroshev/Assembly/Choice.lean` (~150 lines). No other file touched.

**Declarations (signatures verbatim from N10Signatures.lean):** `HeadParams.s1/F1/eps1/R0/epsPrime/tau/rho`,
`choice`, `choice_props` (bpN:p10:choice-props), `cp_dict` (stepN:p10:cp-dict), `cp_rad` (cp-rad),
`cp_size` (cp-size, ex-rho), `head_time_prefactor` (hc-time arithmetic). Private helpers: `eps1_pos`, `F1_pos`,
`epsStar_eq`, `F_eq`.

**Approach:** reuse `Interfaces/Constants` lemmas. `choice_props` from `*_pos`, `const_eps0`, `const_size`, `two_mu_le_B`,
`r0_le_*`. `cp_dict`: `epsStar = 2π ε₁`, `F = 2π F₁` by unfold/ring; equivalence via `epsStar/F = ε₁/F₁`. `cp_rad`: rewrite
`const_conclusion` using `Fε/ε* = ε'/ε₁`. `cp_size`: rpow monotonicity + `const_eps0`. `head_time_prefactor`: apply
`const_time_arith` at `Ω₀ = 2πΩ` (using `√n ≤ n`).

**Checks:**
- `inp_lake_build.sh … KAM.Nekhoroshev.Assembly.Choice`: "Build completed successfully (2896 jobs)", no warnings.
- `scripts/lint_sources.sh`: check_lean_modules PASS (415 files); FROZEN-ANCHOR GUARD OK; ABI HASHES OK. It also prints
  "KAM.lean is out of date; run scripts/gen_root_imports.py" (new module not in the generated root; I did not edit KAM.lean — orchestrator to regenerate).
- `#print axioms` (via `lake env lean`) of all five theorems: `[propext, Classical.choice, Quot.sound]`.
  (`inp_sig_check.sh` could not be used: it reads the shared inp build, which lacks this new olean.)

**Uncertainties / errata / deviations:** none. No signature changed; no heartbeat options; no statement found false.
Design signals: none (default heartbeats, 12 s build).

AUDIT FOCUS (design docs/tracks/N/design/N10-LEAN-DESIGN.md row N10-1 and proof plan; its audit DESIGN-N10-design-audit-1.md; blueprint-N p10 choice of constants): (1) statements = design signatures and blueprint (the choice definitions and their properties: dictionary, radii, sizes, time prefactor, with the stated constant dependences); (2) definitions are the intended objects (no junk values); (3) hygiene (lint incl. 100-char lines). Audit ONLY the N10-1 module (KAM/Nekhoroshev/Assembly/Choice*).
