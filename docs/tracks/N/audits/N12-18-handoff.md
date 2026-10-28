# N12-18 prover handoff (branch inp-n1218, 0e80171; contains N12-01..N12-17 (all audited); offloaded package run by the main orchestrator; prover on claude-10)


**Files changed:** KAM/Provider/Nekhoroshev/AveragingMean.lean (54 lines), AveragingMost.lean (52 lines). Nothing else; no Frozen/manifest/KAM.lean edits; not sealed.

**Nodes:** `bpN:p0:avg-mean` -> `KAM.Provider.Nekhoroshev.averaging_mean`; `bpN:p0:avg-most` -> `KAM.Provider.Nekhoroshev.averaging_most`. Signatures copied verbatim from N12Signatures.lean (identical to the frozen binders/conclusions).

**Approach:** each imports only `KAM.Nekhoroshev.Averaging.Mean` / `.Most` (no frozen theorem anchor, no provider). Build `AveragingData n R s h f := ⟨by omega, hR, hs, hh, hf, hrank⟩` (1≤n from 2≤n); apply `averaging_mean_core` (ε₀ = 1) resp. `averaging_most_core` (ε₀ = 1, η₀ = R/8; 0<R/8 and R/8≤R/4 by linarith). `avgH h f ε` unfolds definitionally to `realHamiltonian h (fun w => (ε:ℂ)*f w)`, so the core conclusions are accepted by `exact`.

**Checks:**
- `inp_lake_build.sh` on both provider modules: Build completed successfully (3251 jobs); no sorry warnings in my files (warnings shown are pre-existing in other files).
- `#print axioms` for both providers: `[propext, Classical.choice, Quot.sound]`.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; it reports "KAM.lean is out of date; run scripts/gen_root_imports.py" (generated file, not edited per rules; orchestrator regenerates).

**Uncertainties / errata / deviations:** none. No heartbeat design signals; no overrides used.

AUDIT FOCUS: this package supplies the PROVIDERS for two frozen anchors, so the sub-orchestrator will seal on this audit (D26). Design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-18 and Appendix A; frozen anchors KAM/Frozen/Nekhoroshev/Theorems/AveragingMean.lean and AveragingMost.lean and their manifest entries. Refute-first: (1) KAM.Provider.Nekhoroshev.averaging_mean and averaging_most have types IDENTICAL to the frozen KAM.Nekhoroshev.averaging_mean / averaging_most: check by an exact-type probe 'example : <frozen type> := KAM.Provider.Nekhoroshev.averaging_mean' (and most) elaborated in a transient untracked file, no coercion or unfolding beyond defeq of identical terms; binder order, implicit/explicit status and constant scope identical; (2) the providers import frozen DEFINITIONS only, never the frozen theorem anchors, and nothing outside the provider imports them (quarantine; run scripts/check_frozen_anchors.py); (3) no file under KAM/Frozen changed; (4) the whole closure is sorry-free with only propext, Classical.choice, Quot.sound, and kernel replay passes; (5) the cores averaging_mean_core/mean_family (N12-16) and averaging_most_core (N12-17) are consumed without extra hypotheses: every premise the cores need is discharged from the frozen statement's own hypotheses; (6) hygiene. Audit KAM/Provider/Nekhoroshev/AveragingMean.lean and AveragingMost.lean.
