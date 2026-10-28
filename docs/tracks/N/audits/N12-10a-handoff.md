# N12-10a prover handoff (branch inp-n1210a, cb412a7; base inp-n1201; offloaded package run by the main orchestrator; prover on claude-12)

Files: new KAM/Nekhoroshev/Averaging/FlowDefs.lean (~100 lines).
Nodes: bpN:p12:s-flow#data: avgMaximal, avgTm, avgTp, avgFlow, avgFlowDomain, avgOmega, avgMaximal_spec (signature verbatim).
Approach: private data_smul gives `Data n R s |ε| h (ε f)`; holo_input -> avgH C^∞ on Wdom; ham_smooth_c1 + mono to avgDomain; KAM.ODE.gen_maximal existence; Classical.choose_spec of the dite. No differentiability premise.
Checks: gate build KAM.Nekhoroshev.Averaging.FlowDefs OK (no warnings); scripts/lint_sources.sh: PASS (only "KAM.lean is out of date", expected, not edited); FROZEN-ANCHOR GUARD OK; ABI HASHES OK.
#print axioms avgMaximal_spec: [propext, Classical.choice, Quot.sound].
Uncertainties/errata/deviations: none. No heartbeat issues. Imports added beyond Field: HoloReal, ODE.Maximal, ODE.Hamiltonian (public). KAM.lean needs regeneration by orchestrator.

AUDIT FOCUS (design docs/tracks/N/design/N12-LEAN-DESIGN.md row N12-10a and proof plan; audits DESIGN-N12-design-audit-{1,2}.md; signatures .drafts/design/N12Signatures.lean): (1) statements/definitions = design signatures (choice definitions and avgMaximal_spec, NO differentiability premise; choice only from proved existence/uniqueness, no arbitrary fallback); (2) proofs sound; (3) hygiene. Audit ONLY the FlowDefs module.
