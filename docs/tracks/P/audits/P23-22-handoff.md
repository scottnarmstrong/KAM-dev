# P23-22 prover handoff (branch inp-p2322, fcbf6466; contains inp-p2320 (passed) with P23-18/17; P23-19 and P23-21 on inp; offloaded package run by the main orchestrator)


## Files (new; all < 200 lines; no existing file edited)
- KAM/Planetary/TwoScale/TheoremInverse.lean: KamHyp.freq_real, realFreq_injOn, exists_inverse_locus (unique source inverse locus), inverse_local, inverse_global.
- KAM/Planetary/TwoScale/TheoremTorus.lean: rhoHat_le_rho, KamHyp.phi_injOn, i_injOn, Hr_differentiableAt, lattice_torus_of_limit.
- KAM/Planetary/TwoScale/Theorem.lean: `two_scale_kam`, signature copied VERBATIM from P23Signatures.lean (docstring included), proved.

## Approach
Joint construction on the witnesses of one `tori_limit_of_iterative` (Ds,hs,fs,Ψ,Φ,is,i,Φinf). I₀ chosen by `choose!` from the unique inverse locus (reality + injectivity of freq on real D, from KamHyp); K ω θ := Φinf (θ, i (I₀ ω)); KC from tori_estimates_of_limit via choose!. The `i` of limit_actions_of_steps (needed for the 2560 Lipschitz clause) is identified with ToriLimit's `i` by uniqueness of uniform limits on Ds 0. Per ω: IsLatticeTorus by lattice_torus_of_limit following the P23-20 audit table (L1 lagr/estimates + Hr differentiability via kam_G_diff and 32Ê ρ̂ ≤ ρ; L2 phi_per; L3 injectivity of Φinf from 768nÊ<1, k=0; L4/L5 lagr; L6 invariance). Cross-ω injectivity mod lattice: Φinf and i injective (768nÊ<1, 2560nÊ<1), then ω = realFreq(I₀ ω). Inverse-frequency estimates: ball continuation (Inverse.ball) at real points, injectivity puts the second point in the ball; global case via diam D. Measure clause: meas_torus_final (P23-21) with the same i, I₀, Φinf, K. No new premises; `hL` is unused (the signed statement carries it; KamHyp.L_bound suffices upstream).

## Checks
- Gate builds of TheoremInverse, TheoremTorus, Theorem: success, no sorry, no errors. Only unused-variable/linter style warnings.
- `#print axioms two_scale_kam`: [propext, Classical.choice, Quot.sound].
- scripts/lint_sources.sh: only "KAM.lean is out of date" (generated, not edited); modules, frozen guard, ABI hashes OK.
- No set_option, no heartbeat overrides, no EuclideanSpace; new public names grepped for uniqueness.

## Uncertainties / errata / deviations
None found. No source defect. The helper `rhoHat_le_rho` and others are public in KAM.Planetary (checked unique). Theorem.lean imports `Measure` facade (MeasureJoint) and Tori; no provider/DRAFT_SORRY import.

AUDIT FOCUS (design docs/tracks/P/design/P23-LEAN-DESIGN.md revision 2: row P23-22 (line ~286), the node table rows mapped to 'two_scale_kam / local:...' (e.g. lines 129, 168-170 and all others), N2 and its PRIVATE-INTERFACE RELEASE GATE; P23 design audits; signatures /root/code/KAM-inp/.drafts/design/P23Signatures.lean line ~811; the P23-20 audit's IsLatticeTorus discharge table): (1) two_scale_kam = signature file EXACTLY (byte-compare the declaration header and type; its docstring too); (2) the private-interface release gate: every private conditional helper of P23-17, P23-18, P23-20 and P23-21 is APPLIED here with its premises discharged from proved outputs of iterative or from source premises of two_scale_kam; no conditional premise is left undischarged; shared witnesses are preserved across iteration, limits, tori and complement estimate (design item 7, line 30); (3) every graph node the node table maps to two_scale_kam (including the local named obligations such as limit_actions, la-wp, la-tele, ... and the inverse locus / inverse-frequency estimates) is actually established inside the proof or as an exported helper: list each node with where it is discharged; (4) IsLatticeTorus L1-L6 discharged as the P23-20 audit table prescribes; (5) proof soundness of the unique inverse locus (reality and injectivity of freq on real D), inverse_local/inverse_global; (6) hygiene (no EuclideanSpace; no public short name used elsewhere in KAM; no root shadow). Audit KAM/Planetary/TwoScale/Theorem{,Inverse,Torus}.lean (Tori* and Measure* were audited in P23-20/P23-21; read them as needed).
