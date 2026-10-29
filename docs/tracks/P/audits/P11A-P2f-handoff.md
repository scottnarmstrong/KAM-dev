# P11A-P2f prover handoff (branch inp-p11ap2f, 41f4d35a; contains P11A-P2, P2b, P2c, P2d (passed) and P2e (audit 1 FAIL F1, closed here); offloaded package run by the main orchestrator)


Hard rules observed: no heartbeat overrides, files 86 / 270 lines, no sorry/axiom/admit/unsafe/opaque, no
EuclideanSpace, no frozen/manifest/KAM.lean/README edits, no provider import, lines <= 100.

## Files
* NEW `KAM/Planetary/Preparation/HoloShrink.lean` (86): `P11HoloData.shrink d r` (every clause is monotone in rC).
* NEW `KAM/Planetary/Preparation/HoloAssembly.lean` (270): signed `holo_chart`, `p11SecularData`,
  `total_chart_transport` (verbatim), helpers `p11_J0_close`, `p11_F_real_eq`, `P11SecularSpec.chart_part`,
  `p11PolarR_fast_shift`, `append_int_add`. NOTE: it is a separate module that imports Holomorphic (not imported
  BY Holomorphic: import cycle, HoloData imports Holomorphic). Consumers of `holo_chart`/`p11SecularData`/
  `total_chart_transport` must import `KAM.Planetary.Preparation.HoloAssembly`.
* CHANGED `HoloData.lean` (P2b): new field `Omega_real` of `P11HoloData` (+ its proof in `p11_holo_data`;
  `Omega = 2 pi G`, `G` the real complexification). **Closes P2e audit F1** (hOmega is now discharged from the
  interface: `d.Omega_real`; not a hypothesis of holo_chart). Equivalent to the suggested `p11_holo_data_real`.

## Approach
Base axis a = axis(J0/2pi) (ordered by p11_axis_mem_axes, action a = J0/2pi), so the strip centre is exactly J0/2pi.
(r', sigma') from `p11hs_strip_data`; d := d0.shrink (min rC (pi r'/2)); sigma = sigma'/4;
rz = min{1, r'/(2B), pi sigma'/(2 n B'), min(1,delta)/B}; `P11HsHyp` built from d's fields;
MF = max{1, coth(pi sigma)^n MInf, p11MeanM0}. F = p11hsF, C J = F0(J,0), mean by `p11_hc_mean`, F clauses by
`p11hs_F`, chart clauses by `P11HoloData.chart_spec`, with the real-point identification hF proved here
(`p11_F_real_eq` from `p11hsF_real_eq` + `chartInput_eq` + `perturbation D false = fFix o poincareProd` by rfl).
Every conjunct of P11SecularSpec/FullSpec discharged. total_chart_transport: `total_chart` composed with the
chart clauses; the fast shift is handled by `p11PolarR_fast_shift` (polar chart commutes with castAdd-angle
shifts), the slow shift by `total_chart`'s lattice. `hO`, `hshift` are unused (signature verbatim).

## Checks
* Gate: `inp_lake_build.sh . HoloAssembly HoloMean HoloChart HoloStrip` -> Build completed successfully (9295 jobs).
* `#print axioms holo_chart, total_chart_transport, p11SecularData`: [propext, Classical.choice, Quot.sound].
* `scripts/lint_sources.sh`: only "KAM.lean is out of date" (generated, new modules); check_lean_modules PASS,
  FROZEN-ANCHOR GUARD OK, ABI HASHES OK.

## Uncertainties / errata / deviations
No errata, no signature change, no design signal. Deviation: edit to audited P2b file HoloData.lean (new field,
see F1). Mean clause uses P2e's `p11_radial_schwarz_diag` rather than signed `p11_radial_schwarz` (P2e's note).
KAM.lean needs regeneration (HoloShrink, HoloAssembly).

## ruling 22:50: P11SecularSpec h-realness
`P11SecularSpec` in Holomorphic.lean amended (second conjunct now `(re = ...) ∧ im = 0`; only that conjunct,
re-wrapped to <= 100 columns). `P11HoloData` gets field `h_im` (proved by new `p11HoloH_im` in HoloScalar.lean,
`h = p11HoloH D`); `shrink` carries it; `holo_chart` combines `d.h_re`/`d.h_im`. Downstream uses unaffected
(HoloChart uses only `h_re`). Rebuilt: Build completed successfully (9295 jobs); lint unchanged (only
KAM.lean out of date); no line > 100 columns; axioms of holo_chart/total_chart_transport rechecked below.

ORCHESTRATOR RULINGS: (20:40) P11A-P2 split into P2b..P2f; P2f assembles the signed holo_chart, p11SecularData and total_chart_transport, plus the energy identity moved from P2d. (22:46) The signed P11SecularSpec is AMENDED: its second conjunct also states (C.h (realInclusion J)).im = 0 (P11ASignatures.lean lines 682-700); Holomorphic.lean's definition must equal that text (whitespace aside) and holo_chart must prove it. P2e audit 1 F1 (Omega realness premise hOmega of p11_hc_mean not exported by P2b) is to be CLOSED here: P2f adds an Omega_real field to P11HoloData and discharges hOmega from a proved producer.

AUDIT FOCUS: (a) holo_chart, p11SecularData, total_chart_transport and the amended P11SecularSpec = signature file EXACTLY; every conjunct of P11SecularSpec and P11SecularFullSpec is PROVED in holo_chart from the delivered pieces (P2b data, P2c F clauses, P2d chart/lattice, P2e mean, the energy identity), none assumed, no added hypothesis; (b) P2e audit 1 F1 is closed: hOmega comes from a proved producer, not an assumed field (the new P11HoloData.Omega_real must be proved by p11_holo_data / its strengthened producer); P11HoloData changes are compatible with P2b/P2c/P2d/P2e uses; (c) graph nodes bpP:p11:holo-chart and steps hc-* (assembly), and total_chart_transport; (d) also audit the CHANGES to Holomorphic.lean (P11SecularSpec amendment) and HoloData.lean (Omega_real). Audit the P2f modules: KAM/Planetary/Preparation/HoloAssembly.lean KAM/Planetary/Preparation/HoloData.lean KAM/Planetary/Preparation/Holomorphic.lean KAM/Planetary/Preparation/HoloShrink.lean  plus the diffs to Holomorphic.lean and HoloData.lean since inp-p11ap2d/inp-p11ap2e. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
