# P11A-P10 prover handoff + anchor batch for fixedSunPlanetaryKAM (branch inp-p11ap10, 1fe7689c; built on inp (P8e: prepared/amount/data_star landed) with P13-C (passed, parametric provider) merged; offloaded package run by the main orchestrator)


## Files (all new, KAM/Planetary/Preparation/, each < 300 lines)
WrapperReal (complex-symplectic -> real chart `p11_realChart`), WrapperParts (real factors PsiR/FastR),
WrapperChain (chain Xi_eps: `p11_wr_chain`, `p11_wr_dom`, `p11_wr_chain_eq`), WrapperTube +
WrapperTubeMain (`p11_wr_tube`), WrapperDatum (datum `p11WrDatum`, `p11_periodic_int`), WrapperQI
(`p11_wr_qi`), WrapperSmall (`p11_wr_small`), WrapperAsym (`p11_ev_thr`, `p11_ev_slowDisp`,
`p11_ev_tube`), WrapperTransport, WrapperMeasure, WrapperEps (`p11_wr_xi`, `p11_wr_torus`,
`p11_wr_set`), Wrapper (`wrapper_of_data_star`).
One edit outside: Polar.lean `p11PolarScale_apply` made non-private (needed for real polar formulas).
inp merged twice (last merge clean; no `p11_pr_b` use here).

## Theorem
`wrapper_of_data_star (D : P11Physical n) (hDS : <literal conclusion of data_star D>) :
 ∃ eps0, 0 < eps0 ∧ ∀ eps, 0 < eps → eps < eps0 → ∃ S, MeasurableSet S ∧ 0 < volume S ∧
 volume S < ⊤ ∧ S ⊆ circularTube D.G D.m0 D.m D.a (p11Zeta D) ∧ ∀ z ∈ S, ∃ w K theta0, z = K theta0
 ∧ range K ⊆ S ∧ IsPhysicalTorus (fixedHamiltonian D.G D.m0 D.m eps) w K` (exactly the signed wrapper).
Checked: `fun D => wrapper_of_data_star D (data_star D)` typechecks against the landed `data_star`
(Datum.lean), so `theorem wrapper D := wrapper_of_data_star D (data_star D)` is the one-line closer.
No other conclusion-shaped premise: data_star's conclusion is the only hypothesis; everything else
is landed (holo_chart, avg_fast, avg_slow, total_chart, forward_tube, weak_kam_quantitative_full,
P1 transport/Liouville, measure box bound).

## Steps -> Lean
- wr-nu: nu := max((mu+2)B0+2, 2(mu+2)G0+4) (kappa_D = 1/2, a_D = G0, B0 = p11c_B0 of the fixed datum
  d_*, from `weak_kam_quantitative_full`); eps0 from `p11_wr_small` (specs, hpe, hsm), `p11_ev_thr`
  (eps_f <= c_* beta^B0 and displacement <= 1/2), `p11_ev_slowDisp`, `p11_ev_tube`.
- wr-kam: `p11_wr_qi` (admissibility A1-A4 + hol/per/real from P11PreparedFullSpec) then the
  family of `weak_kam_quantitative_full` (cDelta, cD uniform in beta).
- wr-chain: `p11_wr_chain` (Xi_eps real analytic eps-chart on the real prepared domain, (Q1)-(Q2)
  for the full lattice); `p11_wr_chain_eq`, `p11_wr_link` (H_fix∘Xi = eps(N+P)).
- wr-tor: `p11_wr_torus` (torus_transport_phys via phaseCast n*2 = n+n, `p11_isPhysicalTorus_cast`).
- wr-meas: `p11TorusUnion_props`, `p11_wr_set` (liouville_lattice, mp_a_box finiteness).
- wr-tube: `p11_wr_tube` (Gamma_i <= 2n eps via real orthogonality `p11_orth_sq`; forward_tube).
Domain used is real points with actions within 1 of the box (|I|<3/2 < pi/2 requirement), strictly
larger than needed; tori have |I| <= 1 since displacement <= 1/2.

## Checks
Gate build of KAM.Planetary.Preparation.Wrapper and Datum: success, no warnings in Wrapper* files.
`scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK
(it prints "KAM.lean is out of date" — generated root, not touched).
`#print axioms` of wrapper_of_data_star, p11_wr_chain, p11_wr_tube, p11_wr_torus, p11_wr_set,
p11_wr_qi: [propext, Classical.choice, Quot.sound]. No sorry/maxHeartbeats; lines <= 100.
Design signal: p11_wr_tube and a first nlinarith in p11_tube_sq hit the default heartbeat limit and
were split into small lemmas (no override used).

## Uncertainties / errata / deviations
None found in sources. Deviation: tube lemma hypotheses (hP1,hP2,hR1,hR2) are numeric smallness
conditions discharged eventually; ν2 is fixed before eps as required. Wrapper only needs
`data_star` for the first conjuncts (compactness, volume 1) and the per-eps full spec/amount.

ORCHESTRATOR ADDITIONS (04:25, commit 1fe7689c): after the prover finished, the orchestrator merged inp-fx13c (P13-C, passed audit P13-C-audit-1) and added four one-line applications, each VERBATIM from the signature files: KAM.Planetary.wrapper := wrapper_of_data_star D (data_star D) (Preparation/Wrapper.lean); FixedAssembly.n_general := n_general_of_wrapper (fun D => wrapper D) ... (FixedAssembly/General.lean); FixedAssembly.fixed := fixed_of_wrapper (fun D => wrapper D) ... (FixedAssembly/Main.lean); the provider KAM.Provider.Planetary.fixedSunPlanetaryKAM := fixedSunPlanetaryKAM_of_wrapper (fun D => wrapper D) ... (Provider/Planetary/FixedSunPlanetaryKAM.lean). Orchestrator pre-checks: the exact-type probe example : type_of% @KAM.Planetary.fixedSunPlanetaryKAM := @KAM.Provider.Planetary.fixedSunPlanetaryKAM elaborates; #print axioms of the provider, wrapper and fixed: [propext, Classical.choice, Quot.sound]. Rulings OVERNIGHT 03:25 and 03:50 (parametric pattern). The prover also made one landed lemma public: p11PolarScale_apply in Preparation/Polar.lean (private -> public, statement unchanged).

AUDIT FOCUS (package + SEAL-KEY audit of the frozen anchor KAM.Planetary.fixedSunPlanetaryKAM): (1) wrapper_of_data_star: its ONLY non-source hypothesis is VERBATIM the conclusion of the signed data_star; its conclusion is VERBATIM the signed wrapper (/root/code/KAM-inp/.drafts/design/P11ASignatures.lean ~1196, ~1282); the wr-* steps (design node table: wr-nu, wr-kam, wr-chain, wr-tor, wr-meas, wr-tube) are each established, the exported p11_wr_* lemmas state their literal node conclusions; no conclusion-shaped premise anywhere in the 14 Wrapper*/Polar modules; (2) the four one-liners are VERBATIM the signature files (P11ASignatures.lean wrapper; P1213Signatures.lean n_general ~330, fixed ~343, provider fixedSunPlanetaryKAM ~370); (3) SEAL KEY: re-run the exact-type probe yourself; in a SCRATCH COPY of KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.lean (never edit the real one) replace only the frozen body by 'by exact KAM.Provider.Planetary.fixedSunPlanetaryKAM' with the provider import, and check it compiles; #print axioms of the provider and of that scratch seal: only propext, Classical.choice, Quot.sound; provider quarantine: nothing but the frozen anchor may import the provider module (grep); (4) graph nodes bpP:p11:wrapper, wr-*, bpP:p13:n-general, bpP:p13:fixed and the anchor root bpP:p0:fixed. Audit KAM/Planetary/Preparation/Wrapper*.lean, KAM/Planetary/Preparation/Polar.lean (the visibility change only), the four one-liners in Wrapper.lean, FixedAssembly/General.lean, FixedAssembly/Main.lean and KAM/Provider/Planetary/FixedSunPlanetaryKAM.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
