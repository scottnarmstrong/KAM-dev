# P11A-P10 independent package and seal-key audit 1

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-p11ap10`.
HEAD: `1fe7689ccefc15d75eace3ca2b13b6360db8a42b`.
Comparison `inp`: `e2ea540a1371a4719d004528644ab81134498bba`.

**Overall: FAIL for the advertised literal graph-slice completeness requirement.** Findings F2/F3 below prevent certifying that every unsigned graph-facing export establishes its literal node conclusion. **Anchor `KAM.Planetary.fixedSunPlanetaryKAM`: PASS WITH NOTES (mathematical provider seal-ready using the explicit-binder body).** Its exact type, unconditional proof and standard axioms pass independently. The exact bare seal command requested in the handoff fails (F1); the real frozen anchor remains `DRAFT_SORRY` and was never edited. These findings distinguish theorem soundness from literal graph delivery; no false theorem or extra premise in the unconditional provider was found.

## Authority and scope

Read AGENTS.md, PLAN, DECISIONS, the package audit brief, handoff/AUDIT FOCUS, Track P statement, signed P11A/P1213 interfaces, P11A design node table, Part 11/13 blueprint and relevant P graph packets, frozen anchor and its physical definitions. Compared the full `git diff inp...HEAD`, including inherited P13-C code and audit documents. The diff has 17 Lean files and two P13-C audit documents; Polar changes only private-to-public visibility. The explicit user report path overrides the brief's generic destination. Only this report is written in the repository; probes are isolated under `.lake/abi-scratch/` and removed after use. No state-changing git, source repair, frozen/manifest/generated-file edit, dependency edit, or resource override.

## Findings

**F1 — literal seal recipe fails; valid explicit-binder recipe passes.** `P11A-P10-handoff.md:55` requests replacing only the body by `by exact KAM.Provider.Planetary.fixedSunPlanetaryKAM`. The frozen declaration at `KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.lean:46` has explicit arguments already introduced before the proof. A renamed scratch copy with that exact body exits 1 at line 56: “Type mismatch”, provider has function type `2 ≤ ?m → ∀ G m0 ...`, but the goal is the existential conclusion. Its subsequent axiom print includes `sorryAx` because Lean recovered from the error; that failed scratch result is rejected, not evidence of a valid seal. The correct body, independently checked, is:

```lean
by exact KAM.Provider.Planetary.fixedSunPlanetaryKAM
  hn G m0 m a hG hm0 hm ha hsep eta heta
```

This passes with only `[propext, Classical.choice, Quot.sound]`, as does the exact-type probe. It follows the package brief's explicit-binder rule and DECISIONS D26. The frozen module's prose also advertises the bare recipe; report this inconsistency, do not edit the frozen file. No new mathematical premise is needed.

**F2 — smaller carrier in unsigned `p11_wr_chain`.** `blueprint-P/parts/p11-cp09-preparation.tex:250` says “real analytic on ... |r| < 2, |rho'| < pi/2”; `docs/graph/P/DEPGRAPH.md:21036–21037` repeats that carrier. The export `WrapperChain.lean:182` instead proves its chart/lattice conclusions only on `p11WrO D`, defined at lines 29–35 as real points of `complexStrip × actionNbhd (p11PreparedBox n) 1`. The box is `[-1/2,1/2]^(2n)`, so all real actions on this domain satisfy |I_j| < 3/2. It is strictly smaller than the named node carrier: an r-coordinate 7/4, with all other actions zero, lies in the blueprint carrier but outside this one. The Hamiltonian identity is separately proved by `p11_wr_link`, also on the smaller domain. Consequently the literal `wr-chain` node has not been delivered. This is not a failure of the signed wrapper: all used tori have |I| ≤ 1 and lie inside the proved open domain. The handoff acknowledges a consumer-sufficient domain, but that does not satisfy its explicit unsigned-export/literal-node criterion. Either a separately authorized graph/design revision or a proof on the literal carrier is needed for that certification.

**F3 — `wr-tube` intermediate constants not delivered literally.** The same blueprint at line 253, and `docs/graph/P/DEPGRAPH.md:21137`, assert “sum ... ≤ 4 n eps” and “Gamma_i ≤ 2 n eps”. `WrapperTubeMain.lean:92–116` instead proves the usable coarser bound `Gamma_i ≤ 3*n*eps + 2*n*d_fast^2 ≤ p11PhysicalDelta D`, using `p11_tube_sq`'s `6*eps + 4*d_fast^2` and hR2. No local or exported proof of the two named numerical conclusions occurs in the audited modules. The final literal tube inclusion is proved, and its numeric premises are all discharged by `p11_ev_tube`; this is a sound alternate proof of the consumer conclusion, not a proof of every intermediate graph clause. Under AUDIT FOCUS's literal graph-slice criterion this is a delivery gap. It is not a suspected false blueprint estimate: a sharper small-displacement estimate could establish it after decreasing the threshold.

Minor documentation inaccuracies: handoff says every new file is below 300 lines, but WrapperChain has 302; all are far below the 1500-line cap. Provider prose still says “Until the signed wrapper is proved” although the unconditional application is present. Neither affects proofs.

## Node results

| Node | Declaration / proof locator | Verdict | Reason |
|---|---|---|---|
| `bpP:p11:wrapper` | `wrapper_of_data_star`, `wrapper` | PASS | Exact signed output; hDS is exactly signed data_star's conclusion; unconditional application discharges it. |
| `stepP:p11:wr-nu` | Wrapper:80–119; `p11_wr_small`, `p11_ev_thr`, `p11_ev_slowDisp`, `p11_ev_tube` | PASS | Fixed datum and uniform beta-family constants precede nu, eps0 and eps; max formula uses kappa=1/2, a=G0. No circular use of averaging constants. |
| `stepP:p11:wr-kam` | `p11_wr_qi`; Wrapper:120–153; QuantitativeFamily fields | PASS | Actual K1–K6 family, compact good set and measure bound; beta amount and full spec come from hDS. Action displacement ≤1/2 gives actions ≤1. |
| `stepP:p11:wr-chain` | `p11_wr_chain`, `p11_wr_chain_eq`, `p11_wr_link`, `p11_wr_xi` | FAIL (literal node) | F2: chart, full lattice and physical-time identity proved on smaller consumer domain. |
| `stepP:p11:wr-tor` | `p11_wr_torus`; `p11_wr_set` | PASS | Actual transport, local Hamiltonian equality on an open set, phase reindexing and whole-torus witnesses. |
| `stepP:p11:wr-meas` | `p11TorusUnion_eq/props`; `p11_wr_set` | PASS | Countable translated cells, actual lattice Liouville theorem, positivity and measurable image; finiteness from mp_a_box. Parameter cell is not confused with ambient cell. |
| `stepP:p11:wr-tube` | `p11_wr_tube`, eventual numeric bounds | FAIL (literal intermediate clauses) | F3; final tube inclusion and every consumer premise pass. |
| `bpP:p13:n-general`, `ng-const`, `ng-wrap`, `ng-phys` | General:34–89 | PASS | Canonical d,D depend on a alone; eps0 before eps; exact physical assembly. |
| `bpP:p13:fixed`, `fx-split`, `fx-2`, `fx-n` | Main:32–68 | PASS | n=2 actual independent two-planet proof; n>2 general route; frozen witness order. |
| `bpP:p0:fixed` | Provider:54–64 | PASS WITH NOTES | Unconditional exact-type provider; valid binder-applied scratch seal; F1 bare recipe rejected. |

## Definitions and public declarations

All 12 new definitions are transparent intended constructions on their whole carriers. There are no new structures, abbrevs, instances or notation. The real-part maps are total real restrictions, not claims of complex reality off their source domains. Chart properties are asserted only where source specs establish them. Existing selected fast/slow-data fallbacks are not new here; `p11_wr_small` proves their existence guards and unfolds the successful branches. No theorem relies on an off-domain fallback.

| Definition | Classification |
|---|---|
| `p11ReC` | Continuous real-linear coordinatewise real part, whole complex phase space. |
| `p11FastShift` | Literal integer fast-angle shift, zero slow/actions. |
| `p11WrPsiR`, `p11WrFastR` | Real parts of actual selected complex averaging maps, after real inclusion. |
| `p11WrSlowDom`, `p11WrFastDom` | Explicit source strip/box and working domains. |
| `p11WrV`, `p11WrO` | Prepared complex domain and real preimage; F2 compares this intended object to the graph carrier. |
| `p11WrChain` | Literal composition of chart, fast, polar, slow and affine rescaling. |
| `p11WrDatum` | Full KAM datum with rho=2, vartheta=1/4, s=sigma/72, loss=1/2 and amount b. |
| `p11WrXi` | Same chain with exact phase reindexing n*2=n+n. |
| `p11TorusUnion` | Existential union of entire retained parameter tori. |

The following inventory has one row for every new/newly-public declaration (85 total: 73 theorems, 12 definitions). `KP` means `KAM.Planetary`; `PR` means `KAM.Provider.Planetary`. Helper rows are judged against their stated auxiliary purpose, not falsely promoted to independent graph-node closure.

| Node / role | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| p13 / p0 | `KP.FixedAssembly.n_general_of_wrapper` (General.lean:34) | PASS | Distinct conditional helper or unconditional application of signed wrapper. |
| p13 / p0 | `KP.FixedAssembly.n_general` (General.lean:76) | PASS | Distinct conditional helper or unconditional application of signed wrapper. |
| p13 / p0 | `KP.FixedAssembly.fixed_of_wrapper` (Main.lean:32) | PASS | Distinct conditional helper or unconditional application of signed wrapper. |
| p13 / p0 | `KP.FixedAssembly.fixed` (Main.lean:57) | PASS | Distinct conditional helper or unconditional application of signed wrapper. |
| wr-chain | `KP.p11PolarScale_apply` (Polar.lean:118) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wrapper / wr-nu | `KP.p11SlowConstant_nonneg` (Wrapper.lean:36) | PASS | Source positivity or signed wrapper assembly; hDS discharged by data_star. |
| wrapper / wr-nu | `KP.p11_patch_beta_pos` (Wrapper.lean:43) | PASS | Source positivity or signed wrapper assembly; hDS discharged by data_star. |
| wrapper / wr-nu | `KP.wrapper_of_data_star` (Wrapper.lean:48) | PASS | Source positivity or signed wrapper assembly; hDS discharged by data_star. |
| wrapper / wr-nu | `KP.wrapper` (Wrapper.lean:158) | PASS | Source positivity or signed wrapper assembly; hDS discharged by data_star. |
| wr-nu | `KP.p11_ev_pow_log` (WrapperAsym.lean:28) | PASS | Numeric eventual bound; positivity and exponent guards explicit. |
| wr-nu | `KP.p11_ev_lt` (WrapperAsym.lean:32) | PASS | Numeric eventual bound; positivity and exponent guards explicit. |
| wr-nu | `KP.p11_ev_slowDisp` (WrapperAsym.lean:36) | PASS | Numeric eventual bound; positivity and exponent guards explicit. |
| wr-nu | `KP.p11_inv_alpha_le` (WrapperAsym.lean:67) | PASS | Numeric eventual bound; positivity and exponent guards explicit. |
| wr-nu | `KP.p11_ev_tube` (WrapperAsym.lean:96) | PASS | Numeric eventual bound; positivity and exponent guards explicit. |
| wr-nu | `KP.p11_rpow_natpow` (WrapperAsym.lean:172) | PASS | Numeric eventual bound; positivity and exponent guards explicit. |
| wr-nu | `KP.p11_rpow_scale` (WrapperAsym.lean:176) | PASS | Numeric eventual bound; positivity and exponent guards explicit. |
| wr-nu | `KP.p11_ev_thr` (WrapperAsym.lean:182) | PASS | Numeric eventual bound; positivity and exponent guards explicit. |
| wr-chain | `KP.p11WrV` (WrapperChain.lean:29) | PASS | Intended total construction; classification above. |
| wr-chain | `KP.p11WrO` (WrapperChain.lean:34) | PASS | Intended total construction; classification above. |
| wr-chain | `KP.p11WrChain` (WrapperChain.lean:37) | PASS | Intended total construction; classification above. |
| wr-chain | `KP.p11WrV_isOpen` (WrapperChain.lean:41) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11WrO_isOpen` (WrapperChain.lean:50) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11RescaleReal_eq` (WrapperChain.lean:54) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11RescaleReal_chart` (WrapperChain.lean:63) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11RescaleReal_shift` (WrapperChain.lean:79) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11RescaleReal_injective` (WrapperChain.lean:85) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11_wr_dom` (WrapperChain.lean:101) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11WrO_shift` (WrapperChain.lean:158) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11PolarR_angleShift` (WrapperChain.lean:164) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11_wr_chain` (WrapperChain.lean:182) | FAIL (literal node) | F2; proved statement itself is sound and sufficient for consumers. |
| wr-chain | `KP.p11_wr_chain_eq` (WrapperChain.lean:282) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-kam | `KP.p11WrDatum` (WrapperDatum.lean:31) | PASS | Intended total construction; classification above. |
| wr-kam | `KP.p11WrDatum_valid` (WrapperDatum.lean:44) | PASS | Literal datum, validity, periodicity or frequency/admissibility bridge. |
| wr-kam | `KP.p11_single_mem` (WrapperDatum.lean:87) | PASS | Literal datum, validity, periodicity or frequency/admissibility bridge. |
| wr-kam | `KP.p11_periodic_int` (WrapperDatum.lean:93) | PASS | Literal datum, validity, periodicity or frequency/admissibility bridge. |
| wr-chain | `KP.p11_phaseCast_cancel` (WrapperEps.lean:32) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11_wr_link` (WrapperEps.lean:36) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11WrXi` (WrapperEps.lean:50) | PASS | Intended total construction; classification above. |
| wr-chain | `KP.p11_wr_xi` (WrapperEps.lean:53) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11WrO_realDomain` (WrapperEps.lean:80) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11_wr_torus` (WrapperEps.lean:91) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11_wr_set` (WrapperEps.lean:122) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-meas | `KP.p11TorusUnion` (WrapperMeasure.lean:29) | PASS | Intended total construction; classification above. |
| wr-meas | `KP.p11TorusUnion_eq` (WrapperMeasure.lean:32) | PASS | Whole torus saturation and countable lattice translates. |
| wr-meas | `KP.p11TorusUnion_props` (WrapperMeasure.lean:50) | PASS | Whole torus saturation and countable lattice translates. |
| wr-chain | `KP.p11_eq_realInclusion₂_re` (WrapperParts.lean:33) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11_realInclusion₂_add_angleShift` (WrapperParts.lean:38) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11ReC_add_shift` (WrapperParts.lean:44) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11FastShift` (WrapperParts.lean:50) | PASS | Intended total construction; classification above. |
| wr-chain | `KP.p11_realInclusion₂_add_fastShift` (WrapperParts.lean:52) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11ReC_add_fastShift` (WrapperParts.lean:59) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11WrPsiR` (WrapperParts.lean:66) | PASS | Intended total construction; classification above. |
| wr-chain | `KP.p11WrFastR` (WrapperParts.lean:70) | PASS | Intended total construction; classification above. |
| wr-chain | `KP.p11WrSlowDom` (WrapperParts.lean:74) | PASS | Intended total construction; classification above. |
| wr-chain | `KP.p11WrFastDom` (WrapperParts.lean:80) | PASS | Intended total construction; classification above. |
| wr-chain | `KP.p11WrSlowDom_isOpen` (WrapperParts.lean:84) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11WrPsiR_facts` (WrapperParts.lean:88) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11WrFastDom_isOpen` (WrapperParts.lean:123) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11WrFastDom_shift` (WrapperParts.lean:126) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11WrFastR_facts` (WrapperParts.lean:137) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-kam | `KP.p11_actionNbhd_mono` (WrapperQI.lean:29) | PASS | Literal datum, validity, periodicity or frequency/admissibility bridge. |
| wr-kam | `KP.p11_freq_eq` (WrapperQI.lean:35) | PASS | Literal datum, validity, periodicity or frequency/admissibility bridge. |
| wr-kam | `KP.p11_wr_qi` (WrapperQI.lean:48) | PASS | Literal datum, validity, periodicity or frequency/admissibility bridge. |
| wr-chain | `KP.p11ReC` (WrapperReal.lean:31) | PASS | Intended total construction; classification above. |
| wr-chain | `KP.p11ReC_realInclusion₂` (WrapperReal.lean:35) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11_symplFormC_ofReal` (WrapperReal.lean:37) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-chain | `KP.p11_realChart` (WrapperReal.lean:43) | PASS | Real restriction, domain, chart, or lattice helper; source premises explicit. |
| wr-nu | `KP.p11_wr_small` (WrapperSmall.lean:28) | PASS | Numeric eventual bound; positivity and exponent guards explicit. |
| wr-tor | `KP.p11_isPhysicalTorus_cast` (WrapperTransport.lean:28) | PASS | Equality/reindexing transport; no assumed physical-torus output. |
| wr-tor | `KP.p11_latticeTorus_congr` (WrapperTransport.lean:43) | PASS | Equality/reindexing transport; no assumed physical-torus output. |
| wr-tube | `KP.p11PolarR_cast` (WrapperTube.lean:25) | PASS | Explicit algebraic/displacement helper; numeric guards discharged in wrapper. |
| wr-tube | `KP.p11PolarR_sq` (WrapperTube.lean:30) | PASS | Explicit algebraic/displacement helper; numeric guards discharged in wrapper. |
| wr-tube | `KP.p11_orth_sq` (WrapperTube.lean:43) | PASS | Explicit algebraic/displacement helper; numeric guards discharged in wrapper. |
| wr-tube | `KP.p11_chartInput_gamma` (WrapperTube.lean:67) | PASS | Explicit algebraic/displacement helper; numeric guards discharged in wrapper. |
| wr-tube | `KP.p11_patch_near` (WrapperTube.lean:108) | PASS | Explicit algebraic/displacement helper; numeric guards discharged in wrapper. |
| wr-tube | `KP.p11_abs_le_of_pi_norm` (WrapperTube.lean:114) | PASS | Explicit algebraic/displacement helper; numeric guards discharged in wrapper. |
| wr-tube | `KP.p11_wr_psi_disp` (WrapperTube.lean:120) | PASS | Explicit algebraic/displacement helper; numeric guards discharged in wrapper. |
| wr-tube | `KP.p11_wr_fast_disp` (WrapperTube.lean:139) | PASS | Explicit algebraic/displacement helper; numeric guards discharged in wrapper. |
| wr-tube | `KP.p11_sq_aux` (WrapperTubeMain.lean:25) | PASS | Explicit algebraic/displacement helper; numeric guards discharged in wrapper. |
| wr-tube | `KP.p11_tube_sq` (WrapperTubeMain.lean:30) | PASS | Explicit algebraic/displacement helper; numeric guards discharged in wrapper. |
| wr-tube | `KP.p11_tube_lambda` (WrapperTubeMain.lean:38) | PASS | Explicit algebraic/displacement helper; numeric guards discharged in wrapper. |
| wr-tube | `KP.p11_delta_nonneg` (WrapperTubeMain.lean:59) | PASS | Explicit algebraic/displacement helper; numeric guards discharged in wrapper. |
| wr-tube | `KP.p11_wr_tube` (WrapperTubeMain.lean:64) | FAIL (literal intermediate clauses) | F3; final tube inclusion itself passes. |
| p13 / p0 | `PR.fixedSunPlanetaryKAM_of_wrapper` (FixedSunPlanetaryKAM.lean:33) | PASS | Distinct conditional helper or unconditional application of signed wrapper. |
| p13 / p0 | `PR.fixedSunPlanetaryKAM` (FixedSunPlanetaryKAM.lean:54) | PASS | Distinct conditional helper or unconditional application of signed wrapper. |

## Validation and axiom evidence

Targeted build (exit 0):

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap10 KAM.Provider.Planetary.FixedSunPlanetaryKAM KAM.Planetary.Preparation.Wrapper KAM.Planetary.Preparation.Datum
[inp-gate] slot 1 acquired 04:27:26 for KAM.Provider.Planetary.FixedSunPlanetaryKAM KAM.Planetary.Preparation.Wrapper KAM.Planetary.Preparation.Datum
Build completed successfully (9881 jobs).
```

Inherited dependency warnings were replayed; no build failure. Probes use default resource limits. The exact probe imported the frozen module only to inspect its type, not to prove anything:

```lean
example : type_of% @KAM.Planetary.fixedSunPlanetaryKAM :=
  @KAM.Provider.Planetary.fixedSunPlanetaryKAM
example : type_of% @KAM.Planetary.wrapper :=
  fun D => KAM.Planetary.wrapper_of_data_star D (KAM.Planetary.data_star D)
```

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11Exact.lean
exit 0
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11Seal.lean
exit 1 (F1 bare-body type mismatch)
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11SealApplied.lean
exit 0
'KAM.Planetary.auditP11ScratchSeal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Both scratch seals retain the frozen telescope/conclusion and rename only the declaration to avoid collisions. The second changes the failed bare body to the explicit-binder body. Complete `#print axioms` output for all 73 theorem declarations:

```text
'KAM.Planetary.FixedAssembly.n_general_of_wrapper' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.FixedAssembly.n_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.FixedAssembly.fixed_of_wrapper' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.FixedAssembly.fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarScale_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11SlowConstant_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_patch_beta_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wrapper_of_data_star' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.wrapper' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_ev_pow_log' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_ev_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_ev_slowDisp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_inv_alpha_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_ev_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_rpow_natpow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_rpow_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_ev_thr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WrV_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WrO_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11RescaleReal_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11RescaleReal_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11RescaleReal_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11RescaleReal_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_dom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WrO_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarR_angleShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_chain_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WrDatum_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_single_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_periodic_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_phaseCast_cancel' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_link' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_xi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WrO_realDomain' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_torus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_set' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11TorusUnion_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11TorusUnion_props' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_eq_realInclusion₂_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_realInclusion₂_add_angleShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11ReC_add_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_realInclusion₂_add_fastShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11ReC_add_fastShift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WrSlowDom_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WrPsiR_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WrFastDom_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WrFastDom_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11WrFastR_facts' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_actionNbhd_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_freq_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_qi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11ReC_realInclusion₂' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_symplFormC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_realChart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_isPhysicalTorus_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_latticeTorus_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarR_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11PolarR_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_orth_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_chartInput_gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_patch_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_abs_le_of_pi_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_psi_disp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_fast_disp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_sq_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_tube_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_tube_lambda' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_delta_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_wr_tube' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.fixedSunPlanetaryKAM_of_wrapper' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.fixedSunPlanetaryKAM' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Whitespace-normalized source comparison independently returned True for signed wrapper, n_general, fixed, provider, and hDS versus the signed data_star conclusion. Their binder/quantifier order, constants, carriers and conclusion are preserved; the four unconditional bodies are exactly the applications described in the handoff.

Kernel replay: one invocation containing every changed Lean module, exit 0.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.FixedAssembly.General KAM.Planetary.FixedAssembly.Main KAM.Planetary.Preparation.Polar KAM.Planetary.Preparation.Wrapper KAM.Planetary.Preparation.WrapperAsym KAM.Planetary.Preparation.WrapperChain KAM.Planetary.Preparation.WrapperDatum KAM.Planetary.Preparation.WrapperEps KAM.Planetary.Preparation.WrapperMeasure KAM.Planetary.Preparation.WrapperParts KAM.Planetary.Preparation.WrapperQI KAM.Planetary.Preparation.WrapperReal KAM.Planetary.Preparation.WrapperSmall KAM.Planetary.Preparation.WrapperTransport KAM.Planetary.Preparation.WrapperTube KAM.Planetary.Preparation.WrapperTubeMain KAM.Provider.Planetary.FixedSunPlanetaryKAM
replaying KAM.Provider.Planetary.FixedSunPlanetaryKAM
replaying KAM.Planetary.Preparation.WrapperTubeMain
replaying KAM.Planetary.Preparation.WrapperTube
replaying KAM.Planetary.Preparation.WrapperTransport
replaying KAM.Planetary.Preparation.WrapperSmall
replaying KAM.Planetary.Preparation.WrapperReal
replaying KAM.Planetary.Preparation.WrapperQI
replaying KAM.Planetary.Preparation.WrapperParts
replaying KAM.Planetary.Preparation.WrapperMeasure
replaying KAM.Planetary.Preparation.WrapperEps
replaying KAM.Planetary.Preparation.WrapperDatum
replaying KAM.Planetary.Preparation.WrapperChain
replaying KAM.Planetary.Preparation.WrapperAsym
replaying KAM.Planetary.Preparation.Wrapper
replaying KAM.Planetary.Preparation.Polar
replaying KAM.Planetary.FixedAssembly.Main
replaying KAM.Planetary.FixedAssembly.General
```

Final serialized lint:

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1262 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only lint failure is the stale generated root, explicitly allowed by the brief. Module, frozen-anchor and elaborated ABI checks pass. The root was not regenerated.

Static checks: `git diff --check inp...HEAD` exits 0, no output. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. Changed Lean files range from 63 to 302 lines, except General/Main/provider (93/72/68); no line exceeds 100 Unicode characters. Module headers, copyright, public imports, docstrings, exposed public sections are present. No forbidden token, EuclideanSpace, resource override, reused public helper short name, or harmful root shadow found in the changed code.

Provider quarantine: reverse import search finds exactly `KAM/Frozen/Planetary/Theorems/FixedSunPlanetaryKAM.lean:24`. The provider directly imports Mathlib, the frozen FixedKolmogorovSet definition and FixedAssembly.Main. Recursive project-import traversal reaches exactly one other frozen theorem, ProperlyDegenerateKAM, manifest `SEALED`; its own provider is reached through that sealed anchor. There is no direct cross-provider import and no transitive DRAFT_SORRY theorem in the production proof chain. The real audited anchor remains DRAFT_SORRY.

Audit execution deviation: the initial `sh scripts/lint_sources.sh` was launched alongside the exact probe without the requested environment prefix. Inspection showed lint itself launches an ABI Lean process, so the initial validation scheduling did not guarantee the one-process constraint. No process was killed and no result was silently treated as serialized. The final lint invocation was rerun alone with `LEAN_NUM_THREADS=1 nice -n 5` after kernel replay exited; the exact/body probes and kernel replay otherwise ran one at a time. This is an auditor workflow deviation, not a source-code change.

## Limits and handoff

No suspected pinned mathematical-source erratum is established by this audit. F1 is an exact reproducible seal-instruction defect; F2/F3 are Lean-versus-blueprint/graph delivery discrepancies, not silently repaired statements. No broader audit of all upstream proofs or historical source gaps is claimed. Conditional helpers have distinct names, and their premises are actually discharged in the four unconditional applications. The signed anchor has no remaining conclusion-shaped assumption, but literal graph certification requires resolving F2/F3. No source or frozen change was made by the auditor.

Final validation: all three audit-owned Lean probe files deleted; `git diff --check inp...HEAD` and report whitespace validation pass. Repository status contains only the pre-existing untracked handoff and the new requested report; tracked diff remains empty.
