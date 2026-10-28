# Independent delta design audit 2: P45

Overall verdict: **FAIL**.

Revision audited: `145a2ce0af84347d8f675bf7b65169b9301991d9` (`design(P): resolve P45 audit findings in revision 2`), compared directly with its parent `f8f8fb17c5f24392d90afdc34b521f27006c16bd` and with branch inp. Earlier F1–F6 are resolved at the signature-contract level; N2 is resolved. N1 is only partially resolved: the new concrete P2 application uses a false uniform-divisor claim (F7). A new package ownership dependency also introduces a cycle (F8). The P3 adapter types and numerical dictionary otherwise match the delivered interface.

This is a design audit, not proof closure. The submitted revision elaborates with 69 sorry warnings, including both typed upstream applications. That does not establish the new helper hypotheses supplied to those applications.

## Scope and earlier findings

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the exact audit brief, both audit/design documents, the Revision 2 section and handoff, and the shared 1,282-line signatures. Compared changed declarations with P Parts 4–5 and authoritative inp packets `P-p4.nodes.md`/`P-p5.nodes.md`. Checked new fixture declarations against current P23Signatures, and the frozen/period/chart interfaces used by the adapters. Local P4/P5 blueprint files remain byte-identical to current inp copies. No subagents were used.

`S:L` means `/root/code/KAM-inp/.drafts/design/P45Signatures.lean:L`; `D:L` means `docs/tracks/P/design/P45-LEAN-DESIGN.md:L`; P5 locators refer to `blueprint-P/parts/p5-pg-assembly.tex`.

| Prior finding | Delta verdict | Evidence and consumer effect |
|---|---|---|
| F1 — collar | PASS, resolved | S:307–329 scopes compactness and exact difference to every t>0; measure bounds retain t<d; lower measure and neighbourhood inclusion are present. Consumers may project the appropriate clause without adding a source radius restriction to compactness. |
| F2 — coefficient continuity/symmetry | PASS, resolved | S:632–648 exports joint continuity of constructed coefficients and complex beta symmetry. Together with birkhoff_ext it supplies the exact P5:49–61 contract. This remains proved output, not a provider premise. |
| F3 — radius-2 polynomial bounds | PASS, resolved | S:696–700 defines analyticBoundDomain with slow radius 2; PGAnalyticSpec uses it for N/DN/D²N. Radius-1 analyticDomain remains the inverse domain. |
| F4 — muStar bound | PASS, resolved | S:711 now includes muStar≤mu0. The unchanged freq_inj range is contained in the interval of every supporting bound. The design records the original blueprint omission explicitly. |
| F5 — numerical constants | PASS, resolved | S:670–679 exposes dioConstant and its estimate; S:1195–1220 gives both measure upper constants, the explicit pgBudget sum and the bound with that same constant. The strictly positive enclosing Ry enlargement is now declared at D:619–623. All constants remain data-only. |
| F6 — polar null coverage | PASS, resolved | S:512–520 contains both cell volume and null complement of the positive-action polar image. Other chart/image/shell statements retain their carriers and factors. |
| N1 — upstream adapters | FAIL, partially resolved | Exact fixtures and actual theorem applications are now supplied. P3 checks are consistent. The P2 hypothesis adapter S:1021–1025 supplies an invalid divisor bound; see F7. |
| N2 — ownership/diameter helper | PASS, resolved | ext_conn is assigned before collar, beta_inverse before slow resonance work, and S:839–842 exports the short-section measure helper. Abstract CutMeasure is early; the actual family measure is downstream in Strictness. A different new placement defect is F8. |

## New findings

### F7 — Major: P2 adapter asserts an excessive divisor bound on the entire neighbourhood

**Locations:** S:41–43 (`KAM.NormalForm.DivisorBound`), S:102–117 (`OscHyp.divisor`), S:1021–1025 (`pg_osc_hyp`); D:338–360. Source: P5:176–178, especially `stepP:p5:av-R1` and its graph packet record.

The delivered OscHyp requires a constant lower bound α for every nonzero lattice mode of size at most K throughout the complex action neighbourhood. The new adapter sets

```text
alpha = gammaBar / (2*pi).
```

The frozen Diophantine hypothesis instead bounds the divisor at a core point by gammaBar/|k|^tau. Extension to the rhoBar-neighbourhood loses a further factor 2. Since pgOscH=H0/(2*pi), the source supplies exactly

```text
alpha = gammaBar / (4*pi*Kbar^tau).
```

The revision lost both the cutoff power and the neighbourhood factor. This is a false helper target, not just a missing proof or an unverified library name. The #check application accepts it only because the false target is currently supplied by sorry.

**Concrete refutation already in one fast dimension.** Take a=b=1, V=(-1,1), W=(-2,2), H0(I)=I²/2, and an angle-independent quartic oscillator perturbation P=R²/2, with P0=Omega=0 and beta=1. These satisfy the frozen source premises with ordinary positive radii and collar/torsion constants. For sufficiently small admissible r choose mu=r^10. Then gamma=gammaBar tends to zero, so I0=gamma lies in the inner core and satisfies IsDiophantine gamma 3 (fastFrequency H0 I0): for any nonzero integer k, gamma/|k|³≤|k|gamma. Write rho=rhoBar>0 and choose the real point I'=gamma-rho/2 in the complex rho-neighbourhood of that core point. The formulas give rho<gamma for small r. For k=1 (Kbar>1), the proposed constant bound requires

```text
gamma/(2*pi) ≤ |I'|/(2*pi) = (gamma-rho/2)/(2*pi),
```

a contradiction. Analytic agreement forces the selected H0 extension and its derivative to equal the quadratic on these real interior points; arbitrary off-domain values cannot fix this.

**Complete replacement signature:**

```lean
def pgOscAlpha (d : PGData a b) (r mu : ℝ) : ℝ :=
  (params d r mu).gammaBar /
    (4*Real.pi*(params d r mu).Kbar^(pgTau a b))

theorem pg_osc_hyp (d : PGData a b) (r mu : ℝ)
    (h : admissible d (pgRstar d) r mu) :
    OscHyp (checkedCore d r mu) (params d r mu).rhoBar
      (pgOscEpsilon d) (pgOscEpsilon d)
      0 (pgOscWidth d)
      (15/(Real.pi*pgOscWidth d)*Real.log (1/r))
      (pgOscAlpha d r mu) (pgOscE d mu)
      (pgOscH d) (pgOscE d mu • pgOscP d mu) := by sorry
```

The actual averaged_remainder application can keep its existing form: α is inferred from the corrected record. Do not repair this by requesting a stronger source Diophantine condition or adding a divisor hypothesis to frozen P-G.

**Dependent prose/estimate corrections:** let c=2*pi, e=pgOscRadius, w=pgWidth, L=LP, K=Kbar, gamma=gammaBar and rho=rhoBar. Keep the conformally symplectic normalization T; it is sound. After conjugation back, the quadratic remainder bound must be

```text
800*(1+b)*L^2*mu^2*K^tau / (gamma*min(rho*w,e^2)).
```

The physical fast-action displacement is at most `6*L*mu*K^tau/(gamma*w)`; each oscillator block is at most `18*L*mu*K^tau/(gamma*e)`. Thus the already exported constants 12 and 18 in AveragingSpec remain adequate. Replace D:348–360 accordingly; the present stronger estimates follow from the erroneous α.

The existing G conditions have room for this repair without changing frozen quantifiers. With `rho*w≤e²`, substitute rho=gamma/(2*M0*K^(tau+1)): the quadratic term becomes

```text
1600*(1+b)*M0*L^2*mu^2*K^(2*tau+1)/(gamma^2*w)
  ≤ L*mu*r^5
```

by the first gamma branch and G²≥1600*(1+b)*M0/w. OscHyp.small reduces to G²≥2^14*(1+b)*M0*K*r^5, supplied by the existing G bound and K*r^5≤1. These calculations identify the intended proof obligations; they are not Lean proof receipts. pg_osc_bound, positivity, zero-mode identity, normalization and domain equality do not require signature changes.

### F8 — Medium: new KAM dictionary points back into the later Family package

**Locations:** D:488–489 (package output ownership); S:1117–1120 (`pgD0`), S:1130–1134 (`pg_kam_dictionary`).

P5-KH/KAMInputs now owns pg_kam_dictionary, whose type mentions pgD0. The package table still assigns pgD0 to P5-FAM/Family. Family imports KAMInputs for the KAM estimates and application. Consequently the printed ownership requires KAMInputs→Family→KAMInputs, contradicting the claimed dependency order. The single signature file elaborates because pgD0 happens to be placed before the dictionary; that does not validate the proposed module split.

Move pgD0 to P5-PAR/Parameters (or an equally early module) and remove it from Family's outputs. It depends only on parameters, the real frequency formula and the P1 two-scale predicate. Parameters already has both real action domains; add the P1 predicate import there. Preserve the exact declaration:

```lean
-- Owner: KAM/Planetary/PGAssembly/Parameters.lean
-- Defined after pgActionDomain; before the KAMInputs consumer.
def pgD0 (d : PGData a b) (r mu : ℝ) : Set (Fin (a+b) → ℝ) :=
  {J ∈ pgActionDomain d r mu |
    ((2*Real.pi)⁻¹ • freq d.H0 d.P0 d.Omega d.beta mu J) ∈
      twoScaleDiophantine a b (params d r mu).gamma1
        (params d r mu).gamma2 (pgTau a b)}
```

The pg_kam_dictionary statement itself needs no mathematical change. Fix the package table and DAG before splitting the implementation; no frozen edit is involved.

## Every declaration and application

The table inventories all 201 explicit declarations, including copied upstream fixtures and unchanged signatures, so the delta has no omitted declaration. `KAM.NormalForm` entries are qualified to distinguish its derivative frequency from `KAM.Planetary.freq`. PASS is a statement/definition verdict, not a theorem-proof or dependency-closure verdict. F8 concerns module placement; types referencing pgD0 remain mathematically correct. Prior source-contract repairs are marked explicitly. The two #check applications are assessed after the table.

| Lean name (S line) | Blueprint role | Verdict | Reason |
|---|---|---|---|
| `KAM.NormalForm.zBall` (38) | `bpP:p2:osc-averaging / exact divisor fixture` | PASS | Exact delivered NormalForm fixture; no carrier change. |
| `KAM.NormalForm.freq` (39) | `bpP:p2:osc-averaging / exact divisor fixture` | PASS | Exact delivered NormalForm fixture; no carrier change. |
| `KAM.NormalForm.dotC` (40) | `bpP:p2:osc-averaging / exact divisor fixture` | PASS | Exact delivered NormalForm fixture; no carrier change. |
| `KAM.NormalForm.DivisorBound` (41) | `bpP:p2:osc-averaging / exact divisor fixture` | PASS | Exact delivered NormalForm fixture; no carrier change. |
| `twoScaleDiophantine` (50) | `bpP:p1:two-scale` | PASS | Source formula/carrier; no changed norm or global instance. |
| `IsLatticeTorus` (59) | `bpP:p1:lattice-torus` | PASS | Exact delivered P23 fixture. |
| `CPhase` (68) | `bpP:p2:conv / carrier fixture` | PASS | Exact delivered P23 fixture. |
| `CHam` (69) | `bpP:p2:conv / carrier fixture` | PASS | Exact delivered P23 fixture. |
| `geometricWidth` (70) | `bpP:p3:period-dictionary` | PASS | Exact delivered P23 fixture. |
| `realBase` (71) | `bpP:p3:conv` | PASS | Exact delivered P23 fixture. |
| `coefficientDom` (72) | `bpP:p3:conv` | PASS | Exact delivered P23 fixture. |
| `realTube` (74) | `bpP:p3:conv` | PASS | Exact delivered P23 fixture. |
| `firstBlock` (76) | `bpP:p2:conv / coordinate fixture` | PASS | Exact delivered P23 fixture. |
| `lastBlock` (78) | `bpP:p2:conv / coordinate fixture` | PASS | Exact delivered P23 fixture. |
| `oscPack` (80) | `bpP:p2:osc-averaging / packing` | PASS | Exact delivered P23 fixture. |
| `oscUnpack` (83) | `bpP:p2:osc-averaging / unpacking` | PASS | Exact delivered P23 fixture. |
| `oscFunction` (86) | `bpP:p2:osc-averaging / Fourier carrier` | PASS | Exact delivered P23 fixture. |
| `oscParams` (87) | `bpP:p2:osc-averaging / parameter domain` | PASS | Exact delivered P23 fixture. |
| `oscDom` (91) | `bpP:p2:osc-averaging / domain` | PASS | Exact delivered P23 fixture. |
| `oscBound` (93) | `bpP:p2:osc-averaging / norm` | PASS | Exact delivered P23 fixture. |
| `oscClass` (96) | `bpP:p2:osc-averaging / analyticity` | PASS | Exact delivered P23 fixture. |
| `OscHyp` (100) | `bpP:p2:osc-averaging` | PASS | Exact delivered P23 fixture. |
| `averaged_remainder` (115) | `bpP:p2:averaged-remainder` | PASS | Exact delivered P23 fixture. |
| `ScaleData` (144) | `bpP:p3:constants` | PASS | Exact delivered P23 fixture. |
| `constants` (157) | `bpP:p3:constants` | PASS | Exact delivered P23 fixture. |
| `cutoff` (163) | `bpP:p3:constants` | PASS | Exact delivered P23 fixture. |
| `rhoHat` (164) | `bpP:p3:constants` | PASS | Exact delivered P23 fixture. |
| `eHat` (165) | `bpP:p3:constants` | PASS | Exact delivered P23 fixture. |
| `kamConstant` (166) | `bpP:p3:constants` | PASS | Exact delivered P23 fixture. |
| `complementConstant` (167) | `bpP:p3:two-scale-kam` | PASS | Exact delivered P23 fixture. |
| `initialL` (168) | `bpP:p3:constants` | PASS | Exact delivered P23 fixture. |
| `realFreq` (169) | `bpP:p3:conv` | PASS | Exact delivered P23 fixture. |
| `dioBase` (171) | `bpP:p3:two-scale-kam` | PASS | Exact delivered P23 fixture. |
| `omegaSet` (174) | `bpP:p3:two-scale-kam` | PASS | Exact delivered P23 fixture. |
| `KamHyp` (177) | `bpP:p3:interface` | PASS | Exact delivered P23 fixture. |
| `limitmap_data` (203) | `bpP:p3:limit-phi` | PASS | Exact delivered P23 fixture. |
| `two_scale_kam` (204) | `bpP:p3:two-scale-kam` | PASS | Exact delivered P23 fixture. |
| `blockFast` (250) | `bpP:p4:conv#data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `blockSlow` (251) | `bpP:p4:conv#data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `blockFast_real` (252) | `bpP:p4:conv#data` | PASS | Matches source role; no additional defect found. |
| `blockSlow_real` (253) | `bpP:p4:conv#data` | PASS | Matches source role; no additional defect found. |
| `PGData` (256) | `bpP:p5:order` | PASS | Literal frozen premises; connected includes nonempty. |
| `pgBoundaryA` (288) | `bpP:p5:order` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgBoundaryD` (290) | `bpP:p5:order` | PASS | Source formula/carrier; no changed norm or global instance. |
| `realNbhd` (293) | `bpP:p4:conv#data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `innerCore` (296) | `bpP:p4:conv#data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `actionShell` (299) | `bpP:p4:conv#shell` | PASS | Source formula/carrier; no changed norm or global instance. |
| `joinedActions` (301) | `bpP:p4:conv#data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `unitCube` (304) | `bpP:p1:torus-union` | PASS | Source formula/carrier; no changed norm or global instance. |
| `collar` (307) | `bpP:p4:collar` | PASS | F1 resolved: scoped compactness, differences and measures. |
| `ext_deriv` (328) | `bpP:p4:ext-deriv` | PASS | Derivative analyticity; partial-C1 Lipschitz work is separately packaged. |
| `ext_conn` (332) | `bpP:p4:ext-conn` | PASS | Matches source role; no additional defect found. |
| `realNbhd_joinedActions` (335) | `bpP:p4:domain-collar / helper` | PASS | Exact max-norm product, including empty factors. |
| `lip_compact_c1` (339) | `bpP:p4:lip-compact / conditional helper` | PASS | Distinct conditional helper; does not replace partial-C1 result. |
| `lip_compact` (346) | `bpP:p4:lip-compact` | PASS | Matches source role; no additional defect found. |
| `lip_inverse` (354) | `bpP:p4:lip-inverse` | PASS | Matches source role; no additional defect found. |
| `pgInverse` (365) | `bpP:p4:lip-inverse` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgInverseL` (368) | `bpP:p4:lip-inverse` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgInverseR` (371) | `bpP:p4:lip-inverse` | PASS | Source formula/carrier; no changed norm or global instance. |
| `beta_inverse` (374) | `bpP:p4:beta-inverse` | PASS | Dropping symmetry is a true stronger adjugate estimate. |
| `secularPolynomial` (379) | `bpP:p4:freq` | PASS | Source formula/carrier; no changed norm or global instance. |
| `slowFrequency` (385) | `bpP:p4:freq` | PASS | Source formula/carrier; no changed norm or global instance. |
| `freq` (390) | `bpP:p4:freq` | PASS | Source formula/carrier; no changed norm or global instance. |
| `MeasureData` (399) | `bpP:p4:data` | PASS | Unchanged faithful type; supplying P2 route has F7. |
| `affine_slab` (447) | `bpP:p4:affine-slab` | PASS | Matches source role; no additional defect found. |
| `latticeWeight` (452) | `bpP:p4:lattice-tail` | PASS | Source formula/carrier; no changed norm or global instance. |
| `lattice_tail` (454) | `bpP:p4:lattice-tail` | PASS | Matches source role; no additional defect found. |
| `resonanceBad` (463) | `bpP:p4:two-scale-diophantine-measure` | PASS | Source formula/carrier; no changed norm or global instance. |
| `latticeS` (469) | `bpP:p4:lattice-tail` | PASS | Source formula/carrier; no changed norm or global instance. |
| `measure_c1` (471) | `bpP:p4:two-scale-diophantine-measure` | PASS | Source formula/carrier; no changed norm or global instance. |
| `measure_c2` (476) | `bpP:p4:two-scale-diophantine-measure` | PASS | Source formula/carrier; no changed norm or global instance. |
| `two_scale_diophantine_measure` (478) | `bpP:p4:two-scale-diophantine-measure` | PASS | Matches source role; no additional defect found. |
| `domain_collar_helper` (488) | `bpP:p4:domain-collar / helper` | PASS | Matches source role; no additional defect found. |
| `oscillatorPolar` (496) | `bpP:p4:s-disc#chart` | PASS | General a,b formula agrees with P7 at a=b. |
| `polarMap` (502) | `bpP:p4:disc-measure / P7 specialization` | PASS | Owner snapshot; specialization bridge explicit. |
| `oscillatorPolar_eq_polarMap` (506) | `bpP:p4:disc-measure / P7 specialization` | PASS | Matches source role; no additional defect found. |
| `polarCellMap` (509) | `bpP:p4:s-disc#chart` | PASS | Source formula/carrier; no changed norm or global instance. |
| `disc_measure` (512) | `bpP:p4:disc-measure` | PASS | F6 resolved: numeric volume and null-image coverage. |
| `disc_measure_image` (521) | `bpP:p4:disc-measure` | PASS | Positive-action cell injectivity; exact (2*pi)^n factor. |
| `disc_measure_shell` (527) | `bpP:p4:disc-measure` | PASS | Matches source role; no additional defect found. |
| `PGComplexPhase` (533) | `bpP:p5:ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `assembleComplex` (535) | `bpP:p5:ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `extensionDomain` (538) | `bpP:p5:ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGExtension` (543) | `bpP:p5:ext` | PASS | Produced witness, no extra provider assumption. |
| `ext` (568) | `bpP:p5:ext` | PASS | Matches source role; no additional defect found. |
| `pgExtension` (570) | `bpP:p5:ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgWidth` (572) | `bpP:p5:consts` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgOscRadius` (574) | `bpP:p5:consts` | PASS | Source formula/carrier; no changed norm or global instance. |
| `complexAverage` (576) | `bpP:p5:consts` | PASS | Source formula/carrier; no changed norm or global instance. |
| `complexAverage_real` (582) | `bpP:p5:birkhoff-ext` | PASS | Uses actual frozen normalized secularAverage. |
| `jetP0` (588) | `bpP:p5:birkhoff-ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `jetOmega` (590) | `bpP:p5:birkhoff-ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `jetBeta` (593) | `bpP:p5:birkhoff-ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `jetPolynomial` (598) | `bpP:p5:birkhoff-ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgRemainder` (602) | `bpP:p5:birkhoff-ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `consts` (606) | `bpP:p5:consts` | PASS | Matches source role; no additional defect found. |
| `birkhoff_ext` (616) | `bpP:p5:birkhoff-ext` | PASS | Unchanged outputs; F2 completed by regularity companion. |
| `birkhoff_ext_parameter_regularity` (632) | `bpP:p5:birkhoff-ext` | PASS | F2 resolved: joint continuity and complex symmetry. |
| `uniform_remainder` (649) | `bpP:p5:uniform-remainder` | PASS | Matches source role; no additional defect found. |
| `lip_complex` (654) | `bpP:p5:lip-complex` | PASS | Matches source role; no additional defect found. |
| `complexFast` (661) | `bpP:p5:bilip` | PASS | Source formula/carrier; no changed norm or global instance. |
| `bilip` (664) | `bpP:p5:bilip` | PASS | Matches source role; no additional defect found. |
| `dioConstant` (670) | `bpP:p5:dio-one` | PASS | F5 resolved: explicit chosen-inverse formula. |
| `dio_one` (673) | `bpP:p5:dio-one` | PASS | F5 resolved: explicit constant estimate. |
| `PGAnalytic` (680) | `bpP:p5:freq-data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `analyticDomain` (693) | `bpP:p5:freq-inj` | PASS | Radius-1 inverse domain unchanged; separate radius-2 bound domain now supplied. |
| `analyticBoundDomain` (696) | `bpP:p5:freq-data` | PASS | F3 resolved: radius-2 bound domain only. |
| `complexIntegrable` (702) | `bpP:p5:freq-inj` | PASS | Source formula/carrier; no changed norm or global instance. |
| `complexFrequency` (705) | `bpP:p5:freq-inj` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGAnalyticSpec` (709) | `bpP:p5:freq-data` | PASS | F3/F4 resolved: radius-2 bounds; muStar≤mu0. |
| `freq_data` (739) | `bpP:p5:freq-data` | PASS | Produces corrected output specification; no new assumption. |
| `pgAnalytic` (741) | `bpP:p5:freq-data` | PASS | Choice from output witness, not an added hypothesis. |
| `pgCU` (743) | `bpP:p5:freq-inj` | PASS | Source formula/carrier; no changed norm or global instance. |
| `complexFrequency_real` (746) | `bpP:p5:freq-inj` | PASS | Identifies derivatives only on V; no boundary claim. |
| `freq_inj` (751) | `bpP:p5:freq-inj` | PASS | F4 resolved: source interval now covers the entire claim. |
| `IsChart` (763) | `bpP:p1:chart` | PASS | Owner snapshot, same analytic and frozen symplectic predicates. |
| `fullShift` (766) | `bpP:p1:period-convert` | PASS | Source formula/carrier; no changed norm or global instance. |
| `angleScale` (768) | `bpP:p1:period-convert` | PASS | Source formula/carrier; no changed norm or global instance. |
| `disc_measure_chart` (770) | `bpP:p4:disc-measure` | PASS | Analytic/symplectic polar chart, determinant and lattice injectivity. |
| `resonanceBad_eq` (781) | `bpP:p4:two-scale-diophantine-measure` | PASS | Matches source role; no additional defect found. |
| `local_real_complexification` (785) | `bpP:p5:ext-loc / helper` | PASS | Matches source role; no additional defect found. |
| `compact_real_complexification` (792) | `bpP:p5:ext-loc / helper` | PASS | Matches source role; no additional defect found. |
| `real_slice_identity` (801) | `bpP:p5:ext-glue / helper` | PASS | Matches source role; no additional defect found. |
| `connected_complex_tube` (808) | `bpP:p5:be-jet / helper` | PASS | Matches source role; no additional defect found. |
| `fourth_jet_unique` (813) | `bpP:p5:be-coef / helper` | PASS | Matches source role; no additional defect found. |
| `schwarz_order_five` (820) | `bpP:p5:ur-schwarz / helper` | PASS | Matches source role; no additional defect found. |
| `schur_inverse_blocks` (826) | `bpP:p5:fi-inv / helper` | PASS | Matches source role; no additional defect found. |
| `finite_measure_coordinate_cut` (834) | `bpP:p5:st-ivt / helper` | PASS | Matches source role; no additional defect found. |
| `section_measure_le_of_pairwise_dist` (839) | `bpP:p4:ext-tonelli` | PASS | N2 resolved: arbitrary real sections, including nonmeasurable sets. |
| `ext_tonelli` (844) | `bpP:p4:ext-tonelli` | PASS | Product-coordinate Tonelli; auxiliary diameter helper is N2. |
| `log_power_dominated` (850) | `bpP:p5:kam-cond#scales / helper` | PASS | Matches source role; no additional defect found. |
| `kam_c1` (854) | `bpP:p5:kam-hyp#C1` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGScales` (859) | `bpP:p5:kam-cond` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgTau` (864) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgK0` (866) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgChat` (869) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGScaleSpec` (871) | `bpP:p5:kam-cond` | PASS | Source formula/carrier; no changed norm or global instance. |
| `kam_cond` (879) | `bpP:p5:kam-cond` | PASS | Matches source role; no additional defect found. |
| `pgScales` (881) | `bpP:p5:kam-cond` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGParameters` (884) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `params` (900) | `bpP:p5:params` | PASS | Literal formulas; K0 data-only; period-one gamma thresholds. |
| `checkedCore` (912) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgActionDomain` (915) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `admissible` (918) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgCgamma` (922) | `bpP:p5:rstar#Cgamma` | PASS | Source formula/carrier; no changed norm or global instance. |
| `rstar` (925) | `bpP:p5:rstar` | PASS | Data-only preliminary threshold; final measure shrink separated. |
| `pgRstar` (948) | `bpP:p5:rstar` | PASS | Source formula/carrier; no changed norm or global instance. |
| `param_facts` (950) | `bpP:p5:param-facts` | PASS | Other source guards are in rstar; no new frozen premise. |
| `r_k` (957) | `bpP:p5:rK` | PASS | Matches source role; no additional defect found. |
| `PGAveraging` (962) | `bpP:p5:avg` | PASS | Source formula/carrier; no changed norm or global instance. |
| `averagingDomain` (966) | `bpP:p5:avg` | PASS | Source formula/carrier; no changed norm or global instance. |
| `realAverageMap` (970) | `bpP:p5:avg` | PASS | Source formula/carrier; no changed norm or global instance. |
| `AveragingSpec` (974) | `bpP:p5:avg` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgOscNormalize` (1007) | `bpP:p5:avg / conformal normalization` | PASS | Correct conformal factor 2*pi, including oscillator scaling. |
| `pgOscUnnormalize` (1011) | `bpP:p5:avg / inverse normalization` | PASS | Exact inverse of normalization on the full carrier. |
| `pgOscP` (1015) | `bpP:p5:avg / normalized perturbation` | PASS | New adapter definition; correct constrained carrier and scaling. |
| `pgOscH` (1017) | `bpP:p5:avg / normalized Hamiltonian` | PASS | Required H0/(2*pi); derivative scaling exposes F7. |
| `pgOscE` (1018) | `bpP:p5:avg / normalized size` | PASS | New adapter definition; correct constrained carrier and scaling. |
| `pgOscEpsilon` (1019) | `bpP:p5:avg / oscillator radius` | PASS | New adapter definition; correct constrained carrier and scaling. |
| `pgOscWidth` (1020) | `bpP:p5:avg / geometric width` | PASS | New adapter definition; correct constrained carrier and scaling. |
| `pg_osc_hyp` (1021) | `stepP:p5:av-R1 / av-R2` | FAIL | F7: wrong uniform divisor; loses 2*Kbar^tau. |
| `pg_osc_bound` (1026) | `bpP:p5:avg / unit perturbation` | PASS | Original weighted bound survives normalized Fourier slice. |
| `pg_osc_positive` (1029) | `bpP:p5:avg / positivity` | PASS | Follows from existing thresholds and positive data. |
| `pg_osc_zero` (1031) | `stepP:p5:av-id` | PASS | Actual Fourier zero mode equals actual normalized average. |
| `pg_osc_normalization` (1039) | `stepP:p5:av-dict` | PASS | Correct inverse identities and conformal form identity. |
| `pg_osc_domain` (1045) | `stepP:p5:av-dict` | PASS | Exact scaled half-domain equality in the max norm. |
| `avg` (1054) | `bpP:p5:avg` | PASS | Source contract unchanged; advertised P2 supplier blocked by F7. |
| `pgAvg` (1057) | `bpP:p5:avg` | PASS | Source formula/carrier; no changed norm or global instance. |
| `phi` (1060) | `bpP:p5:phi` | PASS | Source formula/carrier; no changed norm or global instance. |
| `phiDomain` (1063) | `bpP:p5:phi` | PASS | Source formula/carrier; no changed norm or global instance. |
| `phi_chart` (1067) | `bpP:p5:phi-chart` | PASS | Matches source role; no additional defect found. |
| `oscillatorPolarComplex` (1074) | `bpP:p5:kam-hyp / polar bridge` | PASS | Source formula/carrier; no changed norm or global instance. |
| `oscillatorPolarComplex_real` (1079) | `bpP:p5:kam-hyp / polar bridge` | PASS | Matches source role; no additional defect found. |
| `kamH` (1084) | `bpP:p5:kam-hyp` | PASS | Source formula/carrier; no changed norm or global instance. |
| `kamF` (1087) | `bpP:p5:kam-hyp` | PASS | Source formula/carrier; no changed norm or global instance. |
| `kam_hyp` (1093) | `bpP:p5:kam-hyp` | PASS | Matches source role; no additional defect found. |
| `location` (1112) | `bpP:p5:location` | PASS | Matches source role; no additional defect found. |
| `pgD0` (1117) | `bpP:p5:kset` | PASS | Same predicate; move ownership upstream (F8). |
| `pgKamScale` (1122) | `bpP:p5:kam-hyp / bpP:p3:constants` | PASS | Correct field order; L definitionally initialL. |
| `pg_kam_hyp` (1127) | `bpP:p5:kam-hyp` | PASS | Widths, inverse rows, complex derivative maps match P3. |
| `pg_kam_dictionary` (1130) | `bpP:p5:kam-cond / exact P3 dictionary` | PASS | Numerical/D0 equalities correct; placement must change (F8). |
| `PGFamily` (1139) | `bpP:p5:kset` | PASS | Source formula/carrier; no changed norm or global instance. |
| `physicalTorus` (1142) | `bpP:p5:kset` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGFamilySpec` (1146) | `bpP:p5:torus-conv` | PASS | Unchanged faithful type; supplying P2 route has F7. |
| `torus_conv` (1168) | `bpP:p5:torus-conv` | PASS | Joint upstream output has required family data; downstream of F7. |
| `pgFamily` (1171) | `bpP:p5:torus-conv` | PASS | Choice from output witness, not an added hypothesis. |
| `kset` (1174) | `bpP:p5:kset` | PASS | Source formula/carrier; no changed norm or global instance. |
| `rawUnion` (1178) | `bpP:p5:kset` | PASS | Source formula/carrier; no changed norm or global instance. |
| `outputRepresentative` (1182) | `bpP:p5:cell-transfer` | PASS | Source formula/carrier; no changed norm or global instance. |
| `cell_transfer` (1186) | `bpP:p5:cell-transfer` | PASS | Output cell; mixed-lattice counting; whole unions by definition. |
| `kamMeasureConstant` (1193) | `bpP:p3:two-scale-kam / p5:budget` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgMeasureUpper1` (1195) | `bpP:p5:budget#constant` | PASS | F5 resolved: positive-volume denominator and same inverse bounds. |
| `pgMeasureUpper2` (1204) | `bpP:p5:budget#constant` | PASS | F5 resolved: exact slow lattice constant. |
| `pgBudget` (1207) | `bpP:p5:budget` | PASS | F5 resolved: explicit data-only sum; no family dependence. |
| `budget` (1213) | `bpP:p5:budget` | PASS | F5 resolved: bound uses that explicit sum. |
| `pgLoss` (1221) | `bpP:p5:lower` | PASS | Exact printed sum, once its component contracts are repaired. |
| `lower` (1225) | `bpP:p5:lower` | PASS | Matches source role; no additional defect found. |
| `finalRadius` (1230) | `bpP:p5:rstar / final shrink` | PASS | Source formula/carrier; no changed norm or global instance. |
| `strictness` (1233) | `bpP:p5:strictness` | PASS | Whole-torus deletion; added finalRadius is explicit source smallness. |
| `frequency_bounds` (1241) | `bpP:p5:torus-conv / frequencies` | PASS | Matches source role; no additional defect found. |
| `main` (1247) | `bpP:p5:main` | PASS | Exact frozen telescope and conclusion retained. |

| Typed application | Verdict | Reason |
|---|---|---|
| S:1050–1052, averaged_remainder | FAIL as supplied | Elaborates, but consumes the false pg_osc_hyp. Correct its α as in F7; no upstream theorem change is needed. |
| S:1135–1136, two_scale_kam | PASS for its type | KamHyp fields match; hL is definitionally reflexive. This does not prove pg_kam_hyp or the preceding averaging construction. |

## Consumers, frozen objects, definitions and packages

**Consumers: FAIL at the new averaging boundary (F7).** Direct searches still show no P4/P5 label consumers in I or N, including N Parts 7/11/12. P3b consumes the real-frequency/threshold dictionary and Part 4 loss estimate; those definitions are unchanged. Revised internal P5 consumers correctly project the new collar, regularity and explicit budget contracts. P1 cyl_pipeline uses the unchanged physicalTorus/chart construction and same period-one frequency. Joint P3 output gives raw(J,theta)=Phi(theta,i(J)) by its I0 inverse clause; its scaled Lipschitz bounds have positive scales and can be converted to ordinary Pi/Prod norms for raw parameter cells and null slices. No output-cell preservation by averaging is required. P2 now has concrete types, but the source cannot supply the excessive divisor α.

**Frozen objects: PASS.** Re-read frozen IsDiophantine/actionNbhd and the planetary fast-diffeomorphism, Birkhoff, cylinder-torus/Kolmogorov and Hamiltonian definitions used in the changed interfaces. The core uses the actual frozen Diophantine predicate, which is why F7 cannot be hidden by a different nonresonance definition. PGData and main are unchanged; main's entire telescope/conclusion exactly matches the frozen declaration after theorem-name substitution. New normalization/zero-mode helpers refer to the actual selected extension and constructed average. No parallel solution predicate, new source assumption, boundary identification of arbitrary total coefficient functions, or frozen edit was introduced.

**Definitions: PASS, with the false theorem target F7 excluded.** Exact P23 fixtures have matching types and bodies after whitespace normalization; the moved twoScaleDiophantine body is unchanged. NormalForm.freq resolves before Planetary.freq is declared, preserving the derivative-based upstream meaning. The new T scales fast angles by c and both oscillator coordinates by sqrt(c), so T*omega=c*omega and conjugation of a symplectic map is sound. Oscillator and strip half-domains are scaled consistently. New structures are source records or produced outputs, with no extra conclusion-shaped source premise. No global Pi/matrix instance is installed. Constants remain chosen before r and mu; pgBudget is now a formula and does not depend on a selected torus family.

**Packages: FAIL (F8), otherwise the earlier split remains viable.** Thirty-six packages in seventeen waves, estimated 150–800 lines each, remain below the 1,500-line Lean cap; the 1,282-line fixture also fits. The new pgD0 reference must be placed below KAMInputs and Family. Earlier N2 ownership fixes and moving the actual cut measure after Family are correct. Provider quarantine and generated/frozen-file restrictions remain intact. The twelve SOURCE_GAPs are still explicitly unpaid proof obligations; no source gap is discharged by these sorry signatures or #check outputs.

## Validation and handoff

Only this report is a persistent audit edit. The original shared signatures, revision-1 report, design, frozen files, manifest and generated files were not edited. Scratch signature/API copies used `.lake/abi-scratch/` and were deleted after checks. No state-changing git command or production build was run. All issued Lean invocations were serial, through the required gate with LEAN_NUM_THREADS=1 and nice -n 5; no heartbeat/recursion/synthesis overrides.

- `git log -1` confirms HEAD `145a2ce0af84347d8f675bf7b65169b9301991d9`. Revision diff: one design document, 522 insertions and 101 deletions. Original audit report remained untracked at the start.
- Appendix/shared signatures: byte-identical. SHA256 of audited shared file: `0cda6670cd3dddae5adf778ea94b5fd57c9fdc6bc8acc5262fb3b0087d301cba`. Exact frozen telescope comparison: True. Local P4/P5/current-inp source identity: True.
- `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p45 .lake/abi-scratch/P45R2AuditSignatures.lean`: exit 0; exactly 69 declaration-uses-sorry warnings; no other warnings/errors. Ran the submitted revision once. Both #check fun applications elaborate. Log: `/tmp/p45-r2-audit-signatures.log`.
- `#print axioms KAM.Planetary.main`: `[propext, sorryAx, Classical.choice, Quot.sound]`. This is a design stub, not a proved provider.
- API probe: same gate on `.lake/abi-scratch/P45R2AuditAPIs.lean`, exit 0; all 22 #checks resolve; no warnings/errors. Types inspected include parametric holomorphic integration, sup/weighted conversion, Lipschitz image measure, block inverse, finite-measure limits, chain rule and mixed derivative symmetry. Exact P23 fixture comparison includes both complete upstream theorem types. Log: `/tmp/p45-r2-audit-apis.log`.
- `PATH=/root/code/KAM-inp-design-p45/.drafts/scratch/gated-bin:$PATH LEAN_NUM_THREADS=1 scripts/lint_sources.sh`: **exit 1**. The independent run printed `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)` and `FROZEN-ANCHOR GUARD OK`, then the gated ABI subprocess returned nonzero with only its slot-acquisition message and no Lean diagnostic. **No ABI HASHES OK receipt was produced.** The cause of the subprocess failure is undetermined; this is not evidence of ABI drift. The scratch ABI file was removed by the script's finally clause. Log: `/tmp/p45-r2-audit-lint.log`. The designer's previous successful lint receipt is not substituted for this incomplete independent check. No additional memory-intensive retry was launched.
- Final validation: 201/201 declaration rows; balanced fenced blocks; no trailing whitespace; terminal newline present; `git diff --check` exits 0. The original shared-signature hash is unchanged. Git status lists only the pre-existing untracked audit-1 report and this new audit-2 report, with no tracked changes. All manually created probe files were removed. The signature elaboration is the targeted Lean check for a report/design-only audit; there is no changed production module to build.

**Uncertainties, errata and deviations:** no new pinned-paper erratum is alleged. F7 is a transcription/normalization error relative to the explicit blueprint av-R1 inequality, not an error in that inequality. F8 is a module-ownership error. The previously noted missing muStar≤mu0 blueprint condition is explicitly repaired as produced output. The positive enclosing Ry enlargement is now declared and used consistently. Inherited allegations concerning CP10 covering uniformity/rescaled resonances/collars/shell exponents/uniform remainder, and CP11 strict upper measure, were not re-adjudicated against pinned PDFs. No frozen premise or conclusion is changed by either proposed fix. Proposed replacement statements and estimate calculations above are report-only recommendations, not independently proved Lean code.
