# Independent design audit 1: P45

Overall verdict: **FAIL**.

Audited branch `inp-design-p45`, HEAD `f8f8fb17c5f24392d90afdc34b521f27006c16bd`, against `git diff inp...HEAD`. The branch adds only the 1,521-line design. The audit concerns design contracts, not proof closure. The exact frozen P-G telescope is preserved, and the submitted signatures elaborate, but several blueprint conclusions have been omitted or narrowed. The missing source-parameter guard also prevents the advertised frequency-inverse interface from following from its supplied bounds.

Inputs read: repository AGENTS.md, docs/PLAN.md, docs/DECISIONS.md; `/root/code/KAM-inp/.drafts/briefs/inp-audit-design.md`; the design, its Appendix A, the original shared signatures, and `.drafts/handoff-DESIGN-P45.md`; local P Parts 4–5; authoritative inp `docs/graph/P/packets/P-p4.nodes.md`, `P-p5.nodes.md` and their SOURCE_GAP records; P1, P23 and Kepler/P7 signature interfaces; the frozen definitions identified below. Local P4/P5 blueprint files are byte-identical to the current inp copies. The 124-node ownership table does not imply 124 complete signature contracts.

Locators below use `S:L` for `/root/code/KAM-inp/.drafts/design/P45Signatures.lean:L` (also Appendix A at design line L+576), `P4:L` and `P5:L` for the two blueprint source files. Graph locators are the corresponding `NODE:` records in the packets above. Proposed blocks are report text only and have not been independently elaborated; submitted signatures were run exactly once.

## Findings and proposed fixes

### F1 — Medium: collar compactness acquires an extra radius premise

`S:93–100`, `bpP:p4:collar`, P4:22–29. The single telescope puts `htd : t < d` in front of **every** clause. Source clause (a) asserts compactness for every `t > 0`, independently of the collar bound or its radius. The set-difference description and the derived lower-volume clause are also absent. Dropping connectedness is sound here: positive-distance cores of bounded open sets are compact even when disconnected. Dropping positive A is harmless for the printed conditional estimates. The extra radius premise on (a) is not a permissible strengthening.

Replace the combined source signature with the following scoped version (using witness distance, consistent with `innerCore`):

```lean
theorem collar {V : Set (Fin a → ℝ)}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {A d : ℝ}
    (hc : ∀ s : ℝ, 0 < s → s < d →
      volume {I : Fin a → ℝ | ∃ J ∈ frontier V, dist I J < s} ≤
        ENNReal.ofReal (A*s)) :
    (∀ t : ℝ, 0 < t →
      IsCompact (innerCore V t) ∧ innerCore V t ⊆ V ∧
      V \ innerCore V t =
        {I ∈ V | ∃ J ∈ frontier V, dist I J < t}) ∧
    (∀ t : ℝ, 0 < t → t < d →
      volume (V \ innerCore V t) ≤ ENNReal.ofReal (A*t) ∧
      volume V - ENNReal.ofReal (A*t) ≤ volume (innerCore V t)) ∧
    (∀ t s : ℝ, 0 < s → s < t →
      realNbhd (innerCore V t) s ⊆ V ∧
      realNbhd (innerCore V t) s \ innerCore V t ⊆ V \ innerCore V t) ∧
    (∀ t s : ℝ, 0 < s → s < t → t < d →
      volume (realNbhd (innerCore V t) s \ innerCore V t) ≤
        ENNReal.ofReal (A*t)) := by sorry
```

### F2 — Major: Birkhoff extension drops parameter continuity and symmetry

`S:386–400`, `bpP:p5:birkhoff-ext`, P5:49–61; especially graph `stepP:p5:be-an`. The source conclusion explicitly includes continuity in μ of the constructed coefficients and symmetry of the constructed complex beta. The signature exports neither. Equality with the real frozen beta only on V does not itself state complex symmetry on the tube. Separate holomorphy at each μ does not supply uniform bounds over the compact μ interval. The frequency-bounds proof therefore needs additional unexported work at exactly this boundary.

Preserve the existing conclusions and append the following complete additional bridge signature, owned by Jets; treat the pair as the contract for `birkhoff-ext`:

```lean
theorem birkhoff_ext_parameter_regularity (d : PGData a b) :
    ContinuousOn
      (fun z : ℝ × (Fin a → ℂ) => jetP0 d z.1 z.2)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V)
        ((pgExtension d).delta/2)) ∧
    (∀ j, ContinuousOn
      (fun z : ℝ × (Fin a → ℂ) => jetOmega d z.1 z.2 j)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V)
        ((pgExtension d).delta/2))) ∧
    (∀ i j, ContinuousOn
      (fun z : ℝ × (Fin a → ℂ) => jetBeta d z.1 z.2 i j)
      (Icc 0 d.mu0 ×ˢ KAM.actionNbhd (closure d.V)
        ((pgExtension d).delta/2))) ∧
    (∀ mu ∈ Icc 0 d.mu0,
      ∀ I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/2),
        (jetBeta d mu I).IsSymm) := by sorry
```

This is additional proved output, not an additional source assumption. No boundary identities for the arbitrary frozen total functions are proposed.

### F3 — Medium: polynomial-bound domain is narrowed from 2 to 1

`S:442–443, 474–476`, `PGAnalyticSpec` and `freq_data`; `bpP:p5:freq-data`, P5:104–112. The source bounds N and its first two derivatives on the slow-action ball `|J₂| < 2`. The supplied specification uses `analyticDomain`, whose slow ball is `< 1`. The ball of radius 1 is the later injectivity domain `E₁`, not the radius-2 bound domain `E`. These roles must remain distinct. Current downstream applications on the smaller ball may still be provable, but that does not preserve the source contract.

### F4 — Major: inverse theorem extends beyond the μ domain of all supporting bounds

`S:452–479, 494–503`, `PGAnalyticSpec`, `freq_data`, `freq_inj`; P5:104–125. Every polynomial, Lipschitz and beta-inverse bound in the specification is restricted to `mu ∈ Icc 0 d.mu0`. In contrast, `freq_inj` quantifies over `Ioc 0 (pgAnalytic d).muStar`, and the specification only says `muStar ≤ 1`. There is no `muStar ≤ d.mu0`. `PGExtension.P` is wholly unconstrained for μ outside `[0,mu0]`; its jets can be degenerate there. The existential choice of an analytic record does not expose an unstated property of the selected witness.

This is a missing interface guarantee, not a claimed counterexample to frozen P-G. Later admissibility includes μ<mu0, so the frozen goal does not require the excessive range. The same missing guard occurs in the printed P5 frequency-inverse statement; record it as a blueprint defect. Repair by *proving* `muStar ≤ mu0` when selecting the data, preserving the existing `freq_inj` telescope. F3/F4 are repaired together by replacing `PGAnalyticSpec` as below (all unchanged clauses are retained literally).

```lean
def analyticBoundDomain (d : PGData a b) (p : PGAnalytic) :
    Set (Fin (a+b) → ℂ) :=
  {J | blockFast J ∈ KAM.actionNbhd (closure d.V) p.rho ∧
    ‖blockSlow J‖ < 2}

def PGAnalyticSpec (d : PGData a b) (p : PGAnalytic) : Prop :=
  0 < p.rho ∧ p.rho < (pgExtension d).delta/16 ∧ 0 < p.c0 ∧
  1 ≤ p.M0 ∧ 1 ≤ p.AN ∧ 1 ≤ p.LN ∧ 1 ≤ p.LB ∧ 0 < p.muStar ∧ p.muStar ≤ 1 ∧ p.muStar ≤ d.mu0 ∧
  1 ≤ p.LP ∧ (pgExtension d).MP * KAM.Weighted.coth ((pgExtension d).delta/4)^a ≤ p.LP ∧ 0 < p.CQ ∧ 0 < p.r1 ∧ p.r1 ≤ pgOscRadius d ∧ 0 < p.Cdio ∧
  p.muStar*p.AN ≤ p.c0/2 ∧ 4*p.muStar*p.AN^2*p.LB ≤ p.c0 ∧
  2*p.muStar*p.LN^2*p.LB < p.c0 ∧ p.LN ≤ p.AN ∧
  (∀ gamma : ℝ, 0 < gamma →
    volume {I ∈ d.V | ¬ KAM.IsDiophantine gamma ((a+b:ℕ)+1) (fastFrequency d.H0 I)} ≤
      ENNReal.ofReal (p.Cdio*gamma)) ∧
  (∀ z ∈ KAM.actionNbhd (closure d.V) p.rho, ∀ z' ∈ KAM.actionNbhd (closure d.V) p.rho,
    p.c0*‖z-z'‖ ≤ ‖complexFast d z-complexFast d z'‖) ∧
  (∀ z ∈ KAM.actionNbhd (closure d.V) (2*p.rho), ‖fderiv ℂ (complexFast d) z‖ ≤ p.M0) ∧
  (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) p.rho,
    ∀ I' ∈ KAM.actionNbhd (closure d.V) p.rho, ∀ xi : Fin b → ℂ, ‖xi‖ ≤ 1 →
      ‖(fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi)) I (Pi.single i 1)) -
        (fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi)) I' (Pi.single i 1))‖ ≤ p.LN*‖I-I'‖ ∧
      ‖(jetOmega d mu I+(jetBeta d mu I).mulVec xi) -
        (jetOmega d mu I'+(jetBeta d mu I').mulVec xi)‖ ≤ p.LN*‖I-I'‖) ∧
  (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) p.rho,
    ∀ xi xi' : Fin b → ℂ, ‖xi‖ ≤ 1 → ‖xi'‖ ≤ 1 →
      ‖(fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi)) I (Pi.single i 1)) -
        (fun i => fderiv ℂ (fun I => jetPolynomial d mu (Fin.append I xi')) I (Pi.single i 1))‖ ≤ p.LN*‖xi-xi'‖) ∧
  (∀ mu ∈ Icc 0 d.mu0, ∀ J ∈ analyticBoundDomain d p,
    ‖jetPolynomial d mu J‖ ≤ p.AN ∧ ‖fderiv ℂ (jetPolynomial d mu) J‖ ≤ p.AN ∧
      ‖fderiv ℂ (fderiv ℂ (jetPolynomial d mu)) J‖ ≤ p.AN) ∧
  (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) p.rho, ∀ v : Fin b → ℂ,
    ‖v‖ ≤ p.LB*‖(jetBeta d mu I).mulVec v‖) ∧
  (∀ mu ∈ Icc 0 d.mu0, ∀ I ∈ KAM.actionNbhd (closure d.V) ((pgExtension d).delta/4),
    ∀ x : PGComplexPhase b, ‖x‖ ≤ p.r1 → ‖pgRemainder d mu I x‖ ≤ p.CQ*‖x‖^5)
```

The corrected `freq_data` signature remains:

```lean
theorem freq_data (d : PGData a b) : ∃ p : PGAnalytic, PGAnalyticSpec d p := sorry
```

The corrected `freq_inj` signature remains the following, now backed by the repaired specification:

```lean
theorem freq_inj (d : PGData a b) : ∀ mu ∈ Ioc 0 (pgAnalytic d).muStar,
    InjOn (complexFrequency d mu) (analyticDomain d (pgAnalytic d)) ∧
    ∀ J ∈ analyticDomain d (pgAnalytic d),
      ∃ T : (Fin (a+b) → ℂ) ≃L[ℂ] (Fin (a+b) → ℂ),
        (∀ v, T v = fderiv ℂ (complexFrequency d mu) J v) ∧
        ‖T.toContinuousLinearMap‖ ≤ pgCU (pgAnalytic d) ∧
        ‖T.symm.toContinuousLinearMap‖ ≤ pgCU (pgAnalytic d)/mu ∧
        (∀ v, ‖blockFast (T.symm v)‖ ≤ pgCU (pgAnalytic d)*‖v‖) ∧
        (∀ v, ‖blockSlow (T v)‖ ≤ pgCU (pgAnalytic d)*mu*‖v‖) := sorry
```

### F5 — Medium: the explicit one-scale and budget constants become arbitrary witnesses

`S:423–427, 874–880`; `bpP:p5:dio-one` (P5:96–102) and graph `bpP:p5:budget#constant` (P5:286–287). `dio_one` proves only existence of Cdio, losing the printed `2 Λg^a S₁ (2 Ry)^(a−1)`. `budget`/`pgBudget` similarly select an arbitrary bound instead of the graph's explicit sum. Their data-only quantifier order is correct, and this does not invalidate a qualitative existence proof, but these are weaker contracts than the assigned numerical nodes. The design explicitly preserves other constants; it must preserve these too or obtain a recorded blueprint/graph change.

For the existing selected inverse bounds, expose the following concrete estimates. Using a positive enclosing Ry rather than its exact maximum is a declared enlargement and should be recorded; it avoids a zero-radius box. These statements replace the weaker existential contracts; retain convenient existential corollaries under different helper names if needed.

```lean
def dioConstant (d : PGData a b) (tau : ℝ) : ℝ :=
  2*(pgInverseL d)^a*latticeS (a+b) tau*(2*pgInverseR d)^(a-1)

theorem dio_one (d : PGData a b) {tau : ℝ} (ht : (a+b:ℕ) < tau) :
    0 < dioConstant d tau ∧ ∀ gamma : ℝ, 0 < gamma →
      volume {I ∈ d.V | ¬ KAM.IsDiophantine gamma tau
        (fastFrequency d.H0 I)} ≤
          ENNReal.ofReal (dioConstant d tau*gamma) := by sorry

def pgMeasureUpper1 (d : PGData a b) : ℝ :=
  let p := pgAnalytic d
  let t := pgTau a b
  (pgInverseL d)^(a+b)/((volume d.V).toReal/2) *
    max (4*(2*pgInverseR d)^(a-1)*latticeS (a+b) t)
      (4*b^2*p.LB*(2*pgInverseR d)^a *
        (2*3^(a+b-1)/(t+1-(a+b:ℕ))) *
        (4*p.LN*pgInverseL d)^(t+1-(a+b:ℕ)))

def pgMeasureUpper2 (d : PGData a b) : ℝ :=
  b*(pgAnalytic d).LB*latticeS b (pgTau a b+1)

def pgBudget (d : PGData a b) : ℝ :=
  4^(b+1)*2*Real.pi*(pgScales d).k0 *
    (5*pgMeasureUpper1 d+4*pgMeasureUpper2 d) +
    8*(pgBoundaryA d+(pgAnalytic d).Cdio*pgCgamma d)/
      (volume d.V).toReal + b*(pgScales d).k1/16

theorem budget (d : PGData a b) : 0 < pgBudget d ∧
    ∀ r mu : ℝ, ∀ h : admissible d (pgRstar d) r mu,
      volume (({z : Phase (a+b) | z.2 ∈ pgActionDomain d r mu ∧
        z.1 ∈ unitCube (a+b)}) \ rawUnion d r mu h (pgD0 d r mu)) ≤
        ENNReal.ofReal (kamMeasureConstant (a+b)*pgBudget d*Real.sqrt r)*
          volume (pgActionDomain d r mu) := by sorry
```

Move the numeric `pgBudget` definition before `budget` in ActionBudget (or a lower numeric module). The PGAnalyticSpec estimate for its Cdio can remain an arbitrary valid larger bound; the explicit `dio_one` node must still be exported.

### F6 — Medium: polar volume signature omits the null-centre coverage clause

`S:287–289`, `bpP:p4:disc-measure` clause (b), P4:173–185. The design splits chart, image and shell conclusions into four signatures, but none states that the cylinder cell is covered by the polar-cell image up to a null set. The numeric cell volume is not a substitute for this set-level clause, and the graph's `stepP:p4:dm-cell` retains it. Add it to `disc_measure` as follows, or export it separately from the same package:

```lean
theorem disc_measure {V : Set (Fin a → ℝ)} (hV : MeasurableSet V)
    {r : ℝ} (hr : 0 < r) :
    volume (cylinderCell (b:=b) V r) =
      ENNReal.ofReal ((2*Real.pi)^(a+b)*(r^2/2)^b)*volume V ∧
    volume (cylinderCell (b:=b) V r \ polarCellMap ''
      {z : Phase (a+b) | blockFast z.2 ∈ V ∧
        blockSlow z.2 ∈ actionShell b 0 (r^2/2) ∧
        z.1 ∈ unitCube (a+b)}) = 0 := by sorry
```

### N1 — Medium, dispatch gate: P2/P3 application has not been made concrete

Design §5 and handoff accurately label these interfaces pending. Current `/root/code/KAM-inp/.drafts/design/P23Signatures.lean` now supplies `OscHyp`/`averaged_remainder` (L297–367), `ScaleData`/`KamHyp` (L512–543), and the joint `two_scale_kam` output (L811 onward). The P45 package declarations do not contain a typed application/adapter to these records. Their named `limit_actions`/`limit_phi` expectations should be reconciled with the actual joint output.

The KAM-side carriers, inverse-row bounds, unit-cell convention, and weighted width `pgWidth/(24*pi)` match after block-name and derivative-extensionality bridges; `L=C1/mu`, `s=pgWidth/60`, `sbar=pgWidth/15` give the intended numerical dictionary. P1 `cyl_pipeline` accepts the stronger fast-lattice Q2 supplied by `phi_chart`, with unchanged period-one frequency. P1 null-image bounds apply to the raw input-cell parametrization after swapping angle/action factors; they do not require the averaging map to preserve a physical cell.

P2 additionally requires explicit oscillator/fast-angle normalization, the zero-mode identification with `complexAverage`, and the exact transformed-domain/displacement factors. An informal reference to period conversion is not an elaborated application of its canonical flow theorem. Do not dispatch Averaging/Family as interface-approved until adapter signatures and their exact upstream applications are reviewed. No frozen premise should be added to resolve this.

### N2 — Low: package ownership needs two small repairs

Design §8 estimates 36 files, each 150–800 lines, in an otherwise acyclic 17-wave order. `beta_inverse` has a signature but no named package output. `ext_conn` is required by P4-CO but has no explicit supplying package. Assign `ext_conn` to Collar (proved before `collar`) and `beta_inverse` to a small torsion algebra module, or explicitly to ResonanceSlow before use. The short-section diameter bound promised by P4-TO has no exported signature; add a helper (or name its exact Mathlib supplier):

```lean
theorem section_measure_le_of_pairwise_dist {E : Set ℝ} {delta : ℝ}
    (hd : 0 ≤ delta)
    (hE : ∀ x ∈ E, ∀ y ∈ E, dist x y ≤ delta) :
    volume E ≤ ENNReal.ofReal delta := by sorry
```

This is supplemental output for `bpP:p4:ext-tonelli`, not a defect in its product Tonelli inequality. Keep the radius-2 bound domain separate from analyticDomain; do not enlarge the later inverse domain inadvertently when fixing F3.

## Signature-by-signature decisions

Every explicit declaration in the 944-line file appears once below (143 rows: 57 theorems and 86 definitions/structures/abbreviations). Namespace throughout: `KAM.Planetary`. A PASS means the individual mathematical signature/definition has no additional identified defect; it is not an approval of an unverified proof or of unresolved upstream adapters. A theorem can have a faithful type while still depending on a failed supplying contract. Labels marked “helper” are deliberate implementation lemmas for the stated blueprint step, not source theorems with silently changed premises.

| Lean name (S line) | Blueprint label | Verdict | Reason |
|---|---|---|---|
| `blockFast` (36) | `bpP:p4:conv#data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `blockSlow` (37) | `bpP:p4:conv#data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `blockFast_real` (38) | `bpP:p4:conv#data` | PASS | Matches source role; no additional defect found. |
| `blockSlow_real` (39) | `bpP:p4:conv#data` | PASS | Matches source role; no additional defect found. |
| `PGData` (42) | `bpP:p5:order` | PASS | Literal frozen premises; connected includes nonempty. |
| `pgBoundaryA` (74) | `bpP:p5:order` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgBoundaryD` (76) | `bpP:p5:order` | PASS | Source formula/carrier; no changed norm or global instance. |
| `realNbhd` (79) | `bpP:p4:conv#data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `innerCore` (82) | `bpP:p4:conv#data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `actionShell` (85) | `bpP:p4:conv#shell` | PASS | Source formula/carrier; no changed norm or global instance. |
| `joinedActions` (87) | `bpP:p4:conv#data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `unitCube` (90) | `bpP:p1:torus-union` | PASS | Source formula/carrier; no changed norm or global instance. |
| `collar` (93) | `bpP:p4:collar` | FAIL | F1: radius restriction and missing clauses |
| `ext_deriv` (103) | `bpP:p4:ext-deriv` | PASS | Derivative analyticity; partial-C1 Lipschitz work is separately packaged. |
| `ext_conn` (107) | `bpP:p4:ext-conn` | PASS | Matches source role; no additional defect found. |
| `realNbhd_joinedActions` (110) | `bpP:p4:domain-collar / helper` | PASS | Exact max-norm product, including empty factors. |
| `lip_compact_c1` (114) | `bpP:p4:lip-compact / conditional helper` | PASS | Distinct conditional helper; does not replace partial-C1 result. |
| `lip_compact` (121) | `bpP:p4:lip-compact` | PASS | Matches source role; no additional defect found. |
| `lip_inverse` (129) | `bpP:p4:lip-inverse` | PASS | Matches source role; no additional defect found. |
| `pgInverse` (140) | `bpP:p4:lip-inverse` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgInverseL` (143) | `bpP:p4:lip-inverse` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgInverseR` (146) | `bpP:p4:lip-inverse` | PASS | Source formula/carrier; no changed norm or global instance. |
| `beta_inverse` (149) | `bpP:p4:beta-inverse` | PASS | Dropping symmetry is a true stronger adjugate estimate. |
| `secularPolynomial` (154) | `bpP:p4:freq` | PASS | Source formula/carrier; no changed norm or global instance. |
| `slowFrequency` (160) | `bpP:p4:freq` | PASS | Source formula/carrier; no changed norm or global instance. |
| `freq` (165) | `bpP:p4:freq` | PASS | Source formula/carrier; no changed norm or global instance. |
| `MeasureData` (174) | `bpP:p4:data` | PASS | N1/N2 use mu G; positive finite compact core; inverse bounds. |
| `affine_slab` (222) | `bpP:p4:affine-slab` | PASS | Matches source role; no additional defect found. |
| `latticeWeight` (227) | `bpP:p4:lattice-tail` | PASS | Source formula/carrier; no changed norm or global instance. |
| `lattice_tail` (229) | `bpP:p4:lattice-tail` | PASS | Matches source role; no additional defect found. |
| `resonanceBad` (238) | `bpP:p4:two-scale-diophantine-measure` | PASS | Source formula/carrier; no changed norm or global instance. |
| `latticeS` (244) | `bpP:p4:lattice-tail` | PASS | Source formula/carrier; no changed norm or global instance. |
| `measure_c1` (246) | `bpP:p4:two-scale-diophantine-measure` | PASS | Source formula/carrier; no changed norm or global instance. |
| `measure_c2` (251) | `bpP:p4:two-scale-diophantine-measure` | PASS | Source formula/carrier; no changed norm or global instance. |
| `two_scale_diophantine_measure` (253) | `bpP:p4:two-scale-diophantine-measure` | PASS | Matches source role; no additional defect found. |
| `domain_collar_helper` (263) | `bpP:p4:domain-collar / helper` | PASS | Matches source role; no additional defect found. |
| `oscillatorPolar` (271) | `bpP:p4:s-disc#chart` | PASS | General a,b formula agrees with P7 at a=b. |
| `polarMap` (277) | `bpP:p4:disc-measure / P7 specialization` | PASS | Owner snapshot; specialization bridge explicit. |
| `oscillatorPolar_eq_polarMap` (281) | `bpP:p4:disc-measure / P7 specialization` | PASS | Matches source role; no additional defect found. |
| `polarCellMap` (284) | `bpP:p4:s-disc#chart` | PASS | Source formula/carrier; no changed norm or global instance. |
| `disc_measure` (287) | `bpP:p4:disc-measure` | FAIL | F6: null-coverage clause omitted |
| `disc_measure_image` (291) | `bpP:p4:disc-measure` | PASS | Positive-action cell injectivity; exact (2*pi)^n factor. |
| `disc_measure_shell` (297) | `bpP:p4:disc-measure` | PASS | Matches source role; no additional defect found. |
| `PGComplexPhase` (303) | `bpP:p5:ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `assembleComplex` (305) | `bpP:p5:ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `extensionDomain` (308) | `bpP:p5:ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGExtension` (313) | `bpP:p5:ext` | PASS | Produced witness, no extra provider assumption. |
| `ext` (338) | `bpP:p5:ext` | PASS | Matches source role; no additional defect found. |
| `pgExtension` (340) | `bpP:p5:ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgWidth` (342) | `bpP:p5:consts` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgOscRadius` (344) | `bpP:p5:consts` | PASS | Source formula/carrier; no changed norm or global instance. |
| `complexAverage` (346) | `bpP:p5:consts` | PASS | Source formula/carrier; no changed norm or global instance. |
| `complexAverage_real` (352) | `bpP:p5:birkhoff-ext` | PASS | Uses actual frozen normalized secularAverage. |
| `jetP0` (358) | `bpP:p5:birkhoff-ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `jetOmega` (360) | `bpP:p5:birkhoff-ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `jetBeta` (363) | `bpP:p5:birkhoff-ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `jetPolynomial` (368) | `bpP:p5:birkhoff-ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgRemainder` (372) | `bpP:p5:birkhoff-ext` | PASS | Source formula/carrier; no changed norm or global instance. |
| `consts` (376) | `bpP:p5:consts` | PASS | Matches source role; no additional defect found. |
| `birkhoff_ext` (386) | `bpP:p5:birkhoff-ext` | FAIL | F2: continuity and symmetry omitted |
| `uniform_remainder` (402) | `bpP:p5:uniform-remainder` | PASS | Matches source role; no additional defect found. |
| `lip_complex` (407) | `bpP:p5:lip-complex` | PASS | Matches source role; no additional defect found. |
| `complexFast` (414) | `bpP:p5:bilip` | PASS | Source formula/carrier; no changed norm or global instance. |
| `bilip` (417) | `bpP:p5:bilip` | PASS | Matches source role; no additional defect found. |
| `dio_one` (423) | `bpP:p5:dio-one` | FAIL | F5: explicit constant omitted |
| `PGAnalytic` (429) | `bpP:p5:freq-data` | PASS | Source formula/carrier; no changed norm or global instance. |
| `analyticDomain` (442) | `bpP:p5:freq-inj` | PASS | Correct radius-1 inverse domain; F3 concerns bound-domain use. |
| `complexIntegrable` (445) | `bpP:p5:freq-inj` | PASS | Source formula/carrier; no changed norm or global instance. |
| `complexFrequency` (448) | `bpP:p5:freq-inj` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGAnalyticSpec` (452) | `bpP:p5:freq-data` | FAIL | F3/F4: bound domain and mu guard |
| `freq_data` (482) | `bpP:p5:freq-data` | FAIL | F3/F4: produces deficient specification |
| `pgAnalytic` (484) | `bpP:p5:freq-data` | PASS | Choice from output witness, not an added hypothesis. |
| `pgCU` (486) | `bpP:p5:freq-inj` | PASS | Source formula/carrier; no changed norm or global instance. |
| `complexFrequency_real` (489) | `bpP:p5:freq-inj` | PASS | Identifies derivatives only on V; no boundary claim. |
| `freq_inj` (494) | `bpP:p5:freq-inj` | FAIL | F4: supporting bounds stop at mu0 |
| `IsChart` (506) | `bpP:p1:chart` | PASS | Owner snapshot, same analytic and frozen symplectic predicates. |
| `fullShift` (509) | `bpP:p1:period-convert` | PASS | Source formula/carrier; no changed norm or global instance. |
| `angleScale` (511) | `bpP:p1:period-convert` | PASS | Source formula/carrier; no changed norm or global instance. |
| `twoScaleDiophantine` (513) | `bpP:p1:two-scale` | PASS | Source formula/carrier; no changed norm or global instance. |
| `disc_measure_chart` (519) | `bpP:p4:disc-measure` | PASS | Analytic/symplectic polar chart, determinant and lattice injectivity. |
| `resonanceBad_eq` (530) | `bpP:p4:two-scale-diophantine-measure` | PASS | Matches source role; no additional defect found. |
| `local_real_complexification` (534) | `bpP:p5:ext-loc / helper` | PASS | Matches source role; no additional defect found. |
| `compact_real_complexification` (541) | `bpP:p5:ext-loc / helper` | PASS | Matches source role; no additional defect found. |
| `real_slice_identity` (550) | `bpP:p5:ext-glue / helper` | PASS | Matches source role; no additional defect found. |
| `connected_complex_tube` (557) | `bpP:p5:be-jet / helper` | PASS | Matches source role; no additional defect found. |
| `fourth_jet_unique` (562) | `bpP:p5:be-coef / helper` | PASS | Matches source role; no additional defect found. |
| `schwarz_order_five` (569) | `bpP:p5:ur-schwarz / helper` | PASS | Matches source role; no additional defect found. |
| `schur_inverse_blocks` (575) | `bpP:p5:fi-inv / helper` | PASS | Matches source role; no additional defect found. |
| `finite_measure_coordinate_cut` (583) | `bpP:p5:st-ivt / helper` | PASS | Matches source role; no additional defect found. |
| `ext_tonelli` (588) | `bpP:p4:ext-tonelli` | PASS | Product-coordinate Tonelli; auxiliary diameter helper is N2. |
| `log_power_dominated` (594) | `bpP:p5:kam-cond#scales / helper` | PASS | Matches source role; no additional defect found. |
| `kam_c1` (598) | `bpP:p5:kam-hyp#C1` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGScales` (603) | `bpP:p5:kam-cond` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgTau` (608) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgK0` (610) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgChat` (613) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGScaleSpec` (615) | `bpP:p5:kam-cond` | PASS | Source formula/carrier; no changed norm or global instance. |
| `kam_cond` (623) | `bpP:p5:kam-cond` | PASS | Matches source role; no additional defect found. |
| `pgScales` (625) | `bpP:p5:kam-cond` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGParameters` (628) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `params` (644) | `bpP:p5:params` | PASS | Literal formulas; K0 data-only; period-one gamma thresholds. |
| `checkedCore` (656) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgActionDomain` (659) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `admissible` (662) | `bpP:p5:params` | PASS | Source formula/carrier; no changed norm or global instance. |
| `pgCgamma` (666) | `bpP:p5:rstar#Cgamma` | PASS | Source formula/carrier; no changed norm or global instance. |
| `rstar` (669) | `bpP:p5:rstar` | PASS | Data-only preliminary threshold; final measure shrink separated. |
| `pgRstar` (692) | `bpP:p5:rstar` | PASS | Source formula/carrier; no changed norm or global instance. |
| `param_facts` (694) | `bpP:p5:param-facts` | PASS | Other source guards are in rstar; no new frozen premise. |
| `r_k` (701) | `bpP:p5:rK` | PASS | Matches source role; no additional defect found. |
| `PGAveraging` (706) | `bpP:p5:avg` | PASS | Source formula/carrier; no changed norm or global instance. |
| `averagingDomain` (710) | `bpP:p5:avg` | PASS | Source formula/carrier; no changed norm or global instance. |
| `realAverageMap` (714) | `bpP:p5:avg` | PASS | Source formula/carrier; no changed norm or global instance. |
| `AveragingSpec` (718) | `bpP:p5:avg` | PASS | Source formula/carrier; no changed norm or global instance. |
| `avg` (750) | `bpP:p5:avg` | PASS | Output specification faithful; P2 adapter pending (N1). |
| `pgAvg` (753) | `bpP:p5:avg` | PASS | Source formula/carrier; no changed norm or global instance. |
| `phi` (756) | `bpP:p5:phi` | PASS | Source formula/carrier; no changed norm or global instance. |
| `phiDomain` (759) | `bpP:p5:phi` | PASS | Source formula/carrier; no changed norm or global instance. |
| `phi_chart` (763) | `bpP:p5:phi-chart` | PASS | Matches source role; no additional defect found. |
| `oscillatorPolarComplex` (770) | `bpP:p5:kam-hyp / polar bridge` | PASS | Source formula/carrier; no changed norm or global instance. |
| `oscillatorPolarComplex_real` (775) | `bpP:p5:kam-hyp / polar bridge` | PASS | Matches source role; no additional defect found. |
| `kamH` (780) | `bpP:p5:kam-hyp` | PASS | Source formula/carrier; no changed norm or global instance. |
| `kamF` (783) | `bpP:p5:kam-hyp` | PASS | Source formula/carrier; no changed norm or global instance. |
| `kam_hyp` (789) | `bpP:p5:kam-hyp` | PASS | Matches source role; no additional defect found. |
| `location` (808) | `bpP:p5:location` | PASS | Matches source role; no additional defect found. |
| `pgD0` (813) | `bpP:p5:kset` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGFamily` (818) | `bpP:p5:kset` | PASS | Source formula/carrier; no changed norm or global instance. |
| `physicalTorus` (821) | `bpP:p5:kset` | PASS | Source formula/carrier; no changed norm or global instance. |
| `PGFamilySpec` (825) | `bpP:p5:torus-conv` | PASS | Produced quantitative whole-torus family; N1 dispatch gate. |
| `torus_conv` (847) | `bpP:p5:torus-conv` | PASS | Output specification faithful; P3 adapter pending (N1). |
| `pgFamily` (850) | `bpP:p5:torus-conv` | PASS | Choice from output witness, not an added hypothesis. |
| `kset` (853) | `bpP:p5:kset` | PASS | Source formula/carrier; no changed norm or global instance. |
| `rawUnion` (857) | `bpP:p5:kset` | PASS | Source formula/carrier; no changed norm or global instance. |
| `outputRepresentative` (861) | `bpP:p5:cell-transfer` | PASS | Source formula/carrier; no changed norm or global instance. |
| `cell_transfer` (865) | `bpP:p5:cell-transfer` | PASS | Output cell; mixed-lattice counting; whole unions by definition. |
| `kamMeasureConstant` (872) | `bpP:p3:two-scale-kam / p5:budget` | PASS | Source formula/carrier; no changed norm or global instance. |
| `budget` (874) | `bpP:p5:budget` | FAIL | F5: explicit graph constant omitted |
| `pgBudget` (880) | `bpP:p5:budget` | FAIL | F5: arbitrary selected bound |
| `pgLoss` (883) | `bpP:p5:lower` | PASS | Exact printed sum, once its component contracts are repaired. |
| `lower` (887) | `bpP:p5:lower` | PASS | Matches source role; no additional defect found. |
| `finalRadius` (892) | `bpP:p5:rstar / final shrink` | PASS | Source formula/carrier; no changed norm or global instance. |
| `strictness` (895) | `bpP:p5:strictness` | PASS | Whole-torus deletion; added finalRadius is explicit source smallness. |
| `frequency_bounds` (903) | `bpP:p5:torus-conv / frequencies` | PASS | Matches source role; no additional defect found. |
| `main` (909) | `bpP:p5:main` | PASS | Exact frozen telescope, conclusion and quantifier order. |

## Consumer, frozen-object, definition and package verdicts

**Consumers: conditional, not cleared for dispatch.** Direct `bpP:p4:`/`bpP:p5:` searches in I and N blueprints find no consumer occurrences. P3b:208–215 consumes the frequency/threshold dictionary and measure input; the matching `resonanceBad_eq`, actual unrescaled frequency, tau=n+1 and `mu^(tau−n)/lambda` are retained. P1's forward references are descriptive. Parts 4–5 consume one another through the collar, analytic bounds, KAM hypotheses, family, budget and strictness contracts; F1–F6 identify the lost pieces. The brief's `Nref{bpN:p3:` search returns 60 occurrences across I/P, but concerns a different upstream layer, not evidence of additional P45 consumers. N Parts 7/11/12 do not acquire P45 dependencies from that template instruction. P2/P3 applications require N1 reconciliation before proof dispatch.

**Frozen objects: PASS.** Read `HasFastDiffeomorphism`, `HasSecularBirkhoffForm`, `IsCylinderTorus`, `IsCylinderKolmogorovSet`, `DegenerateHamiltonian`, `Cylinder`, `CylinderCell`, `SecularAverage`, `OscillatorAction`, and their imported coordinate/field definitions. `PGData` preserves the exact frozen inputs; complexAverage_real and complexFrequency_real are proved bridge obligations, not assumed equalities. The family uses actual IsCylinderTorus for the actual degenerateHamiltonian. No parallel solution predicate or conclusion-shaped input replaces a frozen result. `main` is byte-identical to the frozen telescope and conclusion with the declaration name replaced (edge whitespace ignored). No suspected frozen defect was found, and no frozen file was changed.

**Definitions/structures: FAIL only at the deficient specification F3/F4 and constant selection F5.** The raw coordinate, total map and scalar definitions otherwise have their intended constrained uses. Arbitrary frozen coefficient values outside V are not used as analytic boundary data. The extension and family specifications are outputs of existence lemmas, so their proof-bearing fields are not illicit source assumptions. Pi/Prod max norms are retained; integer Fourier indices remain `Fin n → ℤ`. No global function/matrix instance is introduced. Complex polar powers are used only on positive-real-part action tubes; the real bridge explicitly assumes positive slow actions. No proof step relies on an uncontrolled off-domain inverse value.

**Packages: PASS WITH NOTES for the dependency plan, subject to F3/F4 and N1/N2.** The proposed split stays below 1,500 lines per Lean file, avoids witness-selection cycles, and quarantines the provider. The 1,521-line Markdown design is not a violation of the Lean cap. The 944-line signature fixture is design evidence, not authorized production sorry code. P5-CUT's actual parameter-measure construction must stay downstream of Family; its standalone finite-measure continuity lemma can remain early as planned. The twelve SOURCE_GAPs remain unpaid until supplying proofs and graph edges land; the design correctly does not claim proof closure from their signatures.

## Independent checks and outputs

All Lean invocations issued by this audit were sequential, used `LEAN_NUM_THREADS=1`, `nice -n 5`, and the existing signature gate. No build, clean, update, cache download, resource override, state-changing git operation, production Lean edit or shared-signature edit was performed. The user-authorized scratch signature copy was refreshed; API probes were under `.lake/abi-scratch/` and removed after checking.

1. `git diff inp...HEAD --stat` and `--numstat`: only `docs/tracks/P/design/P45-LEAN-DESIGN.md`, 1,521 insertions. Initial `git status --short`: empty.
2. Exact Appendix A/shared-signature comparison: **True**. Frozen `main` comparison with only theorem-name substitution: **True**. Signature length: **944**; **57** theorem declarations; **143** explicit declarations in total.
3. `/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p45 .drafts/scratch/P45Signatures.lean`: **exit 0**, exactly **57** `warning: declaration uses sorry` diagnostics, no errors or other warnings. The gate invokes `LEAN_NUM_THREADS=1 nice -n 5 lake env lean <absolute scratch path>` against the existing shared inp build. Run once, no rebuild.
4. API probe: same gate on `.lake/abi-scratch/P45AuditAPIs.lean`: **exit 0**, all **20** `#check`s resolved. Examined the actual types, including compact parametric integration (joint derivative continuity required), sup-to-weighted (positive geometric width and loss required), same-dimensional Lipschitz image measure, block inversion (Invertible instances required), monotone finite-measure limits, and mixed derivative symmetry (ContDiffAt to all finite orders required). These APIs do not prove their P45 specialization automatically. A supplemental serial probe on `.lake/abi-scratch/P45AuditExtraAPIs.lean` also exited **0** for `HasFDerivAt.comp` and `KAM.Weighted.sup_le_wbound`, with no warnings. P1/P7 draft names were checked against their defining files. Both API probe files were deleted.
5. `PATH=/root/code/KAM-inp-design-p45/.drafts/scratch/gated-bin:$PATH LEAN_NUM_THREADS=1 scripts/lint_sources.sh`: **exit 0**. Exact terminal summaries: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`. The pre-existing wrapper routes the ABI Lean call through the same gate.
6. `#print axioms KAM.Planetary.main`: **[propext, sorryAx, Classical.choice, Quot.sound]**. This is the submitted design stub's axiom list, not a proved provider receipt. No targeted module build applies to a report-only change; the specified signature elaboration is the targeted Lean check.
7. Final report validation: **143/143** declaration rows; fenced blocks balanced; `git diff --check` and `git diff --no-index --check /dev/null docs/tracks/P/design/DESIGN-P45-design-audit-1.md` both **exit 0**. Final `git status --short` lists only the requested untracked report; no tracked file changed. Temporary logs are `/tmp/p45-audit-{signatures,apis,extra-apis,lint}.log`; no designer receipt substitutes for these independent reruns.

**Uncertainties and errata.** F4 is a local blueprint/specification domain omission, not a verified CP10/CP11 erratum. The design's inherited allegations about CP10 covering-number uniformity, rescaled resonances, arbitrary-domain collars, shell exponent and uniform fifth-order remainder, and CP11 strict upper measure were not independently checked against pinned PDFs in this design audit. They remain allegations; no paper correction is certified here. The supplied jet/Schwarz and torus-deletion routes are explicit new work. The audit introduces no mathematical deviation or frozen-statement change. The corrected constants in F5 require declaring the enclosing-radius enlargement and updating the relevant design/graph contract consistently.
