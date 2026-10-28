# Independent audit of the Parts 12–13 Lean design

Overall verdict: **FAIL**. One source-facing signature weakens the explicitly fixed physical pair constants (F1). The frozen root/provider signatures themselves match. The other 23 theorem signatures pass at design level, subject to the documented upstream delivery gates. This report does not certify proofs, upstream mathematical gaps, or permission to seal an anchor.

Audit date: 2026-10-28. Scope: the supplied audit brief, `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the designer handoff, the complete design and signature appendix, both assigned blueprints and graph packets, the relevant frozen definitions/theorems, and the named upstream interfaces. Focused tier-2, refute-first review. Only this report is a persistent new audit artifact; the explicitly authorized signature copy is byte-identical, and temporary probes are removed. No git mutation, implementation repair, frozen-file edit, or new build target was authorized or performed.

## Frozen inputs and method

The design worktree HEAD was `8178e2dc6ba6d3653323edbf2cd072d336e0486c`. The comparison `git diff inp...HEAD` contains only the 729-line design document. The merge base is `081967912d5200ad4711d6d16abde6a8cfafea71`; the read-only `inp` ref observed during this audit was `90cb224ec5c0651eb8ad9009c11dae256607bb02`.

| Input | SHA256 |
|---|---|
| `docs/tracks/P/design/P1213-LEAN-DESIGN.md` | `ee32f7f2731eda553fafb4f5c9a9b31dbf60005ccac0770b8dc58ff0d3b04a18` |
| `/root/code/KAM-inp/.drafts/design/P1213Signatures.lean` | `83c26d562e951b5aee941703518bd879dfcfcf63cb0757a3fecf0229a53ce128` |
| `blueprint-P/parts/p12-planar-assembly.tex` | `83eee5fc9d881bf115be39e811ffc58cc206d45355d7956599115c9c7e0965db` |
| `blueprint-P/parts/p13-fixed-assembly.tex` | `8b208fe0799dec36bf3ff95b51a08bda6d2ca705491e045fe7d3c150838bb9e5` |
| `docs/graph/P/packets/P-p12.nodes.md` | `1f77f2b9d213338c39e947a8a64abc77ef224a577b951f9c95b77c4055a7a7ee` |
| `docs/graph/P/packets/P-p13.nodes.md` | `36b9cf0d3c6141d3ebd2aa9cf59035e94b5eb71ee8a3ab879fb5b17b20feefb4` |
| `manifest/frozen-anchors.json` | `5d8d31f1cc70c3cc67375ab28562e4fd4280215c7455dd329004c4dcd7a2f6fa` |
| `/root/code/KAM-inp/.drafts/design/PPart1Signatures.lean` | `78f21690c9e2623e9d9a9b6087bf32d1477434618c3089d98d0d0b99d5d098f7` |
| `/root/code/KAM-inp/.drafts/design/KeplerSignaturesP.lean` | `d9903304231afac0841cf0456d90c3dec04b2eb9e1a9752a9d4f9f9b7164d9c8` |

Line references below refer to these snapshots. The appendix equals the supplied signatures byte for byte: 381 lines, 24 theorem bodies `:= sorry`, and 13 definitions, including five explicitly temporary upstream copies. All 89 local packet nodes occur exactly once in the design table, with their exact statement and proof locators. Node coverage establishes inventory coverage, not theorem fidelity or proof closure.

I compared premises, carrier/normalization choices, witness order, constants, and the actual frozen predicate bodies; then traced producer clauses through the stated consumers. Suspected failures were reconsidered against the frozen root contract, the explicitly split source claims, and upstream bridges before classification. No subagents were used. No pinned-paper claim is being independently certified: the assignment's immediate mathematical authority is the pinned local blueprint and its explicit corrections.

## Findings

### F1 — Medium, blocking signature fidelity: `FixedAssembly.n_general` forgets the canonical pair constants

**Evidence.** `blueprint-P/parts/p13-fixed-assembly.tex:135–144`, label `bpP:p13:n-general`, states: “with ζ*, d, D of Definition ... tube-constants there is ε₀>0”. Its constants step says the same constants “depend on (a,η) only”. The defining source, `blueprint-P/parts/p6-newtonian-models.tex:210–214`, fixes

```text
d = gamma_a / 2
D = 2 * a_max + gamma_a
```

The exact existing definitions are `tubeD (axisGap a)` and `tubeBigD (axisGap a) (axisMax a)`; in fact neither depends on η. The designed helper instead concludes

```lean
∃ eps0 d D : ℝ, 0 < eps0 ∧ 0 < d ∧ d < D ∧
  ∀ eps : ℝ, 0 < eps → eps < eps0 →
    ∃ S : Set (Phase (n * 2)), 0 < volume S ∧ volume S < ⊤ ∧
      FixedKolmogorovSet G m0 m a eps eta d D S
```

at signatures lines 324–332 and design lines 671–679. Thus its pair constants may depend on G, m₀, m and η, and need not equal the claimed constants. The graph packet's `bpP:p13:n-general` explicitly records `CONSTANT_SCOPE: d,D depend on a alone; zeta_* on (a,eta); eps_0 on the fixed data; S on eps as well`. Both this node and `stepP:p13:ng-const` claim the canonical constants, not merely some positive bounds.

**Adversarial refutation.** The strongest defense is that this is exactly the frozen P-FIXED telescope and is sufficient for `FixedAssembly.fixed`. I checked that transcription: it is exact. That defense establishes downstream root applicability, but does not restore the stronger source helper statement. Frozen files need no change: an internal helper may preserve the canonical constants and its consumer can existentially package them. The design itself promises canonical d,D in its construction and general assembly prose. Merely choosing them in a future proof of the weaker signature does not export that assertion. For example, from valid canonical bounds one could export the looser bounds `d/(1+G)` and `D+G`; the current type cannot distinguish that output. The audit brief explicitly fails constants with wider dependence or weakened conclusions. **Finding survived refutation.** This is an interface-fidelity defect, not a counterexample to planetary KAM.

**Proposed fix.** Replace only this helper's signature by the following, in the existing signature-file context. Keep `fixed` and both provider telescopes unchanged. Update the general-branch assembly prose to explicitly repackage the displayed d,D as the frozen root's existential witnesses.

```lean
namespace KAM.Planetary.FixedAssembly

theorem n_general {n : ℕ} (hn : 2 ≤ n)
    (G m0 : ℝ) (m a : Fin n → ℝ)
    (hG : 0 < G) (hm0 : 0 < m0) (hm : ∀ i, 0 < m i)
    (ha : ∀ i, 0 < a i) (hsep : ∀ i j, i < j → a i < a j)
    (eta : ℝ) (heta : 0 < eta) :
    let d := tubeD (axisGap a)
    let D := tubeBigD (axisGap a) (axisMax a)
    ∃ eps0 : ℝ, 0 < eps0 ∧ 0 < d ∧ d < D ∧
      ∀ eps : ℝ, 0 < eps → eps < eps0 →
        ∃ S : Set (Phase (n * 2)), 0 < volume S ∧ volume S < ⊤ ∧
          FixedKolmogorovSet G m0 m a eps eta d D S := sorry

end KAM.Planetary.FixedAssembly
```

This adds no hypothesis and uses the existing literal tube definitions. It keeps the source's threshold-before-coupling order. The displayed body is a design placeholder only, not an implementation instruction to introduce a non-frozen sorry. No proposed repair was applied to the signature file.

### N1 — Medium, nonblocking design gate: upstream jet/chart identities need their own exact certificates

The design at lines 50–61 and 170–172 correctly retains the “actual” Part 8/11b objects and the dictionary `P0mov=C0+δS`, `P0fix=C0`, `Ω=2σ`, `β=beta-hat`. The joint `pg_hypotheses` outputs are assembly interfaces: they certify a common tuple satisfying P-G and chart clauses, but do not themselves expose these canonical jet equalities, the source axis cube, or a common moving/fixed witness. In particular, two separate existence results do not identify their witnesses.

**Proposed disposition:** retain the stated reconciliation gate at design line 301. Before assigning P12-C/P13-A, bind the upstream names and exact characterization conclusions in their briefs; retain the actual jet dictionary and common Birkhoff map in upstream exports or separate local characterization lemmas. Treat the joint outputs as projections used by these root assemblies, not standalone certificates of every finer source definition. This is not a new failure of the frozen roots: those consumers require the respective constructed tuple, and the design already assigns the finer source claims upstream rather than assuming them as root premises.

### N2 — Medium, nonblocking design gate: source gaps and designed dependencies remain unavailable

The design's complete 34-record disposition table matches the groups in `/root/code/KAM-inp/docs/graph/P/reviews/GLOBAL-review.md`. Zero local packet `SOURCE_GAP` notes does not mean zero transitive gaps. P-G sealing, P6-5/P7-6 delivery, the actual jet dictionary, the analytic eigenframe, nonlinear real-flow existence/uniform data, and real-versus-holomorphic Lie/Taylor/symplectic applicability remain proof gates. The general route additionally requires the Part 11 wrapper with the actual K1–K6 chain.

**Proposed disposition:** preserve these gates in each package brief and require delivery/proof audits before importing an upstream result. In particular do not substitute the N holomorphic theorem merely because a real generator is analytic, or import an unsealed P-G/provider. The current design explicitly forbids both shortcuts; this note records their continuing force.

### N3 — Low, implementation detail: make two implicit proof choices explicit in package briefs

The real-power route at design line 168 is valid: `ContDiffAt.rpow_const_of_ne` followed by `.analyticAt` requires the analytic differentiability order (`ω`), not merely `C¹` or `C∞`. The independent probe verified the composition at the required order. Also the generic `measure` theorem does not assume measurability of V. Its proof should obtain Borelness using `S ⊆ cylinder V r` to rewrite `S ∩ cylinderCell V r` as S intersected with the fast-angle half-open bounds; it cannot assume a general V is Borel.

**Proposed fix:** state these two proof instructions in P12-B and P12-D briefs. Neither requires a signature change.

## Signature-by-signature ledger

Prefixes: `PA = KAM.Planetary.PlanarAssembly`, `FA = KAM.Planetary.FixedAssembly`, `PR = KAM.Provider.Planetary`. Blueprint entries abbreviate only the repeated prefix `bpP:`. PASS means design-level correspondence, including explicitly assigned bridges; it does not mean a theorem is proved. All signatures use the actual frozen predicates.

| Lean name (signature lines) | Blueprint label / exact role | Verdict | Reason |
|---|---|---|---|
| `PA.compact_cell_isCompact` (65) | `stepP:p12:ft-cpt` | PASS | Compactness of the literal finite-coordinate cell; arbitrary δ is safe (negative δ gives the empty set). |
| `PA.forward_tube` (69) | `p12:forward-tube` | PASS | Same max norm, δ upper bounds, product-domain conclusion, pointwise circular comparison and tube inclusion; physical positivity and δ-before-w quantifiers retained. Axis separation/η are unused standing data, safely dropped. |
| `PA.collar` (82) | `p12:collar` | PASS | Full two-sided frontier collar; `4(L₀+L₁)t`, sup distance, and both strict half-width conditions retained. |
| `PA.product_chart` (90) | `p7:product-chart` (b), locally owned completion | PASS | Literal hProd restriction; positive-action analyticity, fast frequency, diagonal and cross Hessian entries and decoupling match. κ>0 subsumes the product Gm₀. |
| `PA.fast_diffeo` (106) | `p12:fast-diffeo` | PASS | Exact frozen smooth-inverse predicate; positive κ/masses/endpoints suffice. Frequency identification is exported by `product_chart`; explicit cube-root inverse is the assigned construction. |
| `PA.radius_choices` (115) | `p12:data` D8–D9; `p12:quantifiers`; `p13:data#choices` | PASS | Explicit min formulas, strict r<rG<1, `2r²≤δ/2`, positive threshold≤1 and strict coupling bound; no coupling-dependent choice. |
| `PA.birkhoff_mono_radius` (123) | `stepP:p12:pg-h4`, `stepP:p13:pg-h4` | PASS | Restricts both integrability discs and little-o domain in the actual frozen predicate; r>0 and r≤r₀ suffice. |
| `PA.chart_of_birkhoff` (133) | `stepP:p12:ch-chart` | PASS | Conditional composition tool, distinctly named; existing real analytic and symplectic maps with image guard. Analyticity supplies both differentiability premises of `IsSymplecticOn.comp`. |
| `PA.chart_hamiltonian_of_preserves_fast` (141) | `stepP:p12:ch-ham` | PASS | Exact moving Hamiltonian and degenerateHamiltonian identity on guarded chart domain; genuine fast-action preservation input; arbitrary real μ is legitimate. |
| `PA.pg_hypotheses` (151) | `p12:data`, `p12:chart`, `p12:pg-hypotheses` | PASS | Joint assembly output contains every P-G input and required chart/tube clause before μ; no result bundle is assumed. Finer canonical source identities remain explicitly upstream (N1). |
| `PA.transport` (191) | `p12:transport`, reused at `p13:transport` | PASS | Direct fast-lattice theorem with actual local hypotheses; actual cylinder and physical torus predicates, same frequency/time, full range image. a,b generalization is valid. |
| `PA.cylinder_set_shift` (204) | `stepP:p12:me-inv` | PASS | Whole-torus union plus frozen fast winding supplies invariance, without a slow-position lattice. |
| `PA.measure` (210) | `p12:measure`, `stepP:p13:tr-meas` | PASS | Fast-cell image equality, cell injectivity, Borel image and exact volume equality; S⊆O supplied at both consumers. See N3 for arbitrary V. |
| `PA.measure_in_tube` (223) | `p12:measure`, `p13:transport` measure clause | PASS | Explicitly conditional local tool combines cell positivity and equality with tube inclusion and finite tube volume. No unnecessary mass/radius sign premise. |
| `PA.planar` (234) | `p12:planar`, frozen `p0:planar` | PASS | Byte-exact frozen telescope after theorem renaming, including all-time physical predicate, positive finite volume and threshold-first order. |
| `FA.fixed_hamiltonian_form` (252) | `p13:fixed-hamiltonian-form` (a) identity | PASS | Exact existing product identity; accompanying analyticity reused from Product, parts (b)/(c) assigned across difference, upstream identification/BNF and joint construction. n=0 extension is an empty finite-sum identity. |
| `FA.perturbation_difference` (259) | `p13:fixed-hamiltonian-form` (b), `stepP:p13:fh-id` direct difference | PASS | Literal fMov−fFix algebra, including `(2*m₀)` denominator; arbitrary T and zero/nonpositive parameters are safe for this total algebraic identity. Averaged/jet claims remain upstream. |
| `FA.chart_of_preserves_fast` (266) | `p13:chart`, `stepP:p13:ch-ham` | PASS | Correct fixed perturbation, same fast-preservation guard and arbitrary real ε. |
| `FA.pg_hypotheses` (275) | `p13:data`, `p13:chart`, `p13:pg-hypotheses` | PASS | Fresh full P-G input tuple for fFix; shared geometry need not imply equal P-G thresholds. Same upstream characterization boundary as N1. |
| `FA.n2` (314) | `p13:n2` | PASS | Exact two-planet frozen conclusion with fixed Hamiltonian, original physical premises and strict coupling order. |
| `FA.n_general` (324) | `p13:n-general` | **FAIL** | F1: existential arbitrary d,D replace explicitly specified canonical tube constants, widening their dependence. |
| `FA.fixed` (335) | `p13:fixed`, frozen `p0:fixed` | PASS | Exact frozen telescope. Both branches can supply it; F1 repair only requires repackaging canonical witnesses in this proof. |
| `PR.planarTwoPlanetKAM` (352) | frozen `p0:planar`, `p12:planar` | PASS | Exact registered provider signature, no extra premise or parallel dynamics predicate. |
| `PR.fixedSunPlanetaryKAM` (362) | frozen `p0:fixed`, `p13:fixed` | PASS | Exact registered provider signature, implicit dimension and ordered-axis binders preserved. |

Definitions/prelude inventory (all 13 `def` commands):

| Lean name | Source object / body | Verdict |
|---|---|---|
| `KAM.Planetary.axisMax` | Part 6 maximum, literal existing `⨆ i, a i` | PASS, scratch copy only |
| `KAM.Planetary.axisGap` | Part 6 minimum of axes and distinct-axis gaps | PASS, scratch copy only |
| `KAM.Planetary.tubeRadius` | `min η (γ/6)` | PASS, scratch copy only |
| `KAM.Planetary.tubeD` | `γ/2` | PASS, scratch copy only |
| `KAM.Planetary.tubeBigD` | `2*A+γ` | PASS, scratch copy only |
| `PA.kepler_h` | `p7:product-def`, hProd at assembled zero fast-angle/slow coordinates | PASS |
| `PA.action_center` | `p12:sec-set#data`, `mᵢ*sqrt(G*m₀*aᵢ)` | PASS |
| `PA.total_chart` | `p12:perturbation`, existing total product chart composed with supplied T | PASS |
| `PA.perturbation` | `p12:perturbation`, constant coupling family of actual fMov through total_chart | PASS |
| `PA.compact_cell` | `stepP:p12:ft-cpt`, closed fast cell, action box and Γ bounds | PASS |
| `PA.secular_radius` | `p12:data` D8, `min rG (sqrt(δ/2))/2` | PASS |
| `PA.coupling_threshold` | `p12:data` D9, `min 1 (r^6/log(1/r)^c)` | PASS |
| `FA.perturbation` | `p13:data` D6, constant coupling family of actual fFix through total_chart | PASS |

No new structure or global function/matrix instance occurs. The five prelude copies agree with `KAM/Planetary/Newtonian/Tube.lean`; implementation must import their owner rather than redeclare them. New total compositions use existing total functions. Blueprint Part 12 lines 81–89 explicitly allows arbitrary irrelevant values outside the guarded source locus; its displayed zero extension is not used to derive any unguarded theorem here. The new definitions contain no choice, fallback branch or new hidden dynamics. Zero/nonpositive parameter values in literal auxiliary formulas are not used to infer their positive-domain analytic claims.

## Consumer, frozen-object and package verdicts

**Consumers: PASS for frozen-root applicability; FAIL for the exact `n_general` source contract (F1).** The relevant downstream uses are Part 12's local construction/transport/physical assembly, Part 13's reuse and dimensional split, and the two Part 0 roots. Searching I/N/P references located no separate I/N consumer of these Part 12–13 signatures. The audit brief's generic `bpN:p3:` searches were also checked: these are ODE-layer references elsewhere, not new inputs to these two assembly signatures. No direct such reference occurs in Parts 12–13, nor a Part 12/13 consumer in N Parts 7/11/12.

The actual composition checks are:

1. Both joint outputs supply V open/connected/bounded, W open with closure inclusion, the full collar, r₀>0, μ₀=1, B>0, H₀/P/P₀/Ω/β and all six frozen P-G hypotheses. The literal a=b=2 supplies its positive dimensions. No H1–H6 premise is moved to a frozen root.
2. P-G supplies rG<r₀, rG<1, C,c>0, a cylinder Kolmogorov set and explicitly positive cell volume. `radius_choices` supplies all strict r/μ restrictions. Its fixed r is selected before introducing μ or ε.
3. Closure-cylinder inclusion gives S⊆O; lattice invariance/equality clauses match the direct transport and measure signatures. For each point the actual frozen cylinder-set predicate gives an entire torus inside S. The physical predicate follows with the same Diophantine exponent since τ>a+b implies τ>(a+b)−1. No frequency rescaling or invalid exponent lowering is needed.
4. At a=b=2, both phase expressions reduce to `Phase 4`. In general dimension, the wrapper is already on `Phase (n*2)`. The plan uses dependent substitution in the n=2 branch; it does not equate symbolic `Fin (n+n)` and `Fin (n*2)` by reflexivity.
5. The exact P6-5 signatures `movingKolmogorovSet_of_tube` and `fixedKolmogorovSet_of_tube` accept the measurable physical image, canonical tube inclusion and pointwise whole physical tori. The moving variant additionally needs μ≥0, supplied by root μ>0; the fixed variant has arbitrary-real-ε scope. Both produce the actual frozen physical solution and pair-bound clauses. The Part 11 wrapper's source at p11 lines 237–244 supplies exactly the threshold-first Borel set/tube/whole-torus data needed by the general route, with point-dependent frequencies.

**Frozen objects: PASS.** Read and compared the actual `IsCylinderTorus`, `IsCylinderKolmogorovSet`, `IsPhysicalTorus`, `HasFastDiffeomorphism`, `HasSecularBirkhoffForm`, `MovingKolmogorovSet`, `FixedKolmogorovSet`, `IsNewtonSolution`, `IsFixedSolution`, `cylinder`, `cylinderCell`, `fastShift`, `fastFrequency`, `degenerateHamiltonian`, `circularTube`, `hamiltonianVectorField`, and `symplecticForm`, together with the frozen theorem telescopes. The remainder uses the frozen Pi/Prod max norm and oscillator discs, quartic factor 1/2 and literal angle average. The Hamiltonian field/sign conventions and all-real-time `HasDerivAt` clauses are retained. There is no competing solution predicate. Production modules do not import providers or draft anchors; P-G consumption is explicitly gated on sealing.

For the two providers, the binders classify as typing data (dimension, real/function carriers), original physical source data/premises (n≥2 where applicable, G,m₀,m,a, positivity, axis order, η>0), and no additional result hypothesis: **EXCESS = 0**. Threshold, d,D precede the later coupling and S follows it. The four assembly root-shaped transcriptions match their respective frozen telescopes mechanically, with the documented μ→ε/fixed-predicate substitution for n2. This exact match is why F1 is local to the stronger helper-source claim rather than a frozen-anchor defect.

**Definitions: PASS for the declared literal formulas and the explicitly scoped scratch prelude.** No characterized-object construction or uniqueness-based choice is introduced. Upstream source-defined spectral/jet objects are not recertified by a bare existential projection (N1).

**Packages: PASS for dependency order and size planning; F1 must be corrected before P13-C assignment.** P12-A/D at wave 1, B at 2, C at 3, E/P13-A at 4, P13-B at 5, and P13-C at 6 form an acyclic order once named upstream gates deliver. Geometry owns h/action/cell definitions; Data owns total_chart and each perturbation; Measure/Transport are separate modules and terminal providers have no production consumers. Each package estimate is 150–800 lines and each proposed file below 1500; splitting at about 1100 is explicit. These are estimates, not measured proof sizes. There is no new implementation module to build during this Markdown-only audit.

## Verification and limitations

The original signatures were copied to `.drafts/scratch/P1213Signatures.lean`, with the original left untouched, and elaborated **once** using:

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh \
  /root/code/KAM-inp-design-p1213 .drafts/scratch/P1213Signatures.lean
```

The existing shared gate runs `LEAN_NUM_THREADS=1 nice -n 5 timeout 1800 lake env lean <absolute file>` against `/root/code/KAM-inp`'s shared build. Exit 0: exactly 24 `declaration uses sorry` warnings, no errors or other warnings. Only one audit-owned elaboration/lint process was submitted at a time; the gate is shared with other workers and its slots are not an assertion of global machine exclusivity. No heartbeat, recursion-depth or synthesis-budget override was used.

All six printed declarations (`PA.planar`, `FA.n2`, `FA.n_general`, `FA.fixed` and both providers) reported exactly:

```text
[propext, sorryAx, Classical.choice, Quot.sound]
```

These are design stubs with an explicit proof hole, not proof or axiom closure.

An independent temporary `.lake/abi-scratch/P1213AuditProbe.lean` imported Mathlib, checked `IsCompact.uniformContinuousOn_of_continuous`, `MeasurableSet.image_of_continuousOn_injOn`, `ContDiffAt.rpow_const_of_ne`, `ContDiffAt.analyticAt`, `Real.volume_Ioo`, `Real.volume_Icc`, and `MeasureTheory.Measure.pi_pi`, and elaborated the actual no-sorry composition

```lean
example (x p : ℝ) (hx : x ≠ 0) :
    AnalyticAt ℝ (fun y : ℝ => y ^ p) x :=
  (contDiffAt_id.rpow_const_of_ne (p := p) hx).analyticAt
```

The same gated invocation exited 0 with no warnings. The printed Borel-image theorem requires a Polish/Borel domain and Hausdorff target with measurable opens; the finite real Pi/Prod spaces here satisfy those assumptions. Project declarations claimed delivered were checked directly in owning source; designed Part 1/P6/P7 interfaces were compared with their supplied signature files, not represented as proved imports.

Source lint ran once after the Mathlib probe, with the designer's existing local lake shim so that its ABI elaboration used the shared gate:

```text
PATH="$PWD/.drafts/scratch/gated-bin:$PATH" LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
exit 0
check_lean_modules: PASS (412 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The additional lint stages emitted no failure. `git diff --check` exited 0. Since the report is a new untracked file, its contents were separately checked for control characters, whitespace, table inventory and balanced fences. No project or Mathlib rebuild, cache operation, clean, source modification, or theorem sealing is part of this audit. The F1 replacement is a proposed signature, not a proved theorem. An additional isolated probe of that replacement and its existential packaging was queued after lint; it was cancelled while still waiting for the shared gate (exit 143, no Lean invocation or diagnostics). Thus the replacement itself has not been independently elaborated. The submitted signature file and Mathlib probe did complete as recorded above; no passing result is inferred from the cancelled optional check. No new pinned-paper erratum, frozen-definition defect or authorized semantic change is asserted.

## Closeout

All 24 theorem signatures and 13 definitions are classified. One blocking fidelity finding, F1; three numbered implementation/source-gate notes. Correction and fresh independent review of F1 are required for design acceptance. The unmodified frozen root types can remain as they are. All upstream proof and sealing gates remain open until separately discharged.
