# P11B independent design audit 1

**Overall verdict: FAIL.** Two material signature/interface findings, F1 and F2, must be repaired before this exact surface is assigned to provers. Neither finding asserts that the intended KAM theorem is false. The signature check passes; mathematical/source fidelity does not follow from that check.

Date: 2026-10-28. Scope: a tier-2, refute-first audit of the P11B design and its 133 explicit declarations (28 theorem signatures, 105 definitions/abbreviations/structures), including the fields of the result structures. The 119 graph-node rows are a separate coverage inventory, not 119 proved results.

## Inputs and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-design.md`, and `.drafts/handoff-DESIGN-P11B.md`. The user authorized only this report, the explicitly requested scratch copy, and temporary probes. No source repair, git mutation, provider work, or frozen change is authorized or performed.

Frozen audit snapshot V1:

| Input | Revision / SHA256 |
|---|---|
| Worktree HEAD | `323c9214987b70b32939191a489fc417c9ebf5f3` |
| Compared `inp` | `31315a8b040b2ecefe792c4e03f9b30bfc72799c` |
| `docs/tracks/P/design/P11B-LEAN-DESIGN.md` | `64300c55c498e1924097773d63dc44a44b972af81780d5a1bb840a95d60e053f` |
| S = `/root/code/KAM-inp/.drafts/design/P11BSignatures.lean` | `d44e019cd741c2015a2534d1b20dd2f8b22905ca4d8e2f2a6b51ac8394ebc0df` |
| `blueprint-P/parts/p11a3-iteration-selection.tex` | `90251ed2045353dd2c9574b5f2c53588eb5762ea9dbc86ed9075c00bf8d9ad1c` |
| `blueprint-P/parts/p11a4-limit-family.tex` | `c88030106491131ffde29078d1f0919ae092592bf37e1bbc68a87ab087369b2b` |
| `/root/code/KAM-inp/docs/graph/P/packets/P-p11a3.nodes.md` | `deb0a6515ee39460357d692771f73ca27d4bc83ba4fe43039910183e8a445b08` |
| `/root/code/KAM-inp/docs/graph/P/packets/P-p11a45.nodes.md` | `555a803096ee7c19d46afb01bfdf660d35bac0abe7320c6609bc95fa55ae0aed` |
| Adjacent `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` (interface inspection only) | `40f6b495348ae7b10bf06bf8837bba7433b1bb648f98d17602eb780904690983` |

`git diff inp...HEAD` changes only the 1273-line design document. Appendix A is byte-identical to S (927 lines). The two blueprint hashes agree with the designer's stated source snapshot. The live graph packet inventory has exactly the same 119 relevant unique nodes as the design table, with no missing or extra node. Locators below refer to V1; `S:L` denotes the signature file line.

Acceptance criteria were the brief's seven checks: faithful declarations, usable consumer contracts, frozen-object identity, honest definitions/records, existing named APIs, an acyclic bounded package plan, and one successful signature elaboration. Discovery and refutation were separate passes. The examples below test the proposed defenses to the findings; no draft proof body was audited as a proof.

## Findings and proposed corrections

### F1 — MAJOR — `finite_extension` adds a resonance-retention premise

**Anchors.** S:360–372 defines `SelectionFiniteChain` with

```lean
retained : ∀ j < ν, c.K (j + 1) = selectionRetained a d c j
```

S:376–380 then assumes `(hc : SelectionFiniteChain d a c ν)` for `finite_extension`. In contrast, `bpP:p11a:finite-extension`, p11a3:156–165, asks only for “K=K0 ⊃ K1 ⊃ ... ⊃ Knu nonempty compact” and holomorphic real increments bounded by ell_j. The graph record at `P-p11a3.nodes.md:663` has the same source premises and no shell-testing equation. The retained recursion first enters the later “Stage-nu data” paragraph and `retained-def` (p11a3:233–236).

The design's decision 6 calls this “the literal source-defined finite-chain premise of finite-divisor/finite-extension/finite-measure.” It is literal for the latter retained-chain lemmas, but stronger than the earlier extension lemma. An extension of arbitrary nested compact sets is being replaced by an extension only of resonance-retained sets.

**Refutation test, survived.** Nesting does not imply the extra equation. In dimension one take h(I)=I^2/2, K=[-1,1], mu=rho=1, tau=1, beta=1/2, M=C1=1, theta=strip=1, loss=1/2. These satisfy the standing data, with finite type supplied by the first derivative of omega(I)=I. Use the source gamma=gammaStar/2>0 and a schedule with T0=1, t0=1/2, and positive s0, epsilon0. Set K0=K1=K and Delta omega0=0. This satisfies the source extension premises at nu=1, and the extension is simply omega(I)=I. However k=1 is in shell zero and b=0 is excluded by the new retention test, which would require 2*gamma<=0 there. Thus K1=K is not the prescribed retained set and the source chain cannot supply `hc`. The fact that actual KAM chains do satisfy retention does not restore the source theorem's advertised domain.

**Fix.** Separate analytic nested-prefix data from resonance retention. Use the following replacement surface for the extension lemma; retain the current stronger predicate for `finite_divisor` and `finite_measure`. The block contains signatures, not supplied proofs.

```lean
structure SelectionExtensionChain (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) : Prop where
  initial : c.K 0 = d.K
  compact : ∀ j ≤ ν, IsCompact (c.K j)
  nonempty : ∀ j ≤ ν, (c.K j).Nonempty
  nested : ∀ j < ν, c.K (j + 1) ⊆ c.K j
  holomorphic : ∀ j < ν, DifferentiableOn ℂ (c.Δω j)
    (actionNbhd (c.K j) (selectiont a j))
  real : ∀ j < ν, ∀ b : SelectionR n,
    selectionReal b ∈ actionNbhd (c.K j) (selectiont a j) →
    c.Δω j (selectionReal b) = selectionReal (selectionRe (c.Δω j (selectionReal b)))
  bound : ∀ j < ν, ∀ b ∈ actionNbhd (c.K j) (selectiont a j),
    ‖c.Δω j b‖ ≤ selectionell a j

theorem finite_extension (d : SelectionData n) (a : SelectionSchedule n)
    (c : SelectionChain n) (ν : ℕ) (hc : SelectionExtensionChain d a c ν)
    (hμ : a.μ = d.μ) (ht : 0 < a.t₀) (ht1 : a.t₀ ≤ 1)
    (htθ : a.t₀ ≤ d.ϑ / Real.sqrt n) (hτ : 0 ≤ a.τ) :
    ∃ χ : ℕ → SelectionR n → ℝ, ∃ w : SelectionR n → SelectionR n,
      (∀ j < ν, ContDiff ℝ d.μ (χ j) ∧
        (∀ y, 0 ≤ χ j y ∧ χ j y ≤ 1) ∧ (∀ y ∈ c.K j, χ j y = 1) ∧
        tsupport (χ j) ⊆ {y | Metric.infDist y (c.K j) ≤ selectiont a j / 2}) ∧
      w = selectionExtendedFrequency d c χ ν ∧
      ContDiffOn ℝ d.μ w {y | selectionReal y ∈ actionNbhd d.K (2 * d.ϑ)} ∧
      (∀ b ∈ c.K ν, w b = selectionRe (selectionFrequency d c ν (selectionReal b))) ∧
      (ν = 0 → w = frequencyMap d.h) ∧
      ∀ j ≤ d.μ, ∀ y ∈ selectionThick d.K d.ϑ,
        selectionDGVector j (w - frequencyMap d.h) y ≤ selectionExtensionC n d.μ *
          ∑ i ∈ Finset.range ν, selectionell a i / selectiont a i ^ d.μ
```

The current retained chain should project to `SelectionExtensionChain`. This is a weakening of an added premise, not a frozen declaration change.

### F2 — MAJOR — the beta-uniform key fixes the entire Hamiltonian

**Anchors.** S:858–859:

```lean
def selectionFixedKey (d : SelectionData n) :=
  (d.μ, d.ρ, d.τ, d.ϑ, d.strip, d.C₁, d.M, d.loss, d.K, d.h)
```

S:865–879 chooses c, or cD and cstar, after an arbitrary `d₀ : SelectionData n`, then tests equality of this key. Equality therefore requires `d.h = d₀.h`. It does not express constancy of only the listed geometric/numerical data, including M0. The source `adm-budget-beta` (p11a3:402–410, graph record at `P-p11a3.nodes.md:2113`) fixes “K, theta, s, loss, M, M0, C1” before the coefficient. `displacement-power` (p11a4:180–186, graph record at `P-p11a45.nodes.md:1064`) uses the same list. The consuming p11a5:6 is explicit: “Only then is a Hamiltonian chosen”; p11a5:73–78 quantifies over every pair (h,f) satisfying those data. Part 11's KAM datum at p11:25–36 also contains bounds, not a chosen h.

**Consequence.** The delivered existential coefficients may depend on the complete function h, and the universal family is restricted to that one h. The statements do not export the promised Hamiltonian-independent constants for fixed numerical/geometric data. `SelectionData` containing h is acceptable for pointwise constructions; fixing that whole function in the uniformity key is the defect.

**Refutation test, survived.** Replacing h by h+1 changes the key but leaves omega, all its jets, actual M0, Hessian bound, finite-type amount, and every scalar threshold/displacement constant unchanged. The data permitted by the source are identical. The current equality premise cannot be supplied across even this elementary family. I checked the possible defense that `adm_budget` already gives wider uniformity: it does, and provides a route to repair cstar, but does not change the binders of `adm_budget_beta` or `displacement_power`. Likewise the explicit `gamma_inverse` and displacement formulas support a uniform cD repair; they do not justify claiming the existing key already says it.

**Fix.** Replace h in the key by the actual source M0, and retain the existing binder order. The following are complete replacement signatures for the three failing declarations. For the later Part-11 bounded-M0 interface, the monotone minorant remains P11a5's separate obligation.

```lean
def selectionFixedKey (d : SelectionData n) :=
  (d.μ, d.ρ, d.τ, d.ϑ, d.strip, d.C₁, d.M, d.loss, d.K, selectionM₀ d)

theorem adm_budget_beta (d₀ : SelectionData n) :
    ∃ c : ℝ, 0 < c ∧ ∀ d : SelectionData n,
      selectionFixedKey d = selectionFixedKey d₀ → d.β ≤ 1 →
      c * d.β ^ selectionBetaExponent d ≤ selectionAdmissible d

theorem displacement_power (d₀ : SelectionData n) :
    ∃ cD cstar : ℝ, 0 < cD ∧ 0 < cstar ∧ ∀ d : SelectionData n,
      selectionFixedKey d = selectionFixedKey d₀ → d.β ≤ 1 →
      cstar * d.β ^ selectionBetaExponent d ≤ selectionAdmissible d ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ selectionAdmissible d →
      ∀ f : SelectionPhaseC n → ℂ, SelectionPerturbation d f ε →
      ∃ o : SelectionEvaluationOutput d f ε,
        ∀ b ∈ o.Kinf, ∀ θ, ‖o.defect b θ‖ ≤
          cD * Real.sqrt ε * d.β ^ (-((d.μ : ℝ) + 1) / d.ρ)
```

No new premise on h is needed. `selectionCDelta d * selectionCGamma d` supplies the explicit cD; its data dependence is already visible in the formulas. Prove the uniform coefficient before varying h, beta, epsilon and f. The corrected signatures above are proposed report text and have not been installed or elaborated as replacements.

### N1 — NOTE — upstream reconciliation is a real release gate

The design correctly labels P11A interfaces as unimplemented/reconcilable inputs (design:174–198, 302–308). Inspection of the adjacent P11A signature draft confirms compatible Pi/Prod carriers, a vector-valued singleton encoding of scalar tensors, the full-collar `param_cauchy`, and an explicit reality guard in `canonical_step_real`. Supply actual bridges for scalar-vs-singleton tensors, `selectionThick`, the finite-type amount, domain/cutoff formulas, and frozen real/complex frequency identification. Do not mark these as discharged by the standalone P11B elaboration.

There is a specific domain difference to reconcile: P11B S:507–511 asks for `real_angle_derivative` at every real b in the complex collar, while adjacent P11A `canonical_step_real` (lines 605–618) returns its derivative bound for b in S.E. The whole-collar real generator and `real_lipschitz` offer a route to the stronger P11B clause, but the narrower P11A clause cannot be applied verbatim at an arbitrary real collar point. Add that local supplier or strengthen the upstream real clause before releasing B10. This is an acknowledged upstream/interface obligation, not evidence that the P11B torus theorem is false.

The named `chart_field` supplier is present in the delivered PP1-4 worktree source, with factor-one specialization available by its actual type, but its module is absent from `/root/code/KAM-inp` and its shared build at audit time. Its source type was inspected; it was not falsely counted among independently elaborated shared-build names. Land/build it through its own package before B16. No attempt was made to build that other package.

### N2 — NOTE — make recoverable source clauses explicit at release

Several clauses are consequences of the supplied output rather than separate exact exports. This is not a new hypothesis or an irrecoverable loss: `schedule_props`' final derivative-sum <=C1 follows from h2 and t0>0; `free_radius`' lambda<=lambdaMax follows from the balancing identity and hsmall; `finite_divisor`'s intermediate tail/shell inequalities follow from the same retained prefix; E4 follows at j=1 from `map_parameter_bound`.

O4 in the source gives separate A and alpha bounds for the two parameter-derivative blocks, whereas S:490–497 exposes a joint max(A,alpha) bound. Joint holomorphy and the separate block sup bounds also returned by `SelectionIteration` let one prove the source's sharper componentwise Cauchy bounds, without changing any standing premise. Add the explicit blockwise projection lemmas to B10 if that graph clause is to be advertised as an exact export; do not try to derive each smaller bound merely by projecting the max bound. The consumers inspected here use the joint bound or independent collar Cauchy estimates and are not blocked by this packaging choice.

## Per-declaration ledger

PASS means the declaration's intended mathematical surface is compatible with its source and stated consumers, subject to the explicitly named upstream proof/bridge obligations. It does not mean its body is proved. Structure rows include field review; local supplier labels are identified explicitly. Short labels in this table expand to `bpP:p11a:*`, with `step:*` expanding to `stepP:p11a:*`.

| Lean name (KAM.Planetary.) | Blueprint label (bpP:p11a: unless noted) | Verdict | Reason |
|---|---|---|---|
| `SelectionR` (S:38) | `sel-data; domain-def` | **PASS** | Pi/Prod max-norm carriers; real inclusion/restriction. |
| `SelectionC` (S:39) | `sel-data; domain-def` | **PASS** | Pi/Prod max-norm carriers; real inclusion/restriction. |
| `SelectionPhaseC` (S:40) | `sel-data; domain-def` | **PASS** | Pi/Prod max-norm carriers; real inclusion/restriction. |
| `SelectionPoint` (S:41) | `sel-data; domain-def` | **PASS** | Pi/Prod max-norm carriers; real inclusion/restriction. |
| `selectionReal` (S:43) | `sel-data; domain-def` | **PASS** | Pi/Prod max-norm carriers; real inclusion/restriction. |
| `selectionRe` (S:44) | `sel-data; domain-def` | **PASS** | Pi/Prod max-norm carriers; real inclusion/restriction. |
| `selectionLength` (S:45) | `sel-data; index-def` | **PASS** | Explicit Euclidean scalar/tensor formulas; no norm instance. |
| `selectionThick` (S:46) | `sel-data; index-def` | **PASS** | Explicit Euclidean scalar/tensor formulas; no norm instance. |
| `selectionDomain` (S:48) | `domain-def` | **PASS** | Frozen strip, action ball and parameter collar in correct order. |
| `selectionScalar` (S:50) | `sel-data; index-def` | **PASS** | Explicit Euclidean scalar/tensor formulas; no norm instance. |
| `selectionDG` (S:53) | `sel-data; index-def` | **PASS** | Explicit Euclidean scalar/tensor formulas; no norm instance. |
| `selectionDGVector` (S:56) | `sel-data; index-def` | **PASS** | Explicit Euclidean scalar/tensor formulas; no norm instance. |
| `SelectionData` (S:62) | `sel-data` | **PASS** | Inputs (a)–(d), finite type and top tensors; perturbation separate. |
| `SelectionPerturbation` (S:103) | `sel-data(c)` | **PASS** | Holomorphic, period-one, real, bounded by epsilon on full domain. |
| `sel_data` (S:112) | `sel-data` | **PASS** | Inputs (a)–(d), finite type and top tensors; perturbation separate. |
| `selectionCN` (S:114) | `fourier-cutoff` | **PASS** | Literal upstream scalar formulas; reconciliation remains N1. |
| `selectionCutoffError` (S:116) | `fourier-cutoff` | **PASS** | Literal upstream scalar formulas; reconciliation remains N1. |
| `selectionExponent` (S:118) | `schedule-consts` | **PASS** | Geometric ratios and all four growth factors agree. |
| `selectionVarpi` (S:119) | `schedule-consts` | **PASS** | Geometric ratios and all four growth factors agree. |
| `selectionQ` (S:120) | `schedule-consts` | **PASS** | Geometric ratios and all four growth factors agree. |
| `selectionVarrho` (S:121) | `schedule-consts` | **PASS** | Geometric ratios and all four growth factors agree. |
| `selectionCQ` (S:122) | `schedule-consts` | **PASS** | Geometric ratios and all four growth factors agree. |
| `selectionG` (S:123) | `schedule-consts` | **PASS** | Geometric ratios and all four growth factors agree. |
| `schedule_consts` (S:127) | `schedule-consts` | **PASS** | Geometric ratios and all four growth factors agree. |
| `schedule_ratios` (S:130) | `schedule-ratios` | **PASS** | All growth bounds; omitted immediate consequences follow algebraically. |
| `geom_recursion` (S:136) | `geom-recursion` | **PASS** | Nonnegative recursion, initial bound and 7/8 factor agree. |
| `SelectionSchedule` (S:145) | `schedule` | **PASS** | Literal geometric schedule; real powers for real exponents. |
| `selectionT` (S:155) | `schedule` | **PASS** | Literal geometric schedule; real powers for real exponents. |
| `selectionD` (S:156) | `schedule` | **PASS** | Literal geometric schedule; real powers for real exponents. |
| `selectiont` (S:157) | `schedule` | **PASS** | Literal geometric schedule; real powers for real exponents. |
| `selectionε` (S:159) | `schedule` | **PASS** | Literal geometric schedule; real powers for real exponents. |
| `selections` (S:161) | `schedule` | **PASS** | Literal geometric schedule; real powers for real exponents. |
| `selectionσ` (S:162) | `schedule` | **PASS** | Literal geometric schedule; real powers for real exponents. |
| `selectiond` (S:163) | `schedule` | **PASS** | Literal geometric schedule; real powers for real exponents. |
| `selectionr` (S:166) | `schedule` | **PASS** | Literal geometric schedule; real powers for real exponents. |
| `selectionell` (S:168) | `schedule` | **PASS** | Literal geometric schedule; real powers for real exponents. |
| `selectionTail` (S:170) | `schedule` | **PASS** | Literal geometric schedule; real powers for real exponents. |
| `selectionQsharp` (S:171) | `schedule` | **PASS** | Literal geometric schedule; real powers for real exponents. |
| `selectionQ₀` (S:174) | `schedule` | **PASS** | Literal geometric schedule; real powers for real exponents. |
| `schedule` (S:177) | `schedule` | **PASS** | Literal geometric schedule; real powers for real exponents. |
| `strip_budget` (S:179) | `strip-budget` | **PASS** | Summable losses, half strip, cutoff error and recurrence agree. |
| `schedule_props` (S:192) | `schedule-props` | **PASS** | S1–S5; final <= C1 follows from h2 and t0>0. |
| `selectionBumpRaw` (S:215) | `smooth-cutoff` | **PASS** | Exact bump integrals, finite maxima, support and tensor bounds. |
| `selectionBump` (S:216) | `smooth-cutoff` | **PASS** | Exact bump integrals, finite maxima, support and tensor bounds. |
| `selectionBumpL1` (S:218) | `smooth-cutoff` | **PASS** | Exact bump integrals, finite maxima, support and tensor bounds. |
| `selectionCutoffC` (S:219) | `smooth-cutoff` | **PASS** | Exact bump integrals, finite maxima, support and tensor bounds. |
| `selectionExtensionC` (S:221) | `smooth-cutoff` | **PASS** | Exact bump integrals, finite maxima, support and tensor bounds. |
| `smooth_cutoff` (S:226) | `smooth-cutoff` | **PASS** | Exact bump integrals, finite maxima, support and tensor bounds. |
| `SelectionChain` (S:235) | `retained-def; inductive-lemma` | **PASS** | Raw chain data and finite sums, with no asserted construction. |
| `selectionFrequency` (S:242) | `retained-def; inductive-lemma` | **PASS** | Raw chain data and finite sums, with no asserted construction. |
| `selectionEnergy` (S:245) | `retained-def; inductive-lemma` | **PASS** | Raw chain data and finite sums, with no asserted construction. |
| `selectionCompose` (S:247) | `sec-comp#data` | **PASS** | X0 composed through X(nu-1), shared parameter. |
| `selectionModeLength` (S:252) | `schedule` | **PASS** | l1 cutoff, correct shell endpoint and ceiling/log shell index. |
| `selectionShell` (S:253) | `schedule` | **PASS** | l1 cutoff, correct shell endpoint and ceiling/log shell index. |
| `selectionModeStage` (S:257) | `schedule` | **PASS** | l1 cutoff, correct shell endpoint and ceiling/log shell index. |
| `selectionExtendedFrequency` (S:259) | `finite-extension` | **PASS** | Cutoff-weighted real frequency increments on fixed real carrier. |
| `selectionRetained` (S:264) | `retained-def` | **PASS** | Faithful retained-chain predicate; too restrictive for F1 export only. |
| `selectionInitial` (S:269) | `initial` | **PASS** | Translation I=b+eta, Taylor remainder n*C1*s0^2/2, reality/periodicity. |
| `initial` (S:273) | `initial` | **PASS** | Translation I=b+eta, Taylor remainder n*C1*s0^2/2, reality/periodicity. |
| `selectionM₀` (S:289) | `sel-data(d)` | **PASS** | Actual diagonal jet supremum on Euclidean thickening. |
| `selectionChat` (S:292) | `sublevel; power-law; sel-data` | **PASS** | Explicit diameter, beta, measure-loss and lattice-gap factors. |
| `selectionCDio` (S:298) | `sublevel; power-law; sel-data` | **PASS** | Explicit diameter, beta, measure-loss and lattice-gap factors. |
| `selectionGamma` (S:300) | `sublevel; power-law; sel-data` | **PASS** | Explicit diameter, beta, measure-loss and lattice-gap factors. |
| `selectionT₀` (S:304) | `adm-params` | **PASS** | All three branches retained; normalized C1 and exact constants. |
| `selectiont₀` (S:307) | `adm-params` | **PASS** | All three branches retained; normalized C1 and exact constants. |
| `selectionXi` (S:309) | `adm-params` | **PASS** | All three branches retained; normalized C1 and exact constants. |
| `selectionThetaMax` (S:312) | `adm-params` | **PASS** | All three branches retained; normalized C1 and exact constants. |
| `selectionLambdaMax` (S:315) | `adm-params` | **PASS** | All three branches retained; normalized C1 and exact constants. |
| `selectionAdmissible` (S:320) | `adm-params` | **PASS** | All three branches retained; normalized C1 and exact constants. |
| `adm_params` (S:321) | `adm-params` | **PASS** | All three branches retained; normalized C1 and exact constants. |
| `selectionAdapted` (S:325) | `free-radius` | **PASS** | sqrt(2 epsilon/(n C1)), epsilon0=2 epsilon. |
| `SelectionAdmissibility` (S:330) | `adm-choice` | **PASS** | A1–A6 scalar obligations, positivity and lambda bound. |
| `adm_choice` (S:345) | `adm-choice` | **PASS** | A1–A6 scalar obligations, positivity and lambda bound. |
| `free_radius` (S:350) | `free-radius` | **PASS** | Adapted admissibility, radius bound and balancing identities. |
| `SelectionFiniteChain` (S:360) | `retained-def` | **PASS** | Faithful retained-chain predicate; too restrictive for F1 export only. |
| `sec_retained_data` (S:374) | `retained-def` | **PASS** | Faithful retained-chain predicate; too restrictive for F1 export only. |
| `finite_extension` (S:376) | `finite-extension` | **FAIL** | F1: adds the retained-set recursion to arbitrary nested-chain premises. |
| `finite_divisor` (S:392) | `finite-divisor` | **PASS** | Finite retained set; one-tail loss gives boxed divisor conclusion. |
| `continuous_series_on_compact` (S:405) | `step:ps-lim (local supplier)` | **PASS** | Summable envelope gives uniform convergence, continuity and pointwise sum. |
| `selectionΛ` (S:415) | `homological; exported-sums` | **PASS** | Exact coth(pi r)^n-1 scalar expression on positive radii. |
| `selectionA` (S:418) | `inductive-lemma:O3; exported-sums` | **PASS** | Unscaled phase, displacement and real-flow budgets agree. |
| `selectionAlpha` (S:422) | `inductive-lemma:O3; exported-sums` | **PASS** | Unscaled phase, displacement and real-flow budgets agree. |
| `selectionKappa` (S:424) | `inductive-lemma:O3; exported-sums` | **PASS** | Unscaled phase, displacement and real-flow budgets agree. |
| `selectionMapBudget` (S:426) | `inductive-lemma:O3; exported-sums` | **PASS** | Unscaled phase, displacement and real-flow budgets agree. |
| `selectionRealBudget` (S:428) | `inductive-lemma:O3; exported-sums` | **PASS** | Unscaled phase, displacement and real-flow budgets agree. |
| `SelectionIteration` (S:435) | `inductive-lemma; step:ps-iter` | **PASS** | Infinite coherent output strengthens existence; O1–O5 recoverable; N2. |
| `inductive_lemma` (S:514) | `inductive-lemma; step:ps-iter` | **PASS** | Infinite coherent output strengthens existence; O1–O5 recoverable; N2. |
| `inductive_lemma_adapted` (S:518) | `inductive-lemma; step:ps-iter` | **PASS** | Infinite coherent output strengthens existence; O1–O5 recoverable; N2. |
| `SelectionOutput` (S:524) | `parameter-selection` | **PASS** | Same chain/cutoffs, compact sets, measure, real frequency and Diophantine output. |
| `parameter_selection` (S:583) | `parameter-selection` | **PASS** | Same chain/cutoffs, compact sets, measure, real frequency and Diophantine output. |
| `selectionQactual` (S:588) | `exported-sums` | **PASS** | E1–E3 scalar budgets; E4 follows from returned map estimate. |
| `exported_sums` (S:592) | `exported-sums` | **PASS** | E1–E3 scalar budgets; E4 follows from returned map estimate. |
| `param_lip_sum` (S:611) | `param-lip-sum` | **PASS** | Adapted increment/collar summability with exact 2^-10/16 budget. |
| `finite_measure` (S:619) | `finite-measure` | **PASS** | Retained chain is a source premise here; extensions and finite good set output. |
| `SelectionComposition` (S:636) | `composition` | **PASS** | Joint holomorphy, canonical maps, domain, product derivative and block sums. |
| `composition` (S:681) | `composition` | **PASS** | Joint holomorphy, canonical maps, domain, product derivative and block sums. |
| `sec_comp_data` (S:686) | `sec-comp#data` | **PASS** | X0 composed through X(nu-1), shared parameter. |
| `selectionEvaluation` (S:688) | `sec-limit#data` | **PASS** | Original actions b+defect; phase block order theta,b. |
| `sec_limit_data` (S:691) | `sec-limit#data` | **PASS** | Original actions b+defect; phase block order theta,b. |
| `SelectionLimit` (S:694) | `limit-map` | **PASS** | Fixed-strip value/derivative convergence, reality, periodicity and bounds. |
| `limit_map` (S:722) | `limit-map` | **PASS** | Fixed-strip value/derivative convergence, reality, periodicity and bounds. |
| `selectionHamiltonian` (S:726) | `limit-torus; p0:hamsymp` | **PASS** | Direct frozen realHamiltonian wrapper, no new dynamics. |
| `SelectionTori` (S:729) | `limit-torus` | **PASS** | Frozen field/form; analytic, invariant, Lagrangian, immersed and embedded outputs. |
| `limit_torus` (S:748) | `limit-torus` | **PASS** | Frozen field/form; analytic, invariant, Lagrangian, immersed and embedded outputs. |
| `collar_increment_lipschitz` (S:753) | `step:lf-stage (local supplier)` | **PASS** | Short/long-distance dichotomy; no convexity of compact set needed. |
| `selectionDelta` (S:760) | `displacement; gamma-inverse` | **PASS** | Exact epsilon half-power, gamma inverse and beta exponent. |
| `selectionCDelta` (S:763) | `displacement; gamma-inverse` | **PASS** | Exact epsilon half-power, gamma inverse and beta exponent. |
| `selectionCGamma` (S:766) | `displacement; gamma-inverse` | **PASS** | Exact epsilon half-power, gamma inverse and beta exponent. |
| `gamma_inverse` (S:770) | `displacement; gamma-inverse` | **PASS** | Exact epsilon half-power, gamma inverse and beta exponent. |
| `SelectionDisplacement` (S:773) | `displacement` | **PASS** | Same torus witness, both blocks, absolute and power bounds. |
| `displacement` (S:784) | `displacement` | **PASS** | Same torus witness, both blocks, absolute and power bounds. |
| `SelectionLipschitz` (S:788) | `lipschitz-family` | **PASS** | Separate 2^-11 terms and joint 2^-10 max-norm bound. |
| `lipschitz_family` (S:796) | `lipschitz-family` | **PASS** | Separate 2^-11 terms and joint 2^-10 max-norm bound. |
| `selectionHalfCell` (S:800) | `evaluation-bilipschitz` | **PASS** | Period-one half/closed cells and AddCircle quotient. |
| `selectionClosedCell` (S:802) | `evaluation-bilipschitz` | **PASS** | Period-one half/closed cells and AddCircle quotient. |
| `selectionQuotient` (S:804) | `evaluation-bilipschitz` | **PASS** | Period-one half/closed cells and AddCircle quotient. |
| `SelectionEvaluationOutput` (S:808) | `evaluation-bilipschitz; situation` | **PASS** | Nested single witness; inverse, extension, Borel image, volume and compactness. |
| `evaluation_bilipschitz` (S:849) | `evaluation-bilipschitz; situation` | **PASS** | Nested single witness; inverse, extension, Borel image, volume and compactness. |
| `situation` (S:854) | `evaluation-bilipschitz; situation` | **PASS** | Nested single witness; inverse, extension, Borel image, volume and compactness. |
| `selectionFixedKey` (S:858) | `adm-budget-beta; displacement-power` | **FAIL** | F2: fixes d.h instead of the allowed actual M0 datum. |
| `selectionBetaExponent` (S:860) | `adm-budget-beta` | **PASS** | B0=2 max(2G0,1+mu G0); rho=2 specialization agrees. |
| `adm_budget_beta` (S:865) | `adm-budget-beta` | **FAIL** | F2: coefficient may depend on the entire h; narrower universal family. |
| `displacement_power` (S:871) | `displacement-power` | **FAIL** | F2: same over-restricted family for cD and cstar. |
| `SelectionRates` (S:882) | `adm-budget` | **PASS** | All eight rates, correct exponent and coefficient before other seven rates/family. |
| `selectionBudgetD` (S:894) | `adm-budget` | **PASS** | All eight rates, correct exponent and coefficient before other seven rates/family. |
| `selectionBudgetG` (S:896) | `adm-budget` | **PASS** | All eight rates, correct exponent and coefficient before other seven rates/family. |
| `selectionBudgetL` (S:898) | `adm-budget` | **PASS** | All eight rates, correct exponent and coefficient before other seven rates/family. |
| `selectionBudgetJ` (S:899) | `adm-budget` | **PASS** | All eight rates, correct exponent and coefficient before other seven rates/family. |
| `selectionBudgetX` (S:901) | `adm-budget` | **PASS** | All eight rates, correct exponent and coefficient before other seven rates/family. |
| `selectionBudgetH` (S:903) | `adm-budget` | **PASS** | All eight rates, correct exponent and coefficient before other seven rates/family. |
| `selectionBudgetExponent` (S:907) | `adm-budget` | **PASS** | All eight rates, correct exponent and coefficient before other seven rates/family. |
| `selectionFamilyBounds` (S:911) | `adm-budget` | **PASS** | All eight rates, correct exponent and coefficient before other seven rates/family. |
| `adm_budget` (S:918) | `adm-budget` | **PASS** | All eight rates, correct exponent and coefficient before other seven rates/family. |

## Consumer, frozen-object, definition and package verdicts

**Consumers: FAIL for the full advertised interface (F2); remaining witness surface PASS, with N1 release gates.** Direct consumers are p11a4 (iteration/selection/budgets), p11a5 (quantitative theorem, minorant and zero case), and Part 11 (K1–K6); physical transport is deferred to Part 13. For positive epsilon, one `SelectionEvaluationOutput` projects to the same chain, Hinf, Kinf, omega, analytic real tori, displacement, parameter Lipschitz bounds and image estimates. Thus it cannot combine unrelated existential choices. Choose H=Hinf: compactness, measure loss and frozen Diophantine property are available. The orbit field is the frozen field of the frozen real Hamiltonian in original actions, so the shift b is correct. Embedding lower bounds imply injectivity, and the inverse inequality and exponent 2*n give the source lower measure bound with the correct orientation.

The fixed-radius selection theorem permits epsilon=0, while the adapted-radius family requires epsilon>0; this matches the p11a4 source. P11a5 supplies its separate zero-perturbation case and monotone minorant, so their absence from P11B is not a defect. Part 11 can choose N=2n and rho=2 and use the stronger exponent restriction it already supplies. Actual M0 is a supremum in P11B; a consumer with only a supplied upper bound needs precisely the minorant comparison assigned to P11a5, not an equality with that bound.

The brief's requested search for `\Nref{bpN:p3:` in I/P and N Parts 7/11/12 was performed. Those are consumers of the general ODE layer, not direct users of this weak-KAM layer. No P11B theorem claims their continuation/barrier/uniqueness conclusions. Accordingly there is no reason to introduce replacement ODE predicates into these signatures. For later invariant-set transport, a direct `HasDerivAt` orbit is available; agreement with arbitrary solution predicates remains the downstream uniqueness/transport step.

**Frozen objects: PASS.** Read the literal frozen files `KAM/Frozen/Defs/{ActionNbhd,ComplexStrip,IsDiophantine,RealHamiltonian,FrequencyMap,HamiltonianVectorField,HamiltonianVectorFieldC,SymplecticForm}.lean` and `KAM/Frozen/Planetary/Defs/Phase.lean`. The signatures use these objects directly. `selectionHamiltonian` unfolds to `realHamiltonian`; it is not an independent definition of the field. Real inclusion is `phaseToC` from the existing Kepler carrier. `Canonical.symplFormC` is the existing complex form; real restriction to frozen `symplecticForm` is an explicit B16 proof obligation. The frozen real `frequencyMap` is not definitionally the real part of the complex-gradient expression; the holomorphic-real restriction bridge must be proved, as the design requires. No frozen defect or altered frozen statement was found.

**Definitions/structures: PASS except F2's advertised uniform-data key.** No new global function/matrix instance, EuclideanSpace ambient carrier, conclusion-shaped standing field, or assumed constructed torus occurs. Input structures contain source scalar, geometric, analytic and finite-type hypotheses. Raw chains/schedules assert no output properties. Result structures contain conclusions and are used as outputs. `SelectionFiniteChain` is correctly the retained-chain predicate for the lemmas that assume retention; F1 concerns its use at the earlier, more general extension theorem. Supremum/integral definitions require the boundedness, integrability and positivity proofs explicitly assigned to B01/B04/B07. Dimension zero or out-of-range derivatives can give total-library default values, but every quantitative use here is guarded by n>=1, the source derivative ranges, and smoothness/holomorphy. No theorem was found using an unguarded junk division, logarithm or derivative value.

**Packages: PASS as a design, subject to F1/F2 interface corrections and N1.** The 20 B01–B20 packages form an acyclic import plan with maximum wave 14 and estimates 200–800 lines in the listed table, all below 1500. The important type-level edges B10<-B13 and B16->B17->B18->B19 are represented. Raw chain definitions precede Extension. The facade is not a new proof package. Full-prefix recursive construction is required for coherence; a theorem producing unrelated witnesses for each length would not fill the present record. Output packaging is sizable, so the 800-line B10 estimate remains a split trigger, not a guarantee of elaboration performance. No production module is created, hence there is no production module target for a `lake build` in this audit.

## Independent verification

All audit Lean invocations use `LEAN_NUM_THREADS=1`, `nice -n 5`, and exclusive locks on both `/tmp/inp-lean-slot-{1,2}.lock` and all three `/tmp/inp-sig-slot-{1,2,3}.lock`. This serializes the auditor's elaborations with the shared gates; no parallel audit Lean process, heartbeat override, library rebuild, cache fetch or clean was launched. `lake env lean` ran from `/root/code/KAM-inp` because this design worktree has no build snapshot; the input file remained the requested local scratch copy.

1. Signature elaboration, **run once**:

   ```text
   cd /root/code/KAM-inp
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean \
     /root/code/KAM-inp-design-p11b/.drafts/scratch/P11BSignatures-audit1.lean
   exit 0
   exactly 28 warnings: declaration uses `sorry`
   no errors or other diagnostics
   ```

   The scratch copy had the exact original SHA256. The canonical delivery was never edited.

2. Named APIs, temporary `.lake/abi-scratch/P11BAuditNames.lean`: **exit 0**, 18 successful `#check @...` commands. Mathlib names checked were `Real.log_le_sub_one_of_pos`, `HasCompactSupport.hasFDerivAt_convolution_right`, `MeasureTheory.tendsto_measure_iInter_atTop`, `hasSum_geometric_of_norm_lt_one`, `tendstoUniformlyOn_tsum_nat`, `continuousOn_tsum`, and `HasFDerivAt.comp`. Existing KAM names checked were `norm_fderiv_le_of_closedBall_bound`, `norm_iteratedDeriv_line_le_of_closedBall`, `increments_open`, `uniform_limits`, `Fourier.exp_sums`, `decay`, `decay_boundary_radius`, `mcshane_prod`, `lipeo_onto`, `lipeo_bounds`, and `lip_image_prod`.

   Type inspection confirms: convolution requires a locally integrable left input and a compactly supported C1 right kernel (higher orders need iteration); continuity from above requires null measurability, antitonicity and one finite-measure term; the two series lemmas require a summable envelope and completeness, with no open-domain assumption. These fit their proposed uses. `uniform_limits` still needs a fixed open complex domain and a uniform derivative limit, so it is correctly reserved for B15, not used to close the compact-real-set gap by itself. The measure API accepts the actual product carrier and exponent 2*n.

3. `scripts/lint_sources.sh`: **exit 0**; exact output: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (144 frozen declarations)`. The ABI subprocess uses a temporary PATH shim to run against the existing shared build while the whole invocation holds the five exclusive locks. This does not alter source, generated files or the manifest.

4. Mechanical checks: Appendix equality **PASS**; 119/119 unique graph-node coverage **PASS**; explicit declarations 133, theorem bodies 28, all bodies `sorry`, no definition body `sorry`; 927-line signature file below cap; package dependency waves recomputed **PASS**; `git diff --check inp...HEAD` **exit 0**. Final report whitespace check: no trailing whitespace, terminal newline present; git status contains only the requested untracked report.

5. Axioms: no mathematical theorem was proved or sealed here. All 28 draft theorem bodies are literally `sorry`, so no standard-axioms-only result is claimed. The designer's separate `#print axioms` receipt reports `[propext, sorryAx, Classical.choice, Quot.sound]` for `parameter_selection`, `limit_torus`, `evaluation_bilipschitz`, and `displacement_power`; that receipt was read, not independently rerun under the one-signature-elaboration constraint. Imported theorem implementations and kernel replays are outside this design audit.

## Closeout

Files changed: only `docs/tracks/P/design/DESIGN-P11B-design-audit-1.md`. Audit-created scratch files/probes are removed after checks. No production, frozen, manifest, generated or canonical signature file was edited. No state-changing git command was used.

Suspected pinned-paper errata: none newly asserted by this audit. Source/design deviations requiring action are F1 and F2. The blueprint's compact-set uniform-limit citation gap, real-flow/reality obligations, corrected shell endpoint, and absence of a common positive-action-radius normal form are already disclosed in the design and remain explicit obligations/limitations. They are not closed by `sorry` output fields.

Closeout criteria: full explicit-declaration ledger classified; findings include concrete failed defenses and replacement signatures; consumers, frozen objects and packages assessed; signature/API checks completed; lint and final scope check recorded. **Do not release this exact signature surface as source-faithful until F1 and F2 are corrected and re-audited.**
