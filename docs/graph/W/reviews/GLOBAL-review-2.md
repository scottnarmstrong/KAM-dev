# Track W global root-closure review, round 2

Reviewer: `sol-global-W` (GPT-6.1-Sol, codex-1), 2026-10-31. Same global tag as round 1, as required by the round-2 brief; distinct from the writer, all slice/delta tags and `sol-kamend-W`.

## Round-1 finding resolutions

### G1: RESOLVED — direct section-data edges

All 121 complete EDGE lines proposed in round 1 occur verbatim in the assembled graph. A read-only comparison with the round-1 graph at `3c54696db828e44a378390eed4927fcdd46a6952` confirms the additions by target:

| Data target | Added direct edges |
| --- | ---: |
| `bpW:w3#data` | 81 |
| `bpW:w5#data` | 24 |
| `bpW:w7#data` | 15 |
| `bpW:w8#data` | 1 |
| `bpW:w7:basic#data` | 28 |

These are 149 additions, not 149 newly introduced mathematical premises. The original packages and their source premises remain unchanged. The extra 28 edges apply the same direct-use rule to W7's basic frequency-pair context (`w7-measure.tex:340–345`), including its downstream preparatory/iteration and measurability consumers.

The whole-graph scan checks every SOURCE_HYPOTHESES for literal package references and the standardized `W3 standing data`, `W5 standing data` and `W7 standing data` descriptions. There are no missing direct package edges. In particular, all 82 W3 standing-data invocations, all 27 W5 standing-data invocations, all 16 W7 standing-data invocations, and all 36 invocations of `bpW:w7:basic#data` have their direct supplier. These totals include edges already present before round 1. The remaining data nodes (`w0n:birkhoff`, `w0n:nondeg-sec`, W3 quartic/main, W6 notation, W7 density and W8) were checked with their source contexts; no residual package omission was found.

Evidence: `docs/graph/W/DEPGRAPH.md:8768` (W3 data), `:12232` (W5 data), `:16082` (W7 data), `:16113` (basic data), `:19027` (W8 data); the individual consumer EDGE lines; `w3-birkhoff.tex:23–27`, `w5-kamstep.tex:35–39`, `w7-measure.tex:33–41,340–345`, `w8-assembly.tex:36–54`. All affected records are independently REVIEWED by delta 9; this global verdict also checks their substance directly.

### G2: RESOLVED — K amendments, manifest re-pin and exact imports

The four append-only amendments are present in `docs/graph/K/AMENDMENTS.md:881–960`, with reviewer `sol-kamend-W`, and are included in K's assembled effective records. `docs/graph/K/reviews/AMEND-W-G2-review.md:5` records PASS for K-A045 through K-A048. Independently rereading the owner source confirms the corrections: `p1-analysis.tex:24–47` fixes finite-dimensional complex normed targets, positive strip widths, nonzero strip dimension and period-one Fourier conventions. The actual statements are at `:296–312`, `:531–534`, `:757–768` and `:786–789`. The amendments expose those inherited premises without changing conclusions or introducing a Banach-target theorem.

Read-only `git show` confirms commit `aebcc14ea2dcf5d203d11a71482ef4c9f7a34fd8` changes K's FROZEN_MANIFEST hash to `674c73210fe8aeef703101ebe014dbc3e8569cb12f54a14dba1a7ff418d76aab`, which equals the current manifest SHA-256. K's requested full linter/dashboard check exits **0**, with empty stdout and stderr.

For every remaining W import, each of SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION and CONSTANT_SCOPE is byte-for-byte equal to the corresponding **effective** K JSON field, including applied amendments:

| W import | Four exact-copy comparisons | All W consumers |
| --- | --- | --- |
| `K:bp:p1:decay` | PASS, 4/4 | `stepW:w1:fbdecay` |
| `K:bp:p1:fourier-basic` | PASS, 4/4 | `stepW:w1:fsum` |
| `K:bp:p1:strip-identity` | PASS, 4/4 | `stepW:w1:fsum` |

Import records: `docs/graph/W/DEPGRAPH.md:20556,20582,20608`. Both graphs were read with `python3 -I scripts/proof_depgraph.py --db <graph> --json`; the comparison did not use unamended packet fields.

Applicability passes. At `w1-sequences.tex:1007–1013`, `fsum` applies uniqueness and strip identity to the scalar function `⟨e,u-v⟩`, not to the Hilbert target itself. Continuity, periodicity, vanishing coefficients and holomorphy come from the enclosing hypotheses, orthant summability, and the uniformly convergent sum; the strip has positive width under the standing strip convention. At `:1042–1050`, `fbdual` supplies a scalar holomorphic, periodic map `φ ∘ u`, bounded by M, and commutes φ with its coefficient integral. `fbdecay` applies decay to that scalar function with `n≥1`, `s>0`, and `0≤s'<s`, then takes the boundary limit and dual norm. Thus every imported use has a finite-dimensional target, namely ℂ. Their EDGE locators point to these consumer uses (`DEPGRAPH.md:4679,4769`).

### G3: RESOLVED — W owns the Banach-target coefficient argument

`stepW:w1:hacoef` (`docs/graph/W/DEPGRAPH.md:4187`) is an ordinary W step, located at `w1-sequences.tex:829–835`. Its DEPS are exactly `stepW:w1:hamargin`, `bpW:w1:ext-onevar` and `bpW:w1:ext-integral`. Its NOTE explicitly identifies K's `han-cauchy` through `han-bounds` argument as proof provenance for the local complete-target adaptation. There is no K import edge.

The source itself replaces K's finite-dimensional W by a complete F and names precisely the Banach-valued Cauchy formula, Fubini and integration of uniformly convergent continuous F-valued series on a compact torus. K's proof at `p1-analysis.tex:320–350` supplies the cited argument pattern; compactness is of the domain torus. The preceding W margin step supplies the larger closed polydisc and its bound. This is the SPEC proof-reuse case, with no new premise granting the desired coefficient conclusion.

`K:bp:p1:holomorphic-analytic` is absent from the W node set and from every W DEPS list. Its coverage record at `docs/graph/W/DEPGRAPH_COVERAGE.md:9835` is REVIEWED and EXCLUDED as proof provenance. Exactly three imported nodes remain, all referenced.

## Root verdict and reconstructed source fields

**PASS** for the root's source correspondence and for the whole assembled source dependency model. G1–G3 are resolved; no new blocking, major or minor global finding was established. This accepts source topology, not Lean proof completion. The two expected global-header placeholders remain for the orchestrator to fill.

Root: `bpW:wh:nlw2`; export `KAM.Wave.nlw2`; anchor `wave.nlw2.v1`; contract `wave.nlw2`, version `1`.

The following reconstruction comes from `w-headline.tex:19–71` and the frozen declaration statement `KAM/Frozen/Wave/Theorems/Nlw2.lean:43–81`, with the permitted frozen definitions. It agrees with the four root fields at `docs/graph/W/DEPGRAPH.md:20518`.

**SOURCE_HYPOTHESES:** `m : ℝ`, `hm : 0 < m`. Actions and angles have carrier `Fin 2 → ℝ`, with positive actions P, period-one angles, positive modes `ℕ+` and tangential mode `i+1`. The fixed headline space is `WaveSpace = ℓ²_ℝ × ℓ²_ℝ`, in weighted coordinates at `a=p=1`, with product max norm. Coefficients are `coeff y j = y j/(j exp j)`. Reconstructions, cubic gradient and linear torus have their frozen definitions. Set `r(I)=sqrt(I 0+I 1)` and `B_h=Metric.ball 0 h`. No normal-form or KAM conclusion is an additional premise.

**SOURCE_QUANTIFIERS:** For every m>0 choose, in this order, `r₀,C,τ : ℝ`, total `η : ℝ → ℝ`, `Γ : Set (Fin 2 → ℝ)`, total `ν : (Fin 2 → ℝ) → Fin 2 → ℝ`, and total `K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → WaveSpace`. Require `r₀>0`, `C>0`, `τ>1`; η≥0 on `(0,r₀)` and η→0 along `nhdsWithin 0 (Ioi 0)`; Γ measurable and contained in `{I∈P | r(I)<r₀}`; `ContinuousOn ν Γ` and joint `ContinuousOn (uncurry K) (Γ ×ˢ univ)`. These choices precede I, θ, θ₀, t, x and j. For each I∈Γ choose a separate γ_I>0. Clause (3) quantifies over every positive-carrier proof hI. The headline's partial-domain notation is represented by the frozen total functions, whose off-domain values impose no additional requirement.

**SOURCE_CONCLUSION:** In frozen order:

1. `volume(Γ∩B_h)/volume(P∩B_h) → 1` in `[0,∞]`, along the positive-sided filter at zero.
2. Each ν(I), I∈Γ, is `(γ_I,τ)`-Diophantine; ν tends to `(lam m hm (i+1)/(2π))_i` along `nhdsWithin 0 Γ`.
3. Each K_I is `IsAnalyticTorusEmbedding`; at every same angle θ, `‖K_I θ-linearTorus I hI θ‖≤η(r(I))r(I)` and `‖K_I θ‖≤C r(I)`.
4. For every I∈Γ, θ and j∈ℕ+, the two coefficient curves at t=0 have `HasDerivAt` derivatives `lam_j * coeff(K_I θ).2 j` and `-(lam_j * coeff(K_I θ).1 j)-cubicGrad m hm (K_I θ).1 j`.
5. For every θ₀, `u(t,x)=reconU m hm (K_I(θ₀+t•ν(I))).1 x` is analytic at each point of ℝ×[0,π], satisfies the exact `IsClassicalSolution`, and has time derivative `reconV m hm (K_I(θ₀+t•ν(I))).2 x`. For all t and x∈[0,π], `|u|+|derivWithin (u t) (Icc 0 π) x|+|reconV|≤C r(I)`.
6. If `K_I θ=K_I' θ'` for I,I'∈Γ, then I=I' and `θ−θ'` is the coordinatewise cast of an integer vector.

**CONSTANT_SCOPE:** All seven witnesses follow m and precede the inner variables. They may depend on m, with no uniformity in m. C is the same witness in (3) and (5), τ is common to all shells, and γ_I is per I and may degenerate.

## Whole-graph global checks

The whole current graph was checked, including unchanged records and the eleven pinned W source parts; the round-1 report and slice reviews were background. Source-reference and frozen-symbol scans were used to identify candidates for adversarial rereading, not as semantic acceptance criteria. Forward statements, comparisons, proof provenance, individual steps cited by their enclosing theorem name, and premise checks were distinguished from actual theorem applications.

| Global obligation | Result and source evidence |
| --- | --- |
| Frozen-order assembly | PASS. Root PROOF_SOURCE is `w8-assembly.tex:552–599`; its proof-result edge is to `bpW:w8:nlw2-proof` (`DEPGRAPH.md:19900`). The ordered steps are `p-pos`, `p-etapos`, `p-etalim`, `p-meas`, `p-incl`, `p-nucont`, `p-Kcont`, `p-dens`, `p-dioph`, `p-lim`, `p-emb`, `p-close`, `p-size`, `p-inv`, `p-pde`, `p-inj`, then `p-assembly`: 16 conjunct-check steps plus assembly. No frozen conjunct is missing. Definition-symbol edges are separate from the proof-result edge. |
| W0/W1/W3 conventions | PASS. `w0-conventions.tex:39–144`, `w0-normalization.tex:268–307`, `w1-sequences.tex:30–62,242–281,300–337`, `w3-birkhoff.tex:119–151,275–322`: weighted coordinates versus physical coefficients, max versus Hilbert/sum norms and √2 factors, positive-mode indexing, clockwise rotation, period one, the 1/16 prefactor and corrected A/B are retained. `K_s` and `C_m` have their stated dependence; `C_m` is independent of m. |
| W2–W3 on W1 | PASS. `w2-reconstruction.tex:94–159,211–218,250–299,324–359` uses the sine features, bounded coordinate evaluations, frozen cubic identification and the separately retained force step. `w3-birkhoff.tex:241–245,293–322,395–450,831–865` supplies the cubic/normal-form interfaces on their stated carriers. No premise is silently discharged by changing the target space. |
| W4 on W1/W3 | PASS. `w4-homological.tex:286–325,390–488,497–555,658–732`: Banach coefficient estimates and ℓ¹ summation replace the invalid operator square-sum route. The Riesz construction has explicit `ext-riesz`, `ext-lp`, Schur and index suppliers. The derivative interpretation of the weak bracket retains guard (G). |
| W3/W4 into W5 | PASS. `w5-kamstep.tex:137–247,266–326,353–375,622–727`: general smoothing, modified Q divisors, Taylor class, symmetry, principal square roots, action–angle domain and weight comparisons are explicitly supplied. For the modified Lipschitz application β=1/4 and loss 1/2 satisfy `2β≤p+1−p_+`; the preparatory exponent is 53, the iteration exponent 52. Guard (G) holds at a=p=1. |
| W5 into W6 and repaired W4–W6 steps | PASS. `w5-kamstep.tex:378–515,524–606`, `w6-iteration.tex:47–194,209–333`: convex flow margins, second-derivative symmetry, triangular integral, inverse parameter differences, weak conjugacy and regularity at torus points are modeled. The preparatory divisor bound uses `zones(i)` directly, before any admissible-family construction. Its sharp sup displacement comes from `f-flow`, and its starting size includes the Lipschitz part. Borel construction is direct and does not assume its output family. No concealed residual SOURCE_GAP was found in these repairs. |
| W6 into W8 | PASS. `w6-iteration.tex:279–286,300–412`, `w8-assembly.tex:130–248`: W6's statements hold for every admissible ε₀, and `sharp-prep` supplies `ε^flat_{0,n}≤ε_{0,n}≤γ₁ checkα_n`. The shell choice gives `e_tor≤E₅ t_n^(1/64)→0`, preserving little-o closeness at the same angle. |
| W7 constants and absence of circularity | PASS. `w7-measure.tex:211–231,411–446`: `Xzones#consts` (`DEPGRAPH.md:16141`) contains only the affine coefficients and minimum definitions. `constdef` (`:15271`) uses that definition, not the conditional zone estimate (`Xzones`, `:15924`). Positivity follows from finite X and A3, independently of the later frequency family. C1–C5 precede Π,α; W6's s,σ,M,γ₀,γ₁,γ and θ precede shell α; W8's E constants and t₀ precede shells. |
| W7 into W8 | PASS. `w7-measure.tex:559–737`, `w8-assembly.tex:119–178,565–582`: q=1/2, Borel trimmed shells, α_n=t_n^(95/64), admissibility and exclusion supplies match the measure/density consumer. The relative defect is O(t_n^(1/94)). The Diophantine rescaling gives γ_I=checkα_n/(8π); the frequency limit uses the correct `i+1` modes. |
| W3 return and W2 PDE applications in W8 | PASS. `w8-assembly.tex:284–409,464–544,583–597`: the shell image is in B_ρ₁ and its real inverse-coordinate image in B_r₁ before the Birkhoff map is used. Weak invariance is transported through `transport-tori-weak`, which derives the extra weight rather than assuming it. The PDE step consumes embedding, the C₃ size bound and exact coefficient invariance through `w2:clause5`, giving the common C. Family injectivity uses analytic coefficient solutions, uniqueness, positive tangential amplitudes, winding and the injective frequency map. |
| Alternative routes | PASS. Exactly two route nodes, both owned by `stepW:w1:tricoord`: `#via-cubic-bound` and `#via-selection` (`w1-sequences.tex:466–470`). Each is separately sufficient, and they are OR alternatives, not conjunctive DEPS. |
| Frozen symbols and cross-part edges | PASS. The permitted frozen definitions were compared with their transcriptions. Source-symbol candidates were checked under rule 11: bare λ in W5–W8 is the parameter weight and φ there is a phase. No new missing, reversed, merely transitive, provenance-only or false symbol edge was established. Consumer EDGE locators were checked at the named cross-part applications and all import uses. |
| External boundary | PASS. 47 external leaves: 44 W ext-items and the three K imports. The new `w4:ext-riesz`, `w5:ext-symm`, `w5:ext-sqrt`, `w5:ext-triangle` are present (`DEPGRAPH.md:10730,12262,12288,12314`). Every external has empty DEPS/ROUTES. No additional external or duplicate alias was found. The sole assumption leaf is `bpW:w0:mass`. |
| Anchor identity | PASS. All 13 anchor files, exports, IDs, contract IDs/versions and author-controlled ABI hashes match manifest identity fields. The pre-existing `IsDiophantine` anchor is W's thirteenth anchor under SPEC's explicit ruling. Every non-anchor, including each import, has all FROZEN_* fields `-`. No manifest state or proof-status field was used. |

## Reachability and coverage findings

**None.** There are 695 nodes, 2,545 EDGE records, one root and a root closure of 695 nodes; 72 dependency leaves, including 47 externals and one standing assumption; two route nodes; zero unreachable nodes, uncovered nodes, review-queue entries or effective SOURCE_GAP nodes. All 695 nodes are REVIEWED. All 1,094 coverage items are REVIEWED: 709 mapped items and 385 EXCLUDED items.

The corpus inventory was cross-checked against labelled result environments, proof steps, external items, unlabelled data/proof regions and source references. Nested hypothesis/formula labels C1–C2, H1–H3 and F1–F3 are covered by their enclosing result records as SPEC requires; they are not additional assumed leaves.

The requested reachability exclusions remain justified:

- The reconstruction rescaling/dictionary is not invoked by an in-closure proof; coefficient transport comes from W1.
- `w0n:pde-equiv` and its time/ident/converse steps are unused as theorem suppliers. W2 uses the independently retained `stepW:w0n:force`; its parenthetical mention of the proposition identifies that step's location, not an application of the excluded equivalence.
- `w0n:formal-birkhoff` is re-derived in W3 and cited there as provenance; Duffing and its Lindstedt fact are consistency checks unused by the root proof.
- `w4:k0` and its steps are superseded by W7's separation result at the actual applications.
- `w7:melnikov` is unused by the current preparatory argument, which directly negates the unperturbed zone inequality. Its remaining citations are excluded interface remarks.

Cited substantive remarks `w1:kam-conventions`, `w3:class-remark`, `w6:to-w8`, `w7:exponents` and `w7:dioph-use` are represented. Excluded remarks retain administrative, comparison, provenance or pointer roles. No restoration or replacement node/EDGE block is required.

## Snapshot and exact checks

Read-only HEAD: `b4b274bed9195fee1a75dea336ce28382ca28a94`. Byte scope:

| Input | SHA-256 |
| --- | --- |
| W DEPGRAPH.md | `20d93bf152bef51c95147f0f4284c337829e69503968cfc334d723c3619ec433` |
| W DEPGRAPH_COVERAGE.md | `0d74f3a85ecd2ec72d94de51887dcd4a9be7a74f3f72dd34a33283239d72717f` |
| K DEPGRAPH.md | `f1acd9f62471ecb6305483bdf1c0514c866579ede9a9b659be5049ed5ab4e917` |
| K AMENDMENTS.md | `00574c82489f5c5dae8801ecc09ae3c25f4a7d9e4614384f9bebf3d6f6eb47de` |
| frozen-anchors.json | `674c73210fe8aeef703101ebe014dbc3e8569cb12f54a14dba1a7ff418d76aab` |

```text
sha256sum -c docs/graph/W/CORPUS.sha256
# exit 0; all eleven W source files: OK

sha256sum -c docs/graph/W/IMPORTS.sha256
# exit 0; blueprint/parts/p1-analysis.tex: OK

python3 -I /mnt/HC_Volume_106379410/orchestrator-tools/inp_depgraph_imports.py docs/graph/W/packets --slice W-imports --root . --owner K=blueprint --owner-graph K=docs/graph/K --self-track W
W-imports: 3 imported nodes present, 3 referenced, 0 missing, 0 unreferenced
# exit 0

python3 -I scripts/proof_depgraph.py --db docs/graph/K/DEPGRAPH.md --manifest docs/graph/K/DEPGRAPH_COVERAGE.md --source-root . --require-reviewed --require-complete-coverage --require-all-reachable --check
# exit 0; empty stdout and stderr

python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-reviewed --require-complete-coverage --require-initial-lean-status --require-all-reachable
# exit 1; empty stdout; exactly these two stderr lines:
docs/graph/W/DEPGRAPH.md:12: review gate: missing or placeholder GLOBAL_REVIEWER
docs/graph/W/DEPGRAPH.md:13: review gate: missing or placeholder GLOBAL_REVIEW_REF

python3 -I scripts/proof_depgraph.py --db docs/graph/W/DEPGRAPH.md --manifest docs/graph/W/DEPGRAPH_COVERAGE.md --source-root . --require-complete-coverage --require-initial-lean-status --require-all-reachable --check
# exit 0; empty stdout and stderr; current generated dashboard
```

Adding `--check` to W's command with `--require-reviewed` likewise reports exactly the two header placeholders and exits 1. Effective JSON comparisons return 12/12 equal import source fields. Whole-graph package scans find no missing direct package dependency; all 121 round-1 prescribed EDGE lines are present verbatim. The source corpus is unchanged from the round-1 reviewed snapshot; the current whole-graph review was nevertheless rerun.

Only `docs/graph/W/reviews/GLOBAL-review-2.md` is written. No Lean/Lake/build, source lint, state-changing git, dashboard generation, graph/packet/amendment edit, implementation/provider-file read or axiom probe was performed. Frozen declaration statements and definitions were the only Lean evidence used.

## Suspected blueprint defects and deviations

None newly established in the pinned blueprint. The Banach-target proof adaptation is explicitly owned by W and is not a new erratum. The brief now correctly counts 16 conjunct steps plus assembly. Existing P96-W/P96-K/KP96 source issues and the blueprint's declared repairs/deviations remain as documented in the pinned W parts; their original scanned papers were not independently re-audited in this source-graph review. No new deviation is introduced by this report.

## Unresolved questions

None. Global source-topology verdict: **PASS**. The orchestrator still supplies `GLOBAL_REVIEWER: sol-global-W` and `GLOBAL_REVIEW_REF: docs/graph/W/reviews/GLOBAL-review-2.md` and reruns the final reviewed gate; those authorized writer actions are outside this review's edit scope.
