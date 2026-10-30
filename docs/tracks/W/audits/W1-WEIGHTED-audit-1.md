# W1-WEIGHTED independent audit 1

**Overall verdict: FAIL for exact source-faithful package acceptance.** The implemented estimates and derivative equivalences compile and have clean axiom closure. The prescribed lint also reports two prohibited overlong lines (F4). Two public definition carriers do not encode the source objects on their whole domains (F1, F2). The named Hamiltonian-field specialization is a valid conditional helper, but does not close the last sentence of `bpW:w1:coordinatewise` under differentiability alone (F3). No frozen anchor is supplied or sealed by this package; W-NLW2 remains DRAFT_SORRY.

## Scope, authority and frozen snapshot

- Worktree: `/root/code/KAM-inp-wpa`; report location follows the user, overriding the generic brief’s main-worktree output instruction.
- Snapshot: HEAD `84358bc976cd9bec31066690e8ed6e035dc334a0`; comparison branch `inp` = `003c5a3a04b09690bc03ab763b69e159641da2b4`. Initial working tree clean. Full `git diff inp...HEAD` reviewed, including generated roots and handoff.
- Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md` (including D41/D43), `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, handoff/AUDIT FOCUS, `docs/tracks/W/W-STATEMENTS.md`, frozen Wave definitions and literal nlw2 clause (4). The generic `docs/tracks/W/statement.md` does not exist; W-STATEMENTS and frozen files provide the statement authority. W-STATEMENTS retains a stale draft banner; D41 and manifest control freeze status.
- Tier 2 focused correspondence audit using lean-statement-audit and manuscript-audit. Acceptance criteria: complete declaration inventory, no extra source premises or semantic fallbacks, explicit consumer limitations, targeted build, all public theorem axioms, eight-module kernel replay, prescribed SLIM lint, protected-path checks. Findings were subjected to a separate adversarial pass and executable counterexamples where applicable.
- Permission envelope: report-only tracked edit; transient probes under `.lake/abi-scratch/`; no source repairs, commits, source-tree regeneration, provider/seal probes, or parallel Lean activity. All audit-launched Lean/Lake commands use `LEAN_NUM_THREADS=1`, `nice -n 5`, sequentially. Other sessions on the shared host are outside this audit’s control.

Snapshot SHA256 (frozen-v1):

| File | SHA256 |
|---|---|
| `KAM/Wave/Seq/Transport.lean` | `2cceb7d3384f76fd528094286395afe3d1b401a4a2804831219039c05ac76518` |
| `KAM/Wave/Seq/Multiplier.lean` | `c03934de60bc71731ca3ace11aa5a676635ee6bd3d255b5cb58870a1a226de81` |
| `KAM/Wave/Seq/Embed.lean` | `6eaa42593412fac7d1ff381cc1a2f1782bf0fa9f1c268c992fd2f10a3248a78c` |
| `KAM/Wave/Seq/Coordinatewise.lean` | `ee022ccf48825b73ce9cb55862a687d37f52169d21d524c683e28c56147f4ce8` |
| `KAM/Wave/Seq/Diag.lean` | `5c4cdfff9ba620d92fbf31f249aba200e04497b3bd36c7e5428cc77eabcffe27` |
| `KAM/Wave/Seq/Flow.lean` | `5d24be039a3fea6a96d31e40b4f7bf3e93ab5ec3709e6ccb3ae807181e3cb1f3` |
| `KAM/Wave/Seq/Linfty.lean` | `52bfa79389df5479a5545e5dd9747887c4b4ccbec4d2b94433645439718191c1` |
| `KAM/Wave/Seq/Tails.lean` | `fbeff0888343b3ed21c4daf5bccd56e8c43e7ceee1ca38fe43dc05c4fac58c64` |
| `blueprint-W/parts/w1-sequences.tex` | `32647bb0e4ebab844e3976e53b1e033a72d25de06dfab7c6c19c9199c6cff02b` |
| `docs/tracks/W/W-STATEMENTS.md` | `3e6e698a076606b9f79e2a48cced8a6c1728af818746e1f59e9b6f0bae00fc30` |

The shared `inp` ref advanced during the audit to `1316016668e558526520a7820d3f6c94afaa2d96`. Both comparisons have merge-base `fa002b432ee0a320a0c96c0654b083ce8bd3b00d`; a final byte-for-byte comparison of `git diff 003c5a3a04b09690bc03ab763b69e159641da2b4...HEAD` and `git diff inp...HEAD` succeeded (SHA256 `3a89ac8106168965d4af8a685dfa5d1cb9ff5d9f7215af1d9b294ad3925902f3`). Thus the audited patch is unchanged; final protected-path and diff-whitespace checks also passed. HEAD remained fixed.

All source line references below refer to this snapshot. The eight implementation files are entirely new versus inp.

## Findings and refutation

### F1 — FAIL: globally exported weighted norm has nonsummable fallback

`Transport.lean:69–74` defines `ellNormSq (a p : ℝ) (w : ℕ+ → K) : ℝ := ∑' j, (ellWeight a p j * ‖w j‖)^2`, then `ellNorm := Real.sqrt ...`, without `IsEll`. Source `w0-conventions.tex:51–58` defines the norm on the space of sequences for which the displayed series is finite; `w1-sequences.tex:30–37` transports that space.

Concrete counterexample: at `a=p=0`, let `w j = 1 : ℝ`. The series is `Σ 1` and is not summable. Mathlib’s real `tsum` returns zero, so `ellNorm 0 0 w = 0` although `w ≠ 0` and `¬ IsEll 0 0 w`. This is an invented off-source value of an exported function documented as a norm.

Refutation attempt: perhaps `IsEll` is an implicit/ambient premise, or the source authorizes a total real extension. Inspection shows neither; the explicit argument is any sequence. The executable zero-norm probe elaborates. Conversely, every current use in the eight modules is attached to `IsEll` or `coeffW`, and `isEll_coeffW` proves the latter membership. Thus no current estimate is refuted; the failure is public definition fidelity, not a false norm estimate on its valid domain. A source-facing norm on the membership carrier (or a distinctly named raw tsum helper) would resolve the issue without changing frozen files. Status: SURVIVED.

### F2 — FAIL: Lipschitz predicate omits the source codomain

`Linfty.lean:63–67` documents a map `Ω̃ : Π → ℓ^p_∞`, but accepts arbitrary sequence-valued `Ω` and requires only membership/bounds of pairwise differences. Source `w1-sequences.tex:257–261`: “A map ... on ... is L-Lipschitz (L ≥ 0) if ...”. The source first places each value in the weighted bounded-sequence space.

Counterexample: `p=0`, `L=0`, `Dom=Set.univ`, `Ω ξ j = (j : ℝ)`, independent of ξ. Every difference is zero; the Lean predicate holds, although no value is in `IsLinfty 0`. The predicate also has no nonnegativity condition on L (a negative L is admitted on singleton/empty domains).

Refutation attempt: treating this as a difference seminorm is mathematically consistent and matches the displayed difference inequality. It still does not certify the source’s map into ℓ∞ on its declared carrier. `isLinftyLipschitz_iff` characterizes precisely that weaker difference condition, not missing value membership. For the actual tails application the separate theorem `isLinfty_tildeOmegaSeq` supplies membership and the explicit constant is positive, so the spectral result remains valid. Recommended scope: retain a distinctly named difference predicate or bind source value membership and L ≥ 0 into the source-facing predicate. Status: SURVIVED.

### F3 — conditional helper is sound; actual X^w specialization remains unclosed

At `Coordinatewise.lean:60–70`, `frozen_invariance_iff` takes `v : WaveSpace`, `hv₁`, `hv₂`. The coefficient identities uniquely characterize any representative that exists, because `coeffW 1 0` is injective. They do not contain `DK`, the invariance equation, or an asserted derivative, so they are **not conclusion-shaped invariance premises**. The proof correctly uses the chain rule along `θ + t • ν`, coordinate functionals, derivative uniqueness and injectivity. The left side is exactly frozen nlw2 clause (4) at fixed I,θ, with ν already in the frozen time convention; no 2π factor is lost. The right side is the componentwise product equality for the inclusion E₁,₁ → E₁,₀. Pointwise `DifferentiableAt` suffices; this weakens the source’s global differentiability premise and therefore strengthens the theorem.

However, `v` is not literally `X^w(Kmap θ)`, and `hv₂` is not merely typing: supplying such an ℓ² representative proves a nonlinear weighted summability fact. Source `w1-sequences.tex:164–167` says “if ... X^w is the field of Proposition ... (v)”; that proposition (`:556–562`) constructs an analytic field on all WaveSpace with the stated coefficients. This package does not define that field or produce the nonlinear representative. It therefore proves the abstract equivalence conditional on a represented RHS, not the complete source specialization with exactly differentiability as the only mathematical premise beyond standing data.

Refutation attempt: `coeffW` injectivity gives uniqueness, but cannot give existence. Choosing v from DK would make its coefficient hypotheses the invariance conclusion itself; no such construction occurs in this code and it would not repair the missing field. The handoff explicitly defers cubic summability. W2 `w2-reconstruction.tex:227–228` uses the field interpretation only in a remark and says its proof uses the coordinate form; `:399–401` confirms that boundary. Thus this does not block the generic coordinatewise tool used by W2, but the last sentence of the node must remain PARTIAL until the actual hamfield producer is composed. Status: SURVIVED as a source-completion gap; refuted as an accusation of circular invariance hypotheses.

Expanded binder audit of `frozen_invariance_iff` against the **complete last-sentence claim**:

| Binder | Bin | Evidence / reason |
|---|---|
| implicit `m : ℝ` | TYPING | mass parameter |
| `hm : 0 < m` | STANDING | w1 opening / bpW:w0:mass |
| implicit `Kmap : (Fin 2 → ℝ) → WaveSpace` | TYPING | source torus map |
| implicit `θ : Fin 2 → ℝ` | TYPING | evaluation point |
| implicit `ν : Fin 2 → ℝ` | TYPING | torus frequency |
| `hK : DifferentiableAt ℝ Kmap θ` | SOURCE | w1:164, localized differentiability suffices |
| `v : WaveSpace` | EXCESS | a supplied field representative replaces the source’s constructed field |
| `hv₁ : coeffW 1 0 v.1 = ...` | EXCESS | characterization to be supplied by hamfield producer, not a source premise |
| `hv₂ : coeffW 1 0 v.2 = ...` | EXCESS | nonlinear representability not proved here |

Counts: SOURCE 1; STANDING 1; TYPING 4; RULED 0; EXCESS 3. For a separately designated conditional representative helper the final three inputs are legitimate interface data; they cannot count as closure of the actual X^w source result. No structure/class alias hides additional hypotheses here.

### F4 — FAIL: package-owned lint failures

The prescribed SLIM lint reports `Multiplier.lean:15:108` and `Multiplier.lean:70:101` under “Lean lines over 100 characters”. The lines are respectively the weightedDiagCLM docstring bullet and the `norm_diagCLM_le` declaration. `scripts/lint_sources.sh:120–123` sets `status=1` for these findings. They are in a new package file, not an inherited/generated-root issue, and the brief permits no exception for this. The handoff’s claimed exit 0 is not reproduced. Refutation attempt: checked Unicode character lengths and the URL/import exemptions in the linter; neither line is exempt. Status: SURVIVED. No repair applied.

## Source node ledger

| Node | Lean declarations | Verdict | Source comparison |
|---|---|---|---|
| transport | `coeffW`, `IsEll`, `tauLp`, `ellNormSq`, `ellNorm` | FAIL | exact positive-weight division/membership/transport; F1 on raw norm carrier |
| space (i) | inverse, linearity, norm and inner-product lemmas | PASS WITH NOTES | exact transport identities; no new weighted normed type required by realization table; separability omitted and explicitly unconsumed |
| space (ii–iv) | `coeffWCLM`, `norm_coeffW_le`, truncation convergence, frozen norm bridge | PASS | exact evaluation, j ≤ N truncations, max product norm |
| multiplier | `weightedDiagCLM`, bounds, lower bounds, unboundedness, representative | PASS | bound proof carries μ boundedness; no junk branch; M ≥ 0 follows by testing j=1 |
| embed (i–iii) | ratio bounds, `embedCLM`, coefficient identity, injection/composition | PASS | constants and source coefficients exact; real a,a′ generalization is valid; (ii) is norm/membership rather than a bundled CLM |
| coordinatewise general | `hasDerivAt_coeffW`, `hasDerivAt_coordinates_iff` | PASS | derivative witness hc is source differentiability with derivative named; exact equivalence |
| coordinatewise frozen last sentence | `frozen_invariance_iff` | PASS WITH NOTES as helper; FAIL as complete source closure | F3; actual hamfield composition absent |
| diag (i–ii) | `lamMul`, representative, sharp norm, inverse, unboundedness | PASS | all real r; norm (1+m)^(r/2) for r ≥ 0; ≤1 for r<0; opposite inverse follows by replacing r with −r |
| diag (iii) | `rotCLM`, norm/group/continuity | PASS | exp(−iλjt), isometry, inverse from group/zero, strong continuity |
| diag (iv) | `flowCLM`, norm conservation/bound, group, coordinate derivatives | PASS WITH NOTES | exact max-norm √2 bound; complex-coordinate conjugacy explicitly omitted |
| linfty | membership, transport, norm bound, difference predicate | FAIL for source-facing predicate | F2; bound and pointwise equivalence remain valid for their literal types |
| tails | `waveB`, `waveOmega`, `tildeOmegaSeq`, pointwise and sup/Lipschitz bounds | PASS WITH NOTES | exact constants, max norm on Fin 2 → ℝ; all positive j strengthens source j ≥ 3; zero-padding source-authorized; Assumption B packaging not supplied |

## Complete public declaration ledger

Every new public declaration is listed below (including arithmetic/application helpers); node-level details above control each row. PASS is scoped to the literal helper statement, not campaign closure. Prefix all names with `KAM.Wave.`.

| File:line / node | Declaration | Verdict | Reason |
|---|---|---|---|
| Transport:39 / transport/space | `ellWeight_pos` | PASS | Source identity, estimate, or supporting algebra |
| Transport:43 / transport/space | `ellWeight_ne_zero` | PASS | Source identity, estimate, or supporting algebra |
| Transport:46 / transport/space | `ellWeight_cast_ne_zero` | PASS | Source identity, estimate, or supporting algebra |
| Transport:49 / transport/space | `norm_ellWeight_cast` | PASS | Source identity, estimate, or supporting algebra |
| Transport:53 / transport/space | `lp_two_hasSum_sq` | PASS | Source identity, estimate, or supporting algebra |
| Transport:61 / transport/space | `coeffW` | PASS | Source formula / bounded construction |
| Transport:65 / transport/space | `IsEll` | PASS | Source formula / bounded construction |
| Transport:69 / transport/space | `ellNormSq` | FAIL | F1: nonsummable inputs accepted |
| Transport:73 / transport/space | `ellNorm` | FAIL | F1: nonsummable inputs accepted |
| Transport:77 / transport/space | `tauLp` | PASS | Source formula / bounded construction |
| Transport:80 / transport/space | `tauLp_apply` | PASS | Source identity, estimate, or supporting algebra |
| Transport:83 / transport/space | `coeffW_apply` | PASS | Source identity, estimate, or supporting algebra |
| Transport:87 / transport/space | `isEll_coeffW` | PASS | Source identity, estimate, or supporting algebra |
| Transport:97 / transport/space | `tauLp_coeffW` | PASS | Source identity, estimate, or supporting algebra |
| Transport:104 / transport/space | `coeffW_tauLp` | PASS | Source identity, estimate, or supporting algebra |
| Transport:110 / transport/space | `coeffW_injective` | PASS | Source identity, estimate, or supporting algebra |
| Transport:115 / transport/space | `coeffW_add` | PASS | Source identity, estimate, or supporting algebra |
| Transport:119 / transport/space | `coeffW_smul` | PASS | Source identity, estimate, or supporting algebra |
| Transport:123 / transport/space | `coeffW_neg` | PASS | Source identity, estimate, or supporting algebra |
| Transport:127 / transport/space | `coeffW_sub` | PASS | Source identity, estimate, or supporting algebra |
| Transport:132 / transport/space | `coeffWLinear` | PASS | Source formula / bounded construction |
| Transport:138 / transport/space | `norm_tauLp_sq` | PASS | Source identity, estimate, or supporting algebra |
| Transport:150 / transport/space | `ellNorm_coeffW` | PASS | Source identity, estimate, or supporting algebra |
| Transport:158 / transport/space | `inner_tauLp` | PASS | Source identity, estimate, or supporting algebra |
| Transport:167 / transport/space | `norm_coeffW_le` | PASS | Source identity, estimate, or supporting algebra |
| Transport:175 / transport/space | `coeffWCLM` | PASS | Source formula / bounded construction |
| Transport:178 / transport/space | `coeffWCLM_apply` | PASS | Source identity, estimate, or supporting algebra |
| Transport:184 / transport/space | `truncLp` | PASS | Source formula / bounded construction |
| Transport:188 / transport/space | `tendsto_norm_sub_truncLp` | PASS | Source identity, estimate, or supporting algebra |
| Transport:202 / transport/space | `coeffW_one_one` | PASS | Source identity, estimate, or supporting algebra |
| Transport:208 / transport/space | `norm_prod_eq_max_ellNorm` | PASS | Source identity, estimate, or supporting algebra |
| Multiplier:31 / multiplier/embed | `memℓp_diag` | PASS | Source identity, estimate, or supporting algebra |
| Multiplier:44 / multiplier/embed | `weightedDiagCLM` | PASS | Source formula / bounded construction |
| Multiplier:66 / multiplier/embed | `weightedDiagCLM_apply` | PASS | Source identity, estimate, or supporting algebra |
| Multiplier:70 / multiplier/embed | `norm_diagCLM_le` | PASS | Source identity, estimate, or supporting algebra |
| Multiplier:75 / multiplier/embed | `weightedDiagCLM_eq` | PASS | Source identity, estimate, or supporting algebra |
| Multiplier:79 / multiplier/embed | `norm_diagCLM_le'` | PASS | Source identity, estimate, or supporting algebra |
| Multiplier:84 / multiplier/embed | `norm_diagCLM_apply_of_norm_eq_one` | PASS | Source identity, estimate, or supporting algebra |
| Multiplier:92 / multiplier/embed | `norm_le_norm_of_apply_eq` | PASS | Source identity, estimate, or supporting algebra |
| Multiplier:106 / multiplier/embed | `norm_le_norm_diagCLM` | PASS | Source identity, estimate, or supporting algebra |
| Multiplier:111 / multiplier/embed | `not_exists_diag_of_unbounded` | PASS | Source identity, estimate, or supporting algebra |
| Multiplier:119 / multiplier/embed | `diag_representative` | PASS | Source identity, estimate, or supporting algebra |
| Multiplier:127 / multiplier/embed | `embedRatio` | PASS | Source formula / bounded construction |
| Multiplier:129 / multiplier/embed | `embedRatio_pos` | PASS | Source identity, estimate, or supporting algebra |
| Multiplier:132 / multiplier/embed | `embedRatio_eq` | PASS | Source identity, estimate, or supporting algebra |
| Multiplier:141 / multiplier/embed | `embedRatio_le_one` | PASS | Source identity, estimate, or supporting algebra |
| Multiplier:153 / multiplier/embed | `embedRatio_le_of_lt` | PASS | Source identity, estimate, or supporting algebra |
| Multiplier:184 / multiplier/embed | `isEll_coeffW_of_ratio_le` | PASS | Source identity, estimate, or supporting algebra |
| Embed:28 / embed | `norm_embedRatio_cast_le_one` | PASS | Source identity, estimate, or supporting algebra |
| Embed:35 / embed | `embedCLM` | PASS | Source formula / bounded construction |
| Embed:39 / embed | `embedCLM_apply` | PASS | Source identity, estimate, or supporting algebra |
| Embed:44 / embed | `norm_embedCLM_le` | PASS | Source identity, estimate, or supporting algebra |
| Embed:49 / embed | `ellNorm_coeffW_le_of_le` | PASS | Source identity, estimate, or supporting algebra |
| Embed:57 / embed | `ellNorm_coeffW_le_of_lt` | PASS | Source identity, estimate, or supporting algebra |
| Embed:65 / embed | `coeffW_embedCLM` | PASS | Source identity, estimate, or supporting algebra |
| Embed:74 / embed | `embedCLM_injective` | PASS | Source identity, estimate, or supporting algebra |
| Embed:80 / embed | `embedCLM_comp` | PASS | Source identity, estimate, or supporting algebra |
| Coordinatewise:32 / coordinatewise | `hasDerivAt_coeffW` | PASS | Source identity, estimate, or supporting algebra |
| Coordinatewise:41 / coordinatewise | `hasDerivAt_coordinates_iff` | PASS | Source identity, estimate, or supporting algebra |
| Coordinatewise:60 / coordinatewise | `frozen_invariance_iff` | CONDITIONAL | F3: unique representative supplied, not constructed |
| Diag:33 / diag (i–ii) | `pnat_le_lam` | PASS | Source identity, estimate, or supporting algebra |
| Diag:37 / diag (i–ii) | `lam_le_sqrt_mul` | PASS | Source identity, estimate, or supporting algebra |
| Diag:46 / diag (i–ii) | `one_le_lam_div_pnat` | PASS | Source identity, estimate, or supporting algebra |
| Diag:50 / diag (i–ii) | `lam_div_pnat_le` | PASS | Source identity, estimate, or supporting algebra |
| Diag:55 / diag (i–ii) | `lamRatio` | PASS | Source formula / bounded construction |
| Diag:57 / diag (i–ii) | `lamRatio_pos` | PASS | Source identity, estimate, or supporting algebra |
| Diag:60 / diag (i–ii) | `lamRatio_le_of_nonneg` | PASS | Source identity, estimate, or supporting algebra |
| Diag:68 / diag (i–ii) | `lamRatio_le_one_of_neg` | PASS | Source identity, estimate, or supporting algebra |
| Diag:71 / diag (i–ii) | `norm_lamRatio_cast_le` | PASS | Source identity, estimate, or supporting algebra |
| Diag:80 / diag (i–ii) | `lamMul` | PASS | Source formula / bounded construction |
| Diag:83 / diag (i–ii) | `lamMul_apply` | PASS | Source identity, estimate, or supporting algebra |
| Diag:88 / diag (i–ii) | `lamMul_represents` | PASS | Source identity, estimate, or supporting algebra |
| Diag:105 / diag (i–ii) | `norm_lamMul_le_of_nonneg` | PASS | Source identity, estimate, or supporting algebra |
| Diag:112 / diag (i–ii) | `norm_lamMul_le_of_neg` | PASS | Source identity, estimate, or supporting algebra |
| Diag:120 / diag (i–ii) | `norm_lamMul_eq` | PASS | Source identity, estimate, or supporting algebra |
| Diag:133 / diag (i–ii) | `lamMul_comp_neg` | PASS | Source identity, estimate, or supporting algebra |
| Diag:146 / diag (i–ii) | `not_exists_bounded_lam_pow` | PASS | Source identity, estimate, or supporting algebra |
| Flow:43 / diag (iii–iv) | `rotMu` | PASS | Source formula / bounded construction |
| Flow:46 / diag (iii–iv) | `norm_rotMu` | PASS | Source identity, estimate, or supporting algebra |
| Flow:49 / diag (iii–iv) | `continuous_rotMu` | PASS | Source identity, estimate, or supporting algebra |
| Flow:53 / diag (iii–iv) | `rotCLM` | PASS | Source formula / bounded construction |
| Flow:57 / diag (iii–iv) | `rotCLM_apply` | PASS | Source identity, estimate, or supporting algebra |
| Flow:61 / diag (iii–iv) | `norm_rotCLM` | PASS | Source identity, estimate, or supporting algebra |
| Flow:65 / diag (iii–iv) | `rotCLM_add` | PASS | Source identity, estimate, or supporting algebra |
| Flow:72 / diag (iii–iv) | `rotCLM_zero` | PASS | Source identity, estimate, or supporting algebra |
| Flow:76 / diag (iii–iv) | `continuous_rotCLM_apply` | PASS | Source identity, estimate, or supporting algebra |
| Flow:113 / diag (iii–iv) | `cosCLM` | PASS | Source formula / bounded construction |
| Flow:119 / diag (iii–iv) | `sinCLM` | PASS | Source formula / bounded construction |
| Flow:126 / diag (iii–iv) | `flowCLM` | PASS | Source formula / bounded construction |
| Flow:134 / diag (iii–iv) | `flowCLM_fst_apply` | PASS | Source identity, estimate, or supporting algebra |
| Flow:139 / diag (iii–iv) | `flowCLM_snd_apply` | PASS | Source identity, estimate, or supporting algebra |
| Flow:147 / diag (iii–iv) | `norm_sq_flowCLM` | PASS | Source identity, estimate, or supporting algebra |
| Flow:161 / diag (iii–iv) | `norm_flowCLM_apply_le` | PASS | Source identity, estimate, or supporting algebra |
| Flow:179 / diag (iii–iv) | `flowCLM_add` | PASS | Source identity, estimate, or supporting algebra |
| Flow:187 / diag (iii–iv) | `flowCLM_zero` | PASS | Source identity, estimate, or supporting algebra |
| Flow:192 / diag (iii–iv) | `hasDerivAt_flow_fst` | PASS | Source identity, estimate, or supporting algebra |
| Flow:202 / diag (iii–iv) | `hasDerivAt_flow_snd` | PASS | Source identity, estimate, or supporting algebra |
| Flow:212 / diag (iii–iv) | `coeffW_flow_fst` | PASS | Source identity, estimate, or supporting algebra |
| Flow:220 / diag (iii–iv) | `coeffW_flow_snd` | PASS | Source identity, estimate, or supporting algebra |
| Flow:229 / diag (iii–iv) | `hasDerivAt_coeffW_flow_fst` | PASS | Source identity, estimate, or supporting algebra |
| Flow:239 / diag (iii–iv) | `hasDerivAt_coeffW_flow_snd` | PASS | Source identity, estimate, or supporting algebra |
| Linfty:29 / linfty | `IsLinfty` | PASS | Source formula / bounded construction |
| Linfty:33 / linfty | `tauInfty` | PASS | Source formula / bounded construction |
| Linfty:36 / linfty | `tauInfty_apply` | PASS | Source identity, estimate, or supporting algebra |
| Linfty:39 / linfty | `rpow_pnat_pos` | PASS | Source identity, estimate, or supporting algebra |
| Linfty:43 / linfty | `norm_tauInfty_le_iff` | PASS | Source identity, estimate, or supporting algebra |
| Linfty:56 / linfty | `isLinfty_of_bound` | PASS | Source identity, estimate, or supporting algebra |
| Linfty:65 / linfty | `IsLinftyLipschitz` | FAIL | F2: differences only; values need not lie in source codomain |
| Linfty:70 / linfty | `isLinftyLipschitz_iff` | PASS WITH NOTES | Exact characterization of weaker difference predicate (F2) |
| Tails:32 / tails | `waveB` | PASS | Source formula / bounded construction |
| Tails:36 / tails | `waveOmega` | PASS | Source formula / bounded construction |
| Tails:40 / tails | `waveOmegaTilde` | PASS | Source formula / bounded construction |
| Tails:43 / tails | `tildeOmegaSeq` | PASS | Source formula / bounded construction |
| Tails:52 / tails | `lam_pnat_pos` | PASS | Source identity, estimate, or supporting algebra |
| Tails:55 / tails | `lam_sub_pnat_le` | PASS | Source identity, estimate, or supporting algebra |
| Tails:64 / tails | `lam_sub_pnat_pos` | PASS | Source identity, estimate, or supporting algebra |
| Tails:66 / tails | `waveB_sub` | PASS | Source identity, estimate, or supporting algebra |
| Tails:70 / tails | `abs_waveB_le` | PASS | Source identity, estimate, or supporting algebra |
| Tails:90 / tails | `tail_bound` | PASS | Source identity, estimate, or supporting algebra |
| Tails:117 / tails | `tail_lipschitz` | PASS | Source identity, estimate, or supporting algebra |
| Tails:138 / tails | `tail_gap` | PASS | Source identity, estimate, or supporting algebra |
| Tails:164 / tails | `isLinfty_tildeOmegaSeq` | PASS | Source identity, estimate, or supporting algebra |
| Tails:171 / tails | `norm_tildeOmegaSeq_le` | PASS | Source identity, estimate, or supporting algebra |
| Tails:181 / tails | `isLinftyLipschitz_tildeOmegaSeq` | PASS | Source identity, estimate, or supporting algebra |

## Definition classification (all 25 definitions; no new abbrev/structure)

| Definitions | Classification and whole-carrier check |
|---|---|
| `coeffW` | Literal division by positive ellWeight; whole lp carrier valid, arbitrary real weights remain positive. |
| `IsEll` | Literal weighted Memℓp predicate; correct for every sequence. |
| `ellNormSq`, `ellNorm` | Literal real tsum/sqrt code, but FAIL public norm carrier; F1. |
| `tauLp` | Literal weighted sequence bundled with its IsEll proof; no fallback. |
| `coeffWLinear`, `coeffWCLM` | Linear and continuous-linear coefficient formula; source intended operations on all lp inputs. |
| `truncLp` | Finset.image succPNat (range N) = {1,…,N}; finite sum, no missing endpoint. |
| `weightedDiagCLM` | Literal diagonal multiplication via mkContinuous; bound proof ensures square summability on all lp inputs; no conditional zero/default branch. Proof/M independence proved. |
| `embedRatio`, `embedCLM` | Exact positive weight ratio and bounded diagonal inclusion on the order-qualified carrier. |
| `lamRatio`, `lamMul` | Exact (λj/j)^r and bounded multiplier; m>0 explicit, every real r legitimate, all inputs valid. |
| `rotMu`, `rotCLM` | exp(−iλjt) and unit-modulus multiplier; no fallback. |
| `cosCLM`, `sinCLM`, `flowCLM` | Literal bounded trig multipliers and block rotation on the product lp carrier. |
| `IsLinfty`, `tauInfty` | Literal bounded weighted sequence predicate and proof-qualified transport. |
| `IsLinftyLipschitz` | FAIL source codomain/nonnegative-L carrier; literal difference seminorm is well defined (F2). |
| `waveB`, `waveOmega`, `waveOmegaTilde` | Fin 2 sum of ξi/λi+1, exact Ω and Ω−j formula. Formulas extend consistently to j=1,2 as intermediate helpers. |
| `tildeOmegaSeq` | Explicit if j≥3 then Ω−j else 0; this is the authorized normal-mode padding in blueprint :282–284, not a hidden fallback. |

For definitions other than F1/F2: BODY_MATCH OK; PUBLIC_CARRIER OK (real a generalization justified by positive weights); WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS. For `ellNormSq`/`ellNorm`: BODY_MATCH matches the formal finite-domain expression, PUBLIC_CARRIER FAIL, hence DEFINITION_VERDICT FAIL. For `IsLinftyLipschitz`: BODY_MATCH FAIL as the full source map predicate, PUBLIC_CARRIER FAIL, DEFINITION_VERDICT FAIL. All are explicit formulas or bounded bundles, not unique-witness constructions; no unproved choice or deferred well-definedness is used inside a definition.

## Deferred items and actual consumers

- Separability: source w1:144–148 explicitly says “Separability is not consumed by later milestones.” Search of W2/W3 and their dependency ledgers finds no use. The lp carrier already has the relevant Hilbert/completeness infrastructure; no new normed type is needed. This is an honestly declared omission, not a hidden W2/W3 premise.
- Complex conjugacy `L_t` ↔ `R_t` under z=(q+ip)/√2 is a genuine missing sentence of diag(iv), not proved by the separate group laws. W3 uses complex coordinates and nonlinear holomorphic Hamiltonian flows, but no explicit use of this particular real/complex *linear-flow conjugacy* was found. W3 :210–211 explicitly consumes diag(i), and :897 cites diag at node granularity; do not mark the entire diag source node complete. No current Lean consumer outside these eight files is present in this snapshot.
- The actual X^w producer is genuinely needed for the field interpretation in the W2 hidden-regularity remark; the W2 reconstruction proof says it uses only coordinates. W3 :218 also consumes hamfield for its own field construction. It belongs to a later W1 package, not something this audit can assume discharged.
- Assumption B: numerical decay and Lipschitz bounds supplied, including separate membership, suffice as quantitative ingredients; no packaged Assumption-B theorem or normal-index reindexing adapter is proved. W4, not W2/W3, is the relevant later consumer.

## Hygiene and independent verification

Verification results are recorded below. All 99 public theorem axiom probes were generated from the declaration inventory rather than only the handoff’s selected list. No provider is present and no production import of a provider/DRAFT_SORRY theorem occurs. The frozen nlw2 theorem was read as text, not imported into a probe.

Exact targeted build (exit 0; no warning output):

```sh
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpa KAM.Wave.Seq.Transport KAM.Wave.Seq.Multiplier KAM.Wave.Seq.Embed KAM.Wave.Seq.Coordinatewise KAM.Wave.Seq.Diag KAM.Wave.Seq.Flow KAM.Wave.Seq.Linfty KAM.Wave.Seq.Tails
```

```text
[inp-gate] slot 2 acquired 16:33:52 for KAM.Wave.Seq.Transport KAM.Wave.Seq.Multiplier KAM.Wave.Seq.Embed KAM.Wave.Seq.Coordinatewise KAM.Wave.Seq.Diag KAM.Wave.Seq.Flow KAM.Wave.Seq.Linfty KAM.Wave.Seq.Tails
Build completed successfully (2799 jobs).
```

The build wrapper itself runs `nice -n 5 lake build`. No clean or library rebuild was requested.

Kernel replay (exit 0):

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env sh -c 'LEAN_PATH="/root/code/KAM-inp-wpa/.lake/build/lib/lean:/root/code/KAM-inp/.lake/build/lib/lean:$LEAN_PATH" exec leanchecker --verbose KAM.Wave.Seq.Transport KAM.Wave.Seq.Multiplier KAM.Wave.Seq.Embed KAM.Wave.Seq.Coordinatewise KAM.Wave.Seq.Diag KAM.Wave.Seq.Flow KAM.Wave.Seq.Linfty KAM.Wave.Seq.Tails'
```

```text
replaying KAM.Wave.Seq.Tails
replaying KAM.Wave.Seq.Linfty
replaying KAM.Wave.Seq.Flow
replaying KAM.Wave.Seq.Diag
replaying KAM.Wave.Seq.Coordinatewise
replaying KAM.Wave.Seq.Embed
replaying KAM.Wave.Seq.Multiplier
replaying KAM.Wave.Seq.Transport
```

Setup correction: the first replay attempted a base-first `LEAN_PATH` and exited 1 with `object file '/root/code/KAM-inp/.lake/build/lib/lean/KAM/Wave/Seq/Tails.olean' ... does not exist`. This was a path-precedence error, not a kernel rejection; it finished before the corrected invocation. The successful run above places this worktree’s artifacts first, then supplies the main worktree’s frozen artifacts. None of these eight module oleans exists in the main build directory, so the replayed package artifacts are from this worktree.

Public axioms plus counterexample/uniqueness probes (final exit 0, no errors/warnings):

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env sh -c 'LEAN_PATH="/root/code/KAM-inp-wpa/.lake/build/lib/lean:/root/code/KAM-inp/.lake/build/lib/lean:$LEAN_PATH" exec lean .lake/abi-scratch/WpaAudit.lean'
```

The scratch file imports the eight modules and emits `#print axioms KAM.Wave.<name>` for every theorem in the complete public ledger. All **99** outputs are exactly the standard axiom set `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, project axiom or extra constant occurs. Full output:

```text
'KAM.Wave.ellWeight_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.ellWeight_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.ellWeight_cast_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_ellWeight_cast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lp_two_hasSum_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tauLp_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.coeffW_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.isEll_coeffW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tauLp_coeffW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.coeffW_tauLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.coeffW_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.coeffW_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.coeffW_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.coeffW_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.coeffW_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_tauLp_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.ellNorm_coeffW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.inner_tauLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_coeffW_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.coeffWCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tendsto_norm_sub_truncLp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.coeffW_one_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_prod_eq_max_ellNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.memℓp_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.weightedDiagCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_diagCLM_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.weightedDiagCLM_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_diagCLM_le'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_diagCLM_apply_of_norm_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_le_norm_of_apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_le_norm_diagCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.not_exists_diag_of_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.diag_representative' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.embedRatio_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.embedRatio_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.embedRatio_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.embedRatio_le_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.isEll_coeffW_of_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_embedRatio_cast_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.embedCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_embedCLM_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.ellNorm_coeffW_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.ellNorm_coeffW_le_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.coeffW_embedCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.embedCLM_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.embedCLM_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_coeffW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_coordinates_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.frozen_invariance_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.pnat_le_lam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lam_le_sqrt_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.one_le_lam_div_pnat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lam_div_pnat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamRatio_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamRatio_le_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamRatio_le_one_of_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_lamRatio_cast_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamMul_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamMul_represents' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_lamMul_le_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_lamMul_le_of_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_lamMul_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lamMul_comp_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.not_exists_bounded_lam_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_rotMu' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.continuous_rotMu' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.rotCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_rotCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.rotCLM_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.rotCLM_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.continuous_rotCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.flowCLM_fst_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.flowCLM_snd_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_sq_flowCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_flowCLM_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.flowCLM_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.flowCLM_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_flow_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_flow_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.coeffW_flow_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.coeffW_flow_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_coeffW_flow_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_coeffW_flow_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tauInfty_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.rpow_pnat_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_tauInfty_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.isLinfty_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.isLinftyLipschitz_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lam_pnat_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lam_sub_pnat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lam_sub_pnat_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.waveB_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.abs_waveB_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tail_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.tail_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.isLinfty_tildeOmegaSeq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_tildeOmegaSeq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.isLinftyLipschitz_tildeOmegaSeq' depends on axioms: [propext, Classical.choice, Quot.sound]
```

After those print commands, the following additional probes all elaborate (no output). The first exploratory version of the last proof failed only to simplify `|↑n+1|`; the final version below supplies the nonnegativity rewrite explicitly and exits 0. These are independent counterexample witnesses, not implementation edits.

```lean
-- Counterexample: the globally exported alleged norm vanishes on a nonzero constant sequence.
example : ellNorm 0 0 (fun _ : ℕ+ => (1 : ℝ)) = 0 := by
  have hn : ¬ Summable (fun _ : ℕ+ => (1 : ℝ)) := by simp [summable_const_iff]
  simp [ellNorm, ellNormSq, ellWeight, tsum_eq_zero_of_not_summable hn]

-- The Lipschitz predicate admits a constant map with an unbounded value.
example : IsLinftyLipschitz 0 0 Set.univ (fun _ j => (j : ℝ)) := by
  intro ξ hξ ζ hζ
  have h : IsLinfty 0 (fun _ : ℕ+ => (0 : ℝ)) := isLinfty_of_bound 0 _ (C := 0) (by simp)
  refine ⟨by simpa using h, ?_⟩
  apply (norm_tauInfty_le_iff _ _ _ (by simp)).2
  simp

-- The representative, if supplied, is unique; coefficient equations do not constrain DK.
example (v w : WaveSpace)
    (h1 : coeffW 1 0 v.1 = coeffW 1 0 w.1)
    (h2 : coeffW 1 0 v.2 = coeffW 1 0 w.2) : v = w :=
  Prod.ext (coeffW_injective 1 0 h1) (coeffW_injective 1 0 h2)

example : ¬ IsEll 0 0 (fun _ : ℕ+ => (1 : ℝ)) := by
  unfold IsEll
  rw [memℓp_gen_iff (by norm_num)]
  simpa [ellWeight] using (show ¬ Summable (fun _ : ℕ+ => (1 : ℝ)) by simp [summable_const_iff])

example : ¬ IsLinfty 0 (fun j : ℕ+ => (j : ℝ)) := by
  intro h
  obtain ⟨C, hC⟩ := (memℓp_infty_iff.1 h)
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hb := hC (Set.mem_range_self n.succPNat)
  have hb2 : |(n : ℝ) + 1| ≤ C := by simpa [Real.norm_eq_abs] using hb
  rw [abs_of_nonneg (by positivity)] at hb2
  linarith
```

Prescribed SLIM lint (exit **1**, attributable to F4; not a passing run):

```sh
env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpa
```

```text
Lean lines over 100 characters:
/root/code/KAM-inp-wpa/KAM/Wave/Seq/Multiplier.lean:15:108
/root/code/KAM-inp-wpa/KAM/Wave/Seq/Multiplier.lean:70:101
check_lean_modules: PASS (1636 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

The wrapper invokes `nice -n 5 sh scripts/lint_sources.sh` with a temporary combined build overlay. Root generation check and errata rendering check emit no complaint. The 100-character errors are substantive lint failures under this brief; they are not covered by the generic allowance for an out-of-date generated root.

Other checks:

```sh
git diff inp...HEAD -- KAM/Frozen manifest README.md    # empty, exit 0
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
# nonempty: the one added root import; see generated-root deviation below
git diff --check inp...HEAD                           # empty, exit 0
rg -n 'sorry|admit|axiom|unsafe|opaque|set_option|EuclideanSpace|KAM.Provider|KAM.Frozen.*Theorems' KAM/Wave/Seq
# no matches, exit 1 (successful absence check)
wc -l KAM/Wave/Seq/*.lean
```

```text
91 Coordinatewise.lean
161 Diag.lean
92 Embed.lean
250 Flow.lean
85 Linfty.lean
208 Multiplier.lean
197 Tails.lean
214 Transport.lean
1298 total
```

All eight modules have copyright, module command, public interface imports, module docstring and an `@[expose] public noncomputable section`. No resource overrides or forbidden proof escapes were introduced. Frozen definitions imported by the package are manifest SEALED; no theorem anchor is imported. Frozen-anchor guard and all 158 ABI hashes pass as above. Final cleanup removes the audit scratch files after recording their complete relevant contents here; final git status contains only this report, and `git diff --check` is clean.


## Source defects, deviations, and closeout

No new mathematical defect in the pinned blueprint or frozen theorem was established in the audited range. Bounds holding for all j≥1 strengthen the source’s j≥3 statement; they are not errata. The PNat zero padding is explicitly prescribed, not a source mistake. The discrepancies F1/F2 are implementation deviations, and F3 is a declared partial implementation. The handoff says files are “<=245 lines each”, but Flow has 250 physical lines; all remain far below the 1500-line hard cap.

Generated-root deviation: `git diff inp...HEAD -- KAM.lean KAM/Root/Wave.lean` adds a Wave root import and a generated 24-line part. These are acknowledged in the handoff but conflict with the blanket no-edit rule absent an orchestrator exception. AUDIT FOCUS specifically narrows the required empty protected comparison to `KAM/Frozen manifest README.md`, which passes; the broader generic comparison including KAM.lean is nonempty. This report records both facts, without silently waiving the general rule or modifying generated files.

Decision log: user’s exact report path and serial resource limit govern; handoff’s explicit no-provider/no-seal and SLIM lint instructions govern; existing source has not been repaired. Rejected possible findings: no missing 2π factor in invariance; no junk branch in weightedDiagCLM; no circular DK premise in hv₁/hv₂; no hidden need to create a new weighted Hilbert type. Findings remain separated from proposed remedies.

Closeout: source/declaration inventory complete; definition and binder boundaries explicit; independent build/axiom/kernel/lint results below; no claim to seal W-NLW2 or close all of W1/W2/W3. Required next work is public-carrier repair for F1/F2 and an actual hamfield producer/composition before upgrading the complete coordinatewise node. No source or frozen-file edits authorized or performed.
