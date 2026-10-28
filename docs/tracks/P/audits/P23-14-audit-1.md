# Independent audit P23-14 — audit 1

Overall: **PASS WITH NOTES** for the P23-14 infrastructure contract (`KamHyp`, `step`).
No mathematical or signature blocker found in the requested files. This is not a seal of
P-G/P-PLANAR/P-FIXED, a proof of `iterative`, or a campaign/root-closure verdict.
There is no frozen theorem/provider pair owned by this package; the frozen-provider seal
probe is therefore N/A, and the signature-based exact-type probe is the applicable gate.

| Contract / anchor | Verdict | Scope |
|---|---|---|
| `KamHyp` | PASS | Literal source-premise bundle, exact signature. |
| `step` | PASS WITH NOTES | Exact signature and proof closure; blueprint/root notes below. |
| Frozen physical headline anchors | N/A | No seal is supplied or certified by P23-14. |

## Snapshot and scope

- Worktree/report: `/root/code/KAM-inp-p2314/docs/tracks/P/audits/P23-14-audit-1.md`.
- HEAD: `cfa7c03e83ca8e01c6d86320768b4549ba9620ee`.
- Observed `inp`: `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`;
  `inp-p2312`: `303e22ecab09a50deb56f18a426d192eee849b83`.
- Read AGENTS, PLAN, DECISIONS, the independent audit brief, the complete handoff,
  track-P statement, revision-2 P23 design, design audits 1–2, the signature source,
  and blueprint-P `parts/p3a-two-scale-iteration.tex`, especially L22–62, L170–225.
- Reviewed only `KAM/Planetary/TwoScale/{Setting,Step*}.lean`: 17 files,
  104 explicitly named public declarations (97 theorems, six defs and one structure).
  Two private Schwarz support theorems were read and are included in module replay.
- Both requested triple-dot comparisons were inspected. Git warns
  `multiple merge bases, using 73df68628b999ea56e6874df4b859cb21cd6c63e` for `inp...HEAD`.
  Its 90-file diff includes unrelated inherited work. The package files are additions;
  the handoff's narrower `inp-p2312...HEAD` comparison also includes inherited work.
  Neither comparison authorizes auditing unrelated packages as P23-14.
- Only this report is a production edit by the auditor. The pre-existing untracked handoff
  is preserved. Temporary probes and evidence were confined to `.lake/abi-scratch/` and
  removed after incorporation into this report. No git mutation, root regeneration or fix.

## Exact statement and definition audit

The shared signature file is `/root/code/KAM-inp/.drafts/design/P23Signatures.lean`,
SHA256 `d067d47dbabfdf4913da3e2b76886eb29598f4502ad16318d328568d82380cd3`.
Literal comparisons (not normalized pretty-print comparisons) gave:

```text
realFreq EXACT_TEXT True
dioBase EXACT_TEXT True
omegaSet EXACT_TEXT True
KamHyp EXACT_TEXT True
step EXACT_TEXT True
```

For `step`, compare the entire declaration from `theorem step` through its conclusion,
excluding only `:= by ...` versus `:= sorry`. No signature fixture is imported by
production or by the proof probe. The untracked probe imported only the production
`KAM.Planetary.TwoScale.Step`, reproduced that exact type as `audit_exact_step`, and
used `by exact step H hD`. This checks the source-facing explicit application and all
implicit binders at default budgets. Exit 0.

All six new defs are literal formulas, not characterized choices:

| Definition | Classification and full-carrier behavior | Verdict |
|---|---|---|
| `realFreq` (Setting:29) | Real part of the complex gradient at real inclusion; no claim of reality off the guarded analytic domain. `freq_realInclusion_eq` proves agreement there. | PASS |
| `dioBase` (Setting:32) | Literal intersection/preimage of the two-scale Diophantine set. | PASS |
| `omegaSet` (Setting:36) | Literal frequency image intersected with that set. | PASS |
| `alpha₁` (StepNonres:198) | `(2/3)γ₁/K^τ`; actual uses prove K, γ₁ positive. | PASS |
| `alpha₂` (StepNonres:199) | `(2/3)γ₂/K^τ`; actual uses prove K, γ₂ positive. | PASS |
| `xval` (StepConst:28) | `E M² L/γ₁²`; actual log/division uses prove positivity. | PASS |
| `KamHyp` (Setting:42) | Literal source-premise structure, not a KAM-output bundle. Expanded below. | PASS |

For each row: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL;
CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS.
The scalar formulas use Lean's total arithmetic exactly as the design specifies;
there is no invented fallback branch or reliance on a value at a zero denominator.
The existential `ihat` is constructed from `ext_ift`; its values outside the stated
neighbourhood are not consumed. On the stated domain any two valid inverse values
coincide by `freq_inj`; no globally defined choice-based source object is introduced.

Semantic definitions checked at use: `freq` is `fderiv` applied to each coordinate unit;
`coefficientDom` is angle strip × frozen action tube, with coefficient radius divided
by `2π`; `InClass` is holomorphic plus period-one coordinate translations; `WBound`
includes summability and the weighted-series bound at every action point; `RealOn`
is vanishing imaginary part at real phase points. Frozen action tube and fast/slow
coordinate selections agree with these adapters. In particular the zero-coefficient
bound does not exploit a nonsummable `tsum` default.

## Expanded input audit

All rows below refer to the exact `step` at Step:33–88 / signature:643–698.
Source references: P3a means blueprint-P `parts/p3a-two-scale-iteration.tex`.
Rows count logical clauses, not bound point/vector variables inside quantified clauses.
Such inner point/vector/index binders are typing data for the displayed universal laws.
There are no instance parameters adding mathematical assumptions.

| Expanded input | Bin | Source / reason |
|---|---|---|
| `a` | TYPING | P3a:60, dimensions |
| `b` | TYPING | P3a:60, dimensions |
| `D` | TYPING | P3a:60, arbitrary real action set |
| `sbar` | TYPING | P3a:60, width data |
| `p` | TYPING | P3a:42–62, ScaleData numerical fields |
| `h` | TYPING | P3a:61, complex action Hamiltonian |
| `f` | TYPING | P3a:61, complex phase perturbation |
| `H.a_pos` | SOURCE | P3a:60, a ≥ 1 |
| `H.b_pos` | SOURCE | P3a:60, b ≥ 1 |
| `H.τ_gt` | SOURCE | P3a:60, τ > a+b |
| `H.positive: γ₂ > 0` | SOURCE | P3a:42,60,64, all numerical bounds positive |
| `H.positive: s > 0` | SOURCE | P3a:42,60,64, all numerical bounds positive |
| `H.positive: ρ > 0` | SOURCE | P3a:42,60,64, all numerical bounds positive |
| `H.positive: E > 0` | SOURCE | P3a:42,60,64, all numerical bounds positive |
| `H.positive: M > 0` | SOURCE | P3a:42,60,64, all numerical bounds positive |
| `H.positive: Mhat > 0` | SOURCE | P3a:42,60,64, all numerical bounds positive |
| `H.positive: Mbar > 0` | SOURCE | P3a:42,60,64, all numerical bounds positive |
| `H.positive: Mbar₁ > 0` | SOURCE | P3a:42,60,64, all numerical bounds positive |
| `H.positive: Mbar₂ > 0` | SOURCE | P3a:42,60,64, all numerical bounds positive |
| `H.gamma_order` | SOURCE | P3a:60, γ₂ ≤ γ₁ |
| `H.widths: 4s ≤ sbar` | SOURCE | P3a:60 |
| `H.widths: sbar < 1` | SOURCE | P3a:60 |
| `H.normalized: Mhat ≤ M` | SOURCE | P3a:65,91 |
| `H.normalized: Mbar₁ ≤ Mbar` | SOURCE | P3a:65,91 |
| `H.normalized: Mbar₂ ≤ Mbar` | SOURCE | P3a:65,91 |
| `H.L_bound` | SOURCE | P3a:175, L may be larger than initialL |
| `H.holo` | SOURCE | P3a:61, h holomorphic on Dρ |
| `H.real_h expanded RealOn` | SOURCE | P3a:61, h real at all real points in its phase domain |
| `H.real_f expanded RealOn` | SOURCE | P3a:61, f real at all real points in its phase domain |
| `H.f_class.differentiableOn` | SOURCE | P3a:61, f holomorphic on product domain |
| `H.f_class.periodic` | SOURCE | P3a:61, period-one translations |
| `H.f_bound: WSummable` | SOURCE | P3a:24–26,64, finite weighted Fourier series norm |
| `H.f_bound: wsum ≤ E` | SOURCE | P3a:24–26,64, uniform weighted bound |
| `H.injective` | SOURCE | P3a:62, injection on full Dρ |
| `H.hessian: operator norm ≤ M` | SOURCE | P3a:64, full derivative bound |
| `H.hessian: last-row bound ≤ Mhat` | SOURCE | P3a:32–33,64 |
| `H.hessian: existence of A and A = D(freq h)` | SOURCE | P3a:62, nonsingular Hessian as actual equivalence |
| `H.hessian: inverse norm ≤ Mbar` | SOURCE | P3a:64 |
| `H.hessian: first inverse rows ≤ Mbar₁` | SOURCE | P3a:32–33,64 |
| `H.hessian: last inverse rows ≤ Mbar₂` | SOURCE | P3a:32–33,64 |
| `H.small` | SOURCE | P3a:51,174, kamConstant·eHat < 1 |
| `hD: nonzero first block modes` | SOURCE | P3a:176 plus twoScaleDiophantine fast clause |
| `hD: zero first block, nonzero modes` | SOURCE | P3a:176 plus twoScaleDiophantine slow clause |

Counts for these expanded rows: SOURCE 36; TYPING 7; STANDING 0; RULED 0; EXCESS 0.
`H` is the collection of these premises, not an additional input; the full two-scale
Diophantine definition uses all integer modes with ℓ¹ mode size. Inner witnesses for the
inverse Hessian carry the explicit equivalence law, so nonsingularity is not inferred
from a norm bound alone. No theorem conclusion, shifted base, inverse image,
averaging result, next smallness condition or Lipschitz bound is a field of H.

Conditional helpers have visibly separate names. `inv_coord` takes the inverse laws
of its explicit map G, supplied by `ext_ift` in `ihat_exists`; `next_hyp` takes the
actual outputs of `avg` and the proved domain inclusion; `ihat_real` takes the map's
already-proved inverse equation and ball membership. These are internal composition
steps, not extra assumptions on `step` or replacements for its unconditional output.

## Proof and consumer checks

- Nonresonance: coordinate mean value on each real-centred ball inside Dρ, not on
  potentially nonconvex Dρ. Full M bounds the general mode; only last rows and Mhat
  enter when the first block vanishes. Subtract the ℓ¹-mode-size error from the
  real Diophantine divisor to obtain `(2/3)γᵢ/K^τ` on all D_R.
- `Step:94–95` calls P23-12 `avg (H.avgHyp hD) H.small_avg.1` with geometric widths
  equal to coefficient widths / `2π`. The holomorphic, real, periodic, symplectic,
  injective and image laws belong to this same Ψ. `Step:100–108` adds the proved
  zero-coefficient bound E to the averaging error E/4, obtaining 5E/4.
- Hessian: nested scalar/Banach Cauchy bounds give `‖D²g‖ ≤ 80E/R²`, stronger than
  P3a's `80nE/R²`. `beta_facts` proves the 1/100 margins. The perturbation inverse is
  `A⁻¹ (1+B A⁻¹)⁻¹`, preserving both inverse row estimates. All estimates hold on D_(R/4).
- Injectivity: P23-03 `ball` first brings a second preimage into a single convex ball;
  original injectivity identifies it; the derivative bound then forces equality.
  The proof does not assume a global inverse Lipschitz bound on a nonconvex domain.
- `ihat_exists` calls `ext_ift` on the proved open injectivity domain D_(R/8).
  P23-03 `ball` places ω₀(I) in the image for every I in D_(R/16).
  `inv_coord` integrates the actual inverse derivative row bound on an image ball;
  the separate block estimates do not follow by substituting the full inverse norm.
- `schwarz_scalar` proves reflection by the one-variable identity theorem, one coordinate
  at a time. `ihat_real` uses reflection of ω₊ and injectivity, not real-part projection
  as a substitute for the complex inverse. Thus Dp is an actual real inverse image;
  `dp_freq_image` gives equality of frequency images and the triangle inequality gives
  `(Dp)_(R/16) ⊆ D_(R/8)`.
- `next_hyp` assembles all fields from these results and the averaging fs. In particular
  `exp(-Ks/6) ≤ xval`, `E₊ = E*xval`, `initialL₊ ≤ 2L`, realness, periodicity and the
  new product-domain restriction are proved; next smallness is not assumed.
- P23-07 `lip_sup` is applied at Step:147 with radius R/16 and amplitude 10ÊR,
  giving exactly `4n·10ÊR/(R/16) = 640nÊ` on arbitrary D.
- `cutoff_next_le`, `rhoHat_next_ge`, `eHat_next_le`, `eHat_next_lt`, `small_next`
  establish K₊ ≤ 24K, R₊ ≥ R/(2·24^(τ+1)), the exact 8/9 quadratic bound,
  strict contraction and next smallness. Positive real-power bases are established
  before monotonicity, inversion and logarithm rewrites.
- G2 is paid at the design boundary: normalized bounds are inputs, all constants are
  computed from those inputs, and no pre-normalization cutoff/radius/error is retained.
  Upstream `Constants.rem_norm` has R nondecreasing, Ê nonincreasing with L fixed.
  P23-14 neither assumes nor re-proves the contrary blueprint sentence.
- G3 is paid by retaining the same Ψ on V = D_(R/2) × T_(sbar+s/6), with the
  conjugacy identity on the smaller next-stage domain. Proven neighbourhood and width
  inclusions justify the restriction; displacement properties still hold on V.

## Declaration ledger

Namespace prefix is `KAM.Planetary.` throughout, with `KamHyp.` retained where present.
Each row below is one explicitly named public declaration, with file:line and node.
PASS for a conditional helper means the stated internal implication is proved and its
premises are paid by the parent construction; it is not a standalone source theorem.

| Node | Declaration (file:line) | Verdict | Reason / note |
|---|---|---|---|
| `bpP:p3:conv#data; p3b#kam-bounds` | `realFreq` (Setting:29) | PASS | Literal definition; see body/carrier audit above. |
| `bpP:p3:conv#data; p3b#kam-bounds` | `dioBase` (Setting:32) | PASS | Literal definition; see body/carrier audit above. |
| `bpP:p3:conv#data; p3b#kam-bounds` | `omegaSet` (Setting:36) | PASS | Literal definition; see body/carrier audit above. |
| `bpP:p3:conv#data; p3b#kam-bounds` | `KamHyp` (Setting:42) | PASS | Literal definition; see body/carrier audit above. |
| `bpP:p3:step` | `step` (Step:33) | PASS | Exact signature; all joint witnesses supplied in the proof, no added premise. |
| `st-small; st-avg` | `inClass_mono_dom` (StepAvg:30) | PASS | Domain/width restriction, positive divisors and smallness proved from KamHyp; AvgHyp supplied to avg. |
| `st-small; st-avg` | `realOn_mono_dom` (StepAvg:35) | PASS | Domain/width restriction, positive divisors and smallness proved from KamHyp; AvgHyp supplied to avg. |
| `st-small; st-avg` | `KamHyp.alpha₂_pos` (StepAvg:40) | PASS | Domain/width restriction, positive divisors and smallness proved from KamHyp; AvgHyp supplied to avg. |
| `st-small; st-avg` | `KamHyp.alpha_le` (StepAvg:46) | PASS | Domain/width restriction, positive divisors and smallness proved from KamHyp; AvgHyp supplied to avg. |
| `st-small; st-avg` | `KamHyp.alpha₂_ge` (StepAvg:53) | PASS | Domain/width restriction, positive divisors and smallness proved from KamHyp; AvgHyp supplied to avg. |
| `st-small; st-avg` | `KamHyp.alpha₁_ge` (StepAvg:64) | PASS | Domain/width restriction, positive divisors and smallness proved from KamHyp; AvgHyp supplied to avg. |
| `st-small; st-avg` | `KamHyp.small_avg` (StepAvg:76) | PASS | Domain/width restriction, positive divisors and smallness proved from KamHyp; AvgHyp supplied to avg. |
| `st-small; st-avg` | `KamHyp.avgHyp` (StepAvg:114) | PASS | Domain/width restriction, positive divisors and smallness proved from KamHyp; AvgHyp supplied to avg. |
| `st-const; st-quad` | `xval` (StepConst:28) | PASS | Literal definition; see body/carrier audit above. |
| `st-const; st-quad` | `cutoff_eq` (StepConst:30) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `nextScale_s` (StepConst:32) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `nextScale_E` (StepConst:33) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `nextScale_M` (StepConst:35) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `nextScale_Mhat` (StepConst:36) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `nextScale_L` (StepConst:37) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `nextScale_γ₁` (StepConst:38) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `nextScale_γ₂` (StepConst:39) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `nextScale_τ` (StepConst:40) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `nextScale_ρ` (StepConst:41) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `xval_pos` (StepConst:43) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `xval_next` (StepConst:47) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `cutoff_next_le` (StepConst:51) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `rhoHat_eq` (StepConst:69) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `rhoHat_aux` (StepConst:73) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `rhoHat_next_ge` (StepConst:80) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `xval_le` (StepConst:111) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `eHat_pos` (StepConst:149) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `eHat_next_le` (StepConst:154) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `eHat_next_lt` (StepConst:189) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-const; st-quad` | `small_next` (StepConst:203) | PASS | Literal scale identities and guarded real-power/log estimates; exact 24, 8/9 and strict quadratic constants. |
| `st-disp` | `KamHyp.disp_first` (StepDisp:31) | PASS | Conditional arithmetic helper; input is the actual avg displacement clause, supplied at Step:156–159. |
| `st-disp` | `KamHyp.disp_last` (StepDisp:53) | PASS | Conditional arithmetic helper; input is the actual avg displacement clause, supplied at Step:156–159. |
| `st-disp` | `KamHyp.disp_theta` (StepDisp:73) | PASS | Conditional arithmetic helper; input is the actual avg displacement clause, supplied at Step:156–159. |
| `st-ihat` | `realInclusion_re` (StepDp:30) | PASS | Tube/image and real-inclusion helper; reality and inverse equations supplied at Step:109–130,137. |
| `st-ihat` | `dp_realInclusion` (StepDp:34) | PASS | Tube/image and real-inclusion helper; reality and inverse equations supplied at Step:109–130,137. |
| `st-ihat` | `dp_subset_tube` (StepDp:41) | PASS | Tube/image and real-inclusion helper; reality and inverse equations supplied at Step:109–130,137. |
| `st-ihat` | `dp_nbhd_subset` (StepDp:52) | PASS | Tube/image and real-inclusion helper; reality and inverse equations supplied at Step:109–130,137. |
| `st-ihat` | `dp_freq_image` (StepDp:64) | PASS | Tube/image and real-inclusion helper; reality and inverse equations supplied at Step:109–130,137. |
| `st-ihat` | `KamHyp.ihat_const` (StepDp:83) | PASS | Tube/image and real-inclusion helper; reality and inverse equations supplied at Step:109–130,137. |
| `st-nonres; ext-mvt` | `isOpen_actionNbhd'` (StepFreq:28) | PASS | Open tubes, real-frequency restriction and convex coordinate mean value; no global convexity assumed. |
| `st-nonres; ext-mvt` | `actionNbhd_mono` (StepFreq:32) | PASS | Open tubes, real-frequency restriction and convex coordinate mean value; no global convexity assumed. |
| `st-nonres; ext-mvt` | `mem_actionNbhd_of_mem` (StepFreq:36) | PASS | Open tubes, real-frequency restriction and convex coordinate mean value; no global convexity assumed. |
| `st-nonres; ext-mvt` | `actionNbhd_ball` (StepFreq:42) | PASS | Open tubes, real-frequency restriction and convex coordinate mean value; no global convexity assumed. |
| `st-nonres; ext-mvt` | `freq_im_zero` (StepFreq:49) | PASS | Open tubes, real-frequency restriction and convex coordinate mean value; no global convexity assumed. |
| `st-nonres; ext-mvt` | `freq_realInclusion_eq` (StepFreq:88) | PASS | Open tubes, real-frequency restriction and convex coordinate mean value; no global convexity assumed. |
| `st-nonres; ext-mvt` | `coord_mvt` (StepFreq:99) | PASS | Open tubes, real-frequency restriction and convex coordinate mean value; no global convexity assumed. |
| `st-dg; st-U` | `g_bounds` (StepHess:32) | PASS | Holomorphic Cauchy/operator estimates and additive derivative identities on their stated open domains. |
| `st-dg; st-U` | `freq_add` (StepHess:57) | PASS | Holomorphic Cauchy/operator estimates and additive derivative identities on their stated open domains. |
| `st-dg; st-U` | `fderiv_freq_add` (StepHess:65) | PASS | Holomorphic Cauchy/operator estimates and additive derivative identities on their stated open domains. |
| `st-dg; st-U` | `freq_g_fderiv` (StepHess:74) | PASS | Holomorphic Cauchy/operator estimates and additive derivative identities on their stated open domains. |
| `st-dg; st-U` | `KamHyp.beta_facts` (StepHess2:32) | PASS | Small perturbation from KamHyp; doubled forward/inverse and both inverse row bounds proved. |
| `st-dg; st-U` | `KamHyp.hessian_next` (StepHess2:62) | PASS | Small perturbation from KamHyp; doubled forward/inverse and both inverse row bounds proved. |
| `st-ihat` | `inv_coord` (StepIhat:31) | PASS | Conditional inverse-coordinate helper or constructed inverse; ball/ext_ift hypotheses supplied explicitly. |
| `st-ihat` | `KamHyp.ihat_exists` (StepIhat:70) | PASS | Conditional inverse-coordinate helper or constructed inverse; ball/ext_ift hypotheses supplied explicitly. |
| `st-inj` | `ball_subset_actionNbhd` (StepInj:30) | PASS | Cauchy then ball localization then contraction; arbitrary/nonconvex base allowed. |
| `st-inj` | `norm_freq_le` (StepInj:41) | PASS | Cauchy then ball localization then contraction; arbitrary/nonconvex base allowed. |
| `st-inj` | `KamHyp.g_deriv_bounds` (StepInj:52) | PASS | Cauchy then ball localization then contraction; arbitrary/nonconvex base allowed. |
| `st-inj` | `KamHyp.freq_g_le` (StepInj:65) | PASS | Cauchy then ball localization then contraction; arbitrary/nonconvex base allowed. |
| `st-inj` | `KamHyp.freq_g_lip` (StepInj:75) | PASS | Cauchy then ball localization then contraction; arbitrary/nonconvex base allowed. |
| `st-inj` | `KamHyp.freq_inj` (StepInj:99) | PASS | Cauchy then ball localization then contraction; arbitrary/nonconvex base allowed. |
| `st-avg; st-ihat` | `polyNbhd_realBase_subset` (StepMono:28) | PASS | Literal neighbourhood/class/series monotonicity; coeff-zero estimate uses actual summability. |
| `st-avg; st-ihat` | `dom_mono_set` (StepMono:33) | PASS | Literal neighbourhood/class/series monotonicity; coeff-zero estimate uses actual summability. |
| `st-avg; st-ihat` | `coefficientDom_mono` (StepMono:40) | PASS | Literal neighbourhood/class/series monotonicity; coeff-zero estimate uses actual summability. |
| `st-avg; st-ihat` | `wbound_mono_set` (StepMono:46) | PASS | Literal neighbourhood/class/series monotonicity; coeff-zero estimate uses actual summability. |
| `st-avg; st-ihat` | `inClass_mono_set` (StepMono:53) | PASS | Literal neighbourhood/class/series monotonicity; coeff-zero estimate uses actual summability. |
| `st-avg; st-ihat` | `norm_coeff_zero_le` (StepMono:59) | PASS | Literal neighbourhood/class/series monotonicity; coeff-zero estimate uses actual summability. |
| `st-avg; st-const; st-quad` | `KamHyp.exp_cutoff_le` (StepNext:31) | PASS | Averaging outputs and proved tube inclusion assemble every next KamHyp field; no new source premise. |
| `st-avg; st-const; st-quad` | `KamHyp.next_hyp` (StepNext:46) | PASS | Averaging outputs and proved tube inclusion assemble every next KamHyp field; no new source premise. |
| `constants; st-nonres` | `KamHyp.γ₁_pos` (StepNonres:32) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `KamHyp.τ_pos` (StepNonres:34) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `KamHyp.L_pos` (StepNonres:39) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `KamHyp.K_pos` (StepNonres:44) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `KamHyp.R_pos` (StepNonres:46) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `KamHyp.K_mul_s` (StepNonres:50) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `KamHyp.R_le_ρ` (StepNonres:59) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `KamHyp.R_le_γ₁` (StepNonres:62) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `KamHyp.R_le_γ₂` (StepNonres:72) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `KamHyp.eHat_eq` (StepNonres:82) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `KamHyp.eHat_nonneg` (StepNonres:84) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `KamHyp.E_le_Mhat` (StepNonres:90) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `KamHyp.E_le_M` (StepNonres:103) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `KamHyp.eHat_small` (StepNonres:115) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `modeSize_pos_of_ne` (StepNonres:126) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `dotC_block_le` (StepNonres:135) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `dotC_real` (StepNonres:149) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `freq_diff_bounds` (StepNonres:156) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `alpha₁` (StepNonres:198) | PASS | Literal definition; see body/carrier audit above. |
| `constants; st-nonres` | `alpha₂` (StepNonres:199) | PASS | Literal definition; see body/carrier audit above. |
| `constants; st-nonres` | `nonres_arith` (StepNonres:202) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `constants; st-nonres` | `twoDiv_of_kamHyp` (StepNonres:214) | PASS | Guarded scalar/mean-value/divisor arithmetic; full mode size and slow rows used in respective cases. |
| `st-U; ext-neumann` | `perturb_equiv` (StepPerturb:21) | PASS | Actual equivalence (1+B A⁻¹)A; inverse keeps A⁻¹ on the left, preserving row bounds. |
| `st-ihat` | `im_realInclusion_zero` (StepReal:32) | PASS | Realness from RealOn, Schwarz reflection and proved injectivity; supplied ihat equations come from ihat_exists. |
| `st-ihat` | `KamHyp.hp_realOn` (StepReal:46) | PASS | Realness from RealOn, Schwarz reflection and proved injectivity; supplied ihat equations come from ihat_exists. |
| `st-ihat` | `KamHyp.ihat_real` (StepReal:60) | PASS | Realness from RealOn, Schwarz reflection and proved injectivity; supplied ihat equations come from ihat_exists. |
| `st-ihat; ext-ift support` | `hasDerivAt_conj_conj` (StepSchwarz:36) | PASS | Independent conjugate derivative/coordinate identity theorem and scalar/vector reflection; no reflection premise assumed. |
| `st-ihat; ext-ift support` | `differentiableAt_conj_conj` (StepSchwarz:47) | PASS | Independent conjugate derivative/coordinate identity theorem and scalar/vector reflection; no reflection premise assumed. |
| `st-ihat; ext-ift support` | `polydisc_identity` (StepSchwarz:66) | PASS | Independent conjugate derivative/coordinate identity theorem and scalar/vector reflection; no reflection premise assumed. |
| `st-ihat; ext-ift support` | `schwarz_scalar` (StepSchwarz:125) | PASS | Independent conjugate derivative/coordinate identity theorem and scalar/vector reflection; no reflection premise assumed. |
| `st-ihat; ext-ift support` | `schwarz_vec` (StepSchwarz:179) | PASS | Independent conjugate derivative/coordinate identity theorem and scalar/vector reflection; no reflection premise assumed. |

## Independently run checks

All Lean/Lake/checker invocations were serial for this audit, with `LEAN_NUM_THREADS=1`
and `nice -n 5`, no resource-budget overrides. No clean/update/cache operation ran.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2314 KAM.Planetary.TwoScale.Step
```

Exit 0. Output starts `[inp-gate] slot 1 acquired 10:24:43 for KAM.Planetary.TwoScale.Step`
and ends `Build completed successfully (9159 jobs).` Replayed warnings: unused variable
`hm0`, deprecated `if_pos`/`if_neg`, deprecated `ContinuousLinearMap.add_apply`;
other replayed dependency warnings in Diophantine, Inverse, Finite. No build error.

2. Exact type and public axiom closure:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2314Audit.lean
```

Final run exit 0; 104 output lines, all of the form:

```text
'KAM.Planetary.step' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every declaration in the ledger was checked once with `#print axioms`; all 104
reported exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx` or project axiom.
The first probe-generation attempt stopped before writing its file (delimiter differed
between `:= sorry` and `:= by`); a subsequent probe had an auditor namespace-inventory
error only for `ihat_const`. Correcting that temporary inventory gave the clean final
run. No production statement/proof was altered to make a check pass.

3. Kernel replay, one invocation over all 17 modules:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.Setting KAM.Planetary.TwoScale.Step KAM.Planetary.TwoScale.StepAvg KAM.Planetary.TwoScale.StepConst KAM.Planetary.TwoScale.StepDisp KAM.Planetary.TwoScale.StepDp KAM.Planetary.TwoScale.StepFreq KAM.Planetary.TwoScale.StepHess KAM.Planetary.TwoScale.StepHess2 KAM.Planetary.TwoScale.StepIhat KAM.Planetary.TwoScale.StepInj KAM.Planetary.TwoScale.StepMono KAM.Planetary.TwoScale.StepNext KAM.Planetary.TwoScale.StepNonres KAM.Planetary.TwoScale.StepPerturb KAM.Planetary.TwoScale.StepReal KAM.Planetary.TwoScale.StepSchwarz
```

Exit 0. Complete stdout/stderr:

```text
replaying KAM.Planetary.TwoScale.StepSchwarz
replaying KAM.Planetary.TwoScale.StepReal
replaying KAM.Planetary.TwoScale.StepPerturb
replaying KAM.Planetary.TwoScale.StepNonres
replaying KAM.Planetary.TwoScale.StepNext
replaying KAM.Planetary.TwoScale.StepMono
replaying KAM.Planetary.TwoScale.StepInj
replaying KAM.Planetary.TwoScale.StepIhat
replaying KAM.Planetary.TwoScale.StepHess2
replaying KAM.Planetary.TwoScale.StepHess
replaying KAM.Planetary.TwoScale.StepFreq
replaying KAM.Planetary.TwoScale.StepDp
replaying KAM.Planetary.TwoScale.StepDisp
replaying KAM.Planetary.TwoScale.StepConst
replaying KAM.Planetary.TwoScale.StepAvg
replaying KAM.Planetary.TwoScale.Step
replaying KAM.Planetary.TwoScale.Setting
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the explicitly permitted stale generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (524 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No long-line, module, source escape, frozen-guard or ABI failure. Package source hygiene
passes; repository lint is PASS WITH EXPECTED ROOT NOTE, not a literal exit-0 run.

5. Scoped static checks: no forbidden proof token or `set_option`; no EuclideanSpace;
no line over 100 Unicode characters; max file length 267 lines (<1500); all 17 files
have copyright/module/public imports/module docstring/exposed public section.
`git diff --check inp...HEAD -- KAM/Planetary/TwoScale/Setting.lean 'KAM/Planetary/TwoScale/Step*.lean'`
exits 0 (only Git's multiple-merge-base warning). Final report whitespace check exits 0.

6. Import closure: 113 project modules reachable by source import traversal, no provider
and no frozen theorem module. The 12 frozen modules in that closure are definition
modules only; no DRAFT_SORRY theorem is reachable. All 12 reachable frozen definition entries were checked uniquely manifested and SEALED;
the full guard/ABI check is recorded in lint.

7. Protected paths:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

**Not empty**: KAM.lean has 32 added imports of inherited N/planetary packages.
Frozen files, manifest and README have no difference. This is an explicit exception to
an all-branch hygiene PASS, not a falsely reported empty diff. `git log inp-p2312..HEAD
-- KAM.lean` attributes the root changes to inherited regeneration commits `4dad814`,
`f390de8`, `f11c903`, `6e36995`; P23-14 commits touch only the scoped package files.
This audit does not approve those unrelated edits, and did not regenerate the root.

## Notes, errata and limitations

- **Known blueprint defect, G2, not a Lean defect:** P3a:91 says lowering Mhat
  `can increase $\hat\rho$ and $\hat E$` and `$L$ ... is unchanged`. With L fixed, increasing R
  decreases Ê = EL/R². Also if the original Mhat > M, `min(Mhat,M)=M`, and initialL
  is unchanged because it already contains `1/M`; that special normalization is
  covered by upstream rem_norm. Design revision 2, gap table G2, already records
  the corrected direction and requires compatible constants chosen first. The Lean
  package follows the correction; the original sentence remains misleading.
- **Known domain defect, G3:** P3a:180,186–187 describes Ψ₊ as a restricted map but then
  states its displacements on the larger domain. The exact signature and proof retain
  the original total Ψ with each domain explicit; design G3 already adopts this repair.
- **Stronger legitimate intermediate:** `StepHess.g_bounds` and `g_deriv_bounds` give
  dimension-free operator bounds 80E/R², versus P3a:208's weaker 80nE/R². This follows
  from the Banach-space Cauchy operator estimate, not an entrywise-to-operator omission.
  The action displacement from avg is 3E rather than P3a:204's 9E; final step constants
  remain exactly the prescribed ones. The angle bound still uses 9E.
- No new suspected pinned-CP10 erratum was established by this local blueprint/package
  audit. The two blueprint/design issues above are retained explicitly, not silently
  repaired. No deviations introduced by the auditor.
- Signature/blueprint proof closure for this package does not authorize sealing a
  physical headline or claiming iteration/limit/measure closure. External dependencies
  were checked at the actual call sites and through axiom/kernel closure; their source
  proofs were not re-audited as additional packages here.
