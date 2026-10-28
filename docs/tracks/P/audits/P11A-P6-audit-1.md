# P11A-P6 independent audit 1

Overall verdict: **PASS WITH NOTES** for the requested six-file package. The five required theorems and literal averaging definition match their supplied signatures exactly. No extra premise, weakened required conclusion, hidden proof assumption, or invalid definition was found. Notes concern proof-plan/graph coverage, the external e5 node's broader scope, and inherited generated-root differences. This is a helper-package audit: **no frozen theorem anchor is sealed or certified seal-ready here**.

## Scope, permission envelope, and snapshot v1

Independent tier-2, refute-first audit on 2026-10-28. Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the handoff, P track statement, P11A design and all three design audits. The user's exact report destination overrides the generic brief's MAIN-worktree destination. Only this report is a repository edit; transient probes/logs are confined to this worktree's `.lake/abi-scratch/` and removed after recording results. No git mutation, generated-root regeneration, source repair, or delegation.

Audited HEAD: `d5326c497bbc15b501333733dbc5b9b2c45554c5`. Initial `inp`: `e1debc687b5a98ac89399ede04ff471835ab5708`. `git diff inp...HEAD` warns `multiple merge bases`, selecting `2d6d15803d4396fa335918fd31e6762008f40607`; the other merge base is `31f0bfbf70c07b1eefd006237f331c00e003a0e5`. That selected comparison adds precisely the six scoped PolarAverage files, while its full 51-file diff also includes inherited unrelated changes. No audit claim covers those other packages.

Frozen-v1 SHA-256 manifest (paths abbreviated relative to `KAM/Planetary/Preparation/`):

| File | Lines | SHA-256 |
|---|---:|---|
| `PolarAverage.lean` | 334 | `7fd32b1eda4879aa136bf221e36c8a2bf069dddaf32b0ece4724927bad227d83` |
| `PolarAverage/EvenDescent.lean` | 169 | `1668e39486bfc78070cba08c99fd76dda8c341bf7c147cf5940fd4d681e58d9d` |
| `PolarAverage/Iterate.lean` | 196 | `b03b8927e6d7e7cee65ee8fed0541389e0e8233326bffa12e6811f40baf503e1` |
| `PolarAverage/Order.lean` | 139 | `e9fb05c865f6a7fad5adfa41c0f20f8f48936e90f3ec2e754fc549c5e4db5056` |
| `PolarAverage/ParamIntegral.lean` | 100 | `b5a5e545e6c17b8dc5040d6985e6cd97edcf5140cffb532eb4b35bd786779548` |
| `PolarAverage/Torus.lean` | 221 | `1bb30bb93df3d0e06018c8b23b14008b411adc7ea30124789633bbac92a05e40` |

Other pinned inputs:

| Input | SHA-256 |
|---|---|
| `docs/tracks/P/design/P11A-LEAN-DESIGN.md` | `8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9` |
| `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` | `36f4f5b6da43859e9008cb3e1e0a611d926146805a63b4420de6e1fb540a3d1b` |
| `blueprint-P/parts/p11-cp09-preparation.tex` | `4c0e2dfefb50b1e06581e069a55846d25e0e4697a8826514ac699bbb83efb41f` |
| `docs/tracks/P/audits/P11A-P6-handoff.md` | `ec445f5d248720d2dfa11cb0c71ce3f5564325b56870e3bc8cde8384f10672f2` |
| `docs/tracks/P/design/DESIGN-P11A-design-audit-1.md` | `987cb366ade135712e1752d113c62ea8d3ca8010e5543460d5ac188fa82dd72b` |
| `docs/tracks/P/design/DESIGN-P11A-design-audit-2.md` | `86e4dce2f0f0ee8f2c36bd51d0e3ac6a43f5d03ba1d51957472fa768ade2f1ac` |
| `docs/tracks/P/design/DESIGN-P11A-design-audit-3.md` | `639790feaf17d36953f4e4baa157cdfcda61efe3f7f359b121ebd4a8754350d3` |

The signature file is absent locally; the above explicit MAIN-worktree copy was read without modifying it. MAIN HEAD at inspection was `edcbb41e1257f22557319e7e7038488867953a93`; the file hash, rather than that moving branch, pins the untracked signature. The design reports live under `design/`, not `audits/`. Their earlier draft elaboration receipts are not used as proof evidence.

## Statement ledger

All names below have namespace `KAM.Planetary`. Each row represents one public declaration; all 48 were inspected (41 theorems, seven definitions). Helper premises are local analytic/typing hypotheses of the stated helper, supplied at their use sites; they are not additional premises of `polar_avg`. `PA` denotes bpP:p11:polar-avg; `ED` denotes the alternative even-descent proof of PA. File/line anchors refer to snapshot v1.

| Node / role | Lean declaration and location | Verdict | Reason / note |
|---|---|---|---|
| bpP:p11:e5 | `e5` — `PolarAverage.lean:41` | PASS | Exact parity component of bpP:p11:e5; reflections on a period. Full external node is broader (N2). |
| PA / literal object | `p11PolarAverage` — `PolarAverage.lean:69` | PASS | Exact literal principal-root torus integral, including 1/pi. |
| ED / PA helper | `p11_torusAverage_const` — `PolarAverage.lean:75` | PASS | Unit-cube volume is one, including n=0. |
| ED / PA helper | `p11_torusAverage_lin` — `PolarAverage.lean:81` | PASS | Continuous inputs supply integrability before integral_add. |
| ED / PA helper | `p11_norm_sqrt_eq` — `PolarAverage.lean:90` | PASS | Nonnegative square-root norm identity. |
| PA / literal object | `p11Rad` — `PolarAverage.lean:94` | PASS | Literal coordinatewise sqrt(rho/pi). |
| ED / PA helper | `p11_rad_norm_le` — `PolarAverage.lean:96` | PASS | Pi max norm and monotonicity of real sqrt. |
| ED / PA helper | `p11_rad_norm_lt` — `PolarAverage.lean:102` | PASS | Positive radius and strict action-disc bound. |
| ED / PA helper | `p11PolarAverage_eq` — `PolarAverage.lean:108` | PASS | Definitional equality with radial-variable average. |
| ED / PA helper | `p11PolarAverage_differentiableOn` — `PolarAverage.lean:112` | PASS | Stronger radius pi*r^2; positive-pi linear rescaling after descent. |
| ED / PA helper | `p11PolarAverage_norm_le_pow` — `PolarAverage.lean:135` | PASS | Schwarz in phase product, then norm of torus mean. |
| PA (a)-(c) | `polar_avg` — `PolarAverage.lean:156` | PASS | Exact (a)-(c), fixed witness raw average; k=0 and rho=0 treated. |
| PA (d)/uniqueness | `polar_average_linear` — `PolarAverage.lean:249` | PASS | Exact companion for (d); proves integrability locally. |
| PA (d)/uniqueness | `polar_average_normalization` — `PolarAverage.lean:272` | PASS | Exact constant and quadratic identities, rho_i/(2*pi). |
| PA (d)/uniqueness | `polar_extension_unique` — `PolarAverage.lean:298` | PASS | Exact fibrewise identity theorem; no connectedness of D required. |
| ED / PA helper | `p11_sqrt_sq` — `PolarAverage/EvenDescent.lean:31` | PASS | Principal complex square root squares to its input globally. |
| ED / PA helper | `p11_norm_sqrt_sq` — `PolarAverage/EvenDescent.lean:34` | PASS | Norm of square-root square. |
| ED / PA helper | `p11_circle_descent` — `PolarAverage/EvenDescent.lean:38` | PASS | Cauchy kernel partial fractions, both poles inside circle. |
| ED / PA helper | `p11_even_descent` — `PolarAverage/EvenDescent.lean:92` | PASS | Local contour radius strictly between sqrt(norm u) and R; no branch premise. |
| PA / literal object | `p11Vj` — `PolarAverage/Iterate.lean:33` | PASS | Literal first-j-coordinate substitution; branches are intended finite-stage cases. |
| PA / literal object | `p11Wj` — `PolarAverage/Iterate.lean:37` | PASS | Literal mixed-radius domain at stage j. |
| PA / literal object | `p11Oj` — `PolarAverage/Iterate.lean:41` | PASS | Literal parameter domain omitting current coordinate. |
| ED / PA helper | `p11_isOpen_Wj` — `PolarAverage/Iterate.lean:44` | PASS | Finite intersection of open coordinate constraints. |
| ED / PA helper | `p11_isOpen_Oj` — `PolarAverage/Iterate.lean:53` | PASS | Free current coordinate; finite intersection remains open. |
| ED / PA helper | `p11_norm_sqrt_lt` — `PolarAverage/Iterate.lean:65` | PASS | Strict norm comparison with nonnegative r. |
| ED / PA helper | `p11_norm_Vj_lt` — `PolarAverage/Iterate.lean:69` | PASS | Each transformed coordinate stays within r. |
| ED / PA helper | `p11Vj_update` — `PolarAverage/Iterate.lean:79` | PASS | Current coordinate is unprocessed at stage j. |
| ED / PA helper | `p11Vj_succ` — `PolarAverage/Iterate.lean:86` | PASS | Exactly one further square-root substitution. |
| ED / PA helper | `p11PolarW_sqrt_differentiableOn` — `PolarAverage/Iterate.lean:97` | PASS | Induction through every coordinate; evenness supplied by torus shift. |
| ED / PA helper | `p11_iterate_dslope_coeff` — `PolarAverage/Order.lean:29` | PASS | Factorial/Taylor coefficient identity at zero. |
| ED / PA helper | `p11_differentiableOn_iterate_dslope` — `PolarAverage/Order.lean:40` | PASS | Analytic removable divided difference, iterated. |
| ED / PA helper | `p11_vanish_of_decay` — `PolarAverage/Order.lean:51` | PASS | Least nonzero Taylor order contradicts positive-real sqrt(t)^k decay. |
| ED / PA helper | `p11_radial_schwarz_gen` — `PolarAverage/Order.lean:100` | PASS | Finite-dimensional product-space adaptation; full jets become line derivatives. |
| ED / PA helper | `p11_differentiableOn_paramIntegral` — `PolarAverage/ParamIntegral.lean:31` | PASS | Compact-domain derivative bound and dominated differentiation; no integral conclusion assumed. |
| PA / literal object | `p11PolarPt` — `PolarAverage/Torus.lean:31` | PASS | Literal complex sin/cos polar map. |
| PA / literal object | `p11PolarW` — `PolarAverage/Torus.lean:36` | PASS | Literal unit-torus integral in radial variables. |
| ED / PA helper | `p11_norm_sin_le` — `PolarAverage/Torus.lean:39` | PASS | Only real angle is assumed, so bound one is valid. |
| ED / PA helper | `p11_norm_cos_le` — `PolarAverage/Torus.lean:44` | PASS | Only real angle is assumed, so bound one is valid. |
| ED / PA helper | `p11_norm_polarPt_le` — `PolarAverage/Torus.lean:49` | PASS | Product/Pi max norm, real-angle trigonometric bounds. |
| ED / PA helper | `p11_polarPt_mem_ball` — `PolarAverage/Torus.lean:64` | PASS | Image remains in phase ball. |
| ED / PA helper | `p11_continuous_polarPt` — `PolarAverage/Torus.lean:69` | PASS | Continuous real-angle integrand map. |
| ED / PA helper | `p11_continuous_polar_integrand` — `PolarAverage/Torus.lean:74` | PASS | Holomorphic G restricted to image in its domain. |
| ED / PA helper | `p11PolarW_differentiableOn` — `PolarAverage/Torus.lean:83` | PASS | Parameter integral over compact real cube; complex angles only used locally. |
| ED / PA helper | `p11_insertNth_add` — `PolarAverage/Torus.lean:104` | PASS | Coordinate insertion/translation identity. |
| ED / PA helper | `p11_torusAverage_eq_iterated` — `PolarAverage/Torus.lean:113` | PASS | Measure-preserving coordinate permutation plus integrable Fubini. |
| ED / PA helper | `p11_torusAverage_shift` — `PolarAverage/Torus.lean:134` | PASS | Periodicity and continuous-integrand integration over one period. |
| ED / PA helper | `p11PolarPt_update_neg` — `PolarAverage/Torus.lean:160` | PASS | Half-period shift flips sine and cosine together. |
| ED / PA helper | `p11PolarW_even` — `PolarAverage/Torus.lean:189` | PASS | Half-period invariance supplies evenness; no evenness premise on G. |

## Binder and semantic checks

Mechanical comparison of the text from each declaration command through its type, before `:=`, returned `HEADER_BYTE_EQUAL True` for `e5`, `p11PolarAverage`, `polar_avg`, `polar_average_linear`, `polar_average_normalization`, and `polar_extension_unique`. The entire `p11PolarAverage` definition body also returned `BODY_BYTE_EQUAL True`. Thus names, binder order/implicitness, domain, scalar fields, constants, exponent `(k+1)/2`, pi factors, and quantifier scope match literally. No entire sorry-bearing signature module was imported.

Five-bin table for every outer binder of the five required theorem signatures (T = TYPING, S = SOURCE; all STANDING/RULED/EXCESS counts zero). References: PA source L155-L163; accepted companion interfaces design L1817-L1840 and audit-2 F3; e5 source L20. `p11Bound U G S` was unfolded as `∀ z ∈ U, ‖G z‖ ≤ S`.

| Theorem | Binder | Bin | Source / meaning |
|---|---|---|---|
| `e5` | `a` | T | e5: nonnegative integer exponent |
| `e5` | `b` | T | e5: nonnegative integer exponent |
| `e5` | `h` | S | L20: at least one exponent odd |
| `polar_avg` | `n` | T | PA: dimension |
| `polar_avg` | `D` | T | PA: J domain |
| `polar_avg` | `hD` | S | L156: D open |
| `polar_avg` | `r` | T | PA: radius |
| `polar_avg` | `S` | T | PA: bound |
| `polar_avg` | `hr` | S | L156: 0<r |
| `polar_avg` | `hr1` | S | L156: r<=1 |
| `polar_avg` | `hS` | S | L156: S>0 |
| `polar_avg` | `G` | T | PA: complex function on J and phase coordinates |
| `polar_avg` | `hG` | S | L156: holomorphic on D times phase ball |
| `polar_avg` | `hb` | S | L156: pointwise norm bound S |
| `polar_average_linear` | `n` | T | PA dimension |
| `polar_average_linear` | `D` | T | PA J domain |
| `polar_average_linear` | `hD` | S | PA open domain / accepted companion |
| `polar_average_linear` | `r` | T | PA radius |
| `polar_average_linear` | `hr` | S | PA positive radius / accepted companion |
| `polar_average_linear` | `G` | T | PA input function |
| `polar_average_linear` | `H` | T | PA second input function |
| `polar_average_linear` | `hG` | S | PA analytic input / companion |
| `polar_average_linear` | `hH` | S | PA second analytic input / companion |
| `polar_average_linear` | `a` | T | L162: arbitrary complex linear coefficient |
| `polar_average_linear` | `b` | T | L162: arbitrary complex linear coefficient |
| `polar_average_normalization` | `n` | T | PA dimension |
| `polar_average_normalization` | `C` | T | L162: arbitrary phase-independent function of J |
| `polar_average_normalization` | `z` | T | L162: evaluation point |
| `polar_extension_unique` | `n` | T | PA dimension |
| `polar_extension_unique` | `D` | T | PA J domain |
| `polar_extension_unique` | `hD` | S | PA / accepted identity-theorem companion: open D |
| `polar_extension_unique` | `R` | T | action radius |
| `polar_extension_unique` | `hR` | S | accepted identity-theorem companion: R>0 |
| `polar_extension_unique` | `A` | T | first analytic extension candidate |
| `polar_extension_unique` | `B` | T | second analytic extension candidate |
| `polar_extension_unique` | `hA` | S | accepted companion: first candidate holomorphic |
| `polar_extension_unique` | `hB` | S | accepted companion: second candidate holomorphic |
| `polar_extension_unique` | `heq` | S | accepted companion: equality on positive-real action open subset |

Counts: TYPING 22, SOURCE 16, STANDING 0, RULED 0, EXCESS 0. The conditional jet input under `∀ k` in the *conclusion* of `polar_avg` is precisely source clause (c), with universal J and all orders j<k; it is not a hidden assumption for existence or holomorphy. The positive-real guard in clause (b) and in linearity is preserved. `heq` in the separate identity-theorem helper is its source equality-on-an-open-subset premise, not an assumed preparation conclusion.

Definitions (all literal, no classical choice or arbitrary-witness construction):

| Definition | Whole-carrier body classification |
|---|---|
| `p11PolarAverage` | Required raw principal-root normalized torus integral, byte-identical to the signature; total Bochner integral semantics do not justify unrestricted linearity, and no proof uses that shortcut. |
| `p11Rad` | Coordinatewise principal root of rho/pi, including zero and branch-cut values. |
| `p11PolarPt` | Explicit complex trigonometric polar map. |
| `p11PolarW` | Explicit torus average in radial coordinates. |
| `p11Vj` | Finite-stage coordinate substitution. Its if selects processed/unprocessed coordinates by index; neither branch is a fallback for an unproved condition. |
| `p11Wj` | Literal mixed-radius stage domain. |
| `p11Oj` | Literal parameter domain with current coordinate free. |

For each: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS. Holomorphic outputs and normalizations are proved on their intended domains. Principal-root branch discontinuity is removed by evenness in the integral, rather than assumed absent.

## Proof audit and attempted refutations

Reviewed all six proofs/modules, with particular attention to the following possible failures:

- **Branch cut/zero:** EvenDescent L38-L89 evaluates the contour kernel by two Cauchy integrals at ±sqrt(u). Strict radius inequalities keep both poles inside and all denominators nonzero on the circle, including u=0. L92-L167 proves local joint holomorphy via a parameter integral. There is no Re(u)>0 premise smuggled into that result.
- **Differentiation under the integral:** ParamIntegral L43-L97 restricts to a closed half-radius parameter ball and compact integration set, bounds the continuous fderiv there, proves the measurability/integrability obligations, and supplies the literal composed derivative to dominated differentiation. No convergence or derivative conclusion is assumed. Torus L91-L111 supplies the compact real cube and maps every integrand point into the G domain.
- **Evenness:** Torus L113-L158 uses integrable Fubini and period-one translation. L160-L219 shows a half-period shift flips both sine and cosine in the selected coordinate. G itself is not required even. Iterate L97-L194 descends one coordinate at a time on the correct mixed radii, including n=0.
- **Norm/gauge:** `P11CVec n = Fin n → ℂ`, `P11Phase n` is the product of two such spaces; Pi and product norms are max norms. Bounds for sin/cos are applied to real integration angles. sqrt(rho/pi) has norm at most sqrt(norm rho/pi), so the phase image stays inside radius r. No Euclidean/max identification occurs.
- **Vanishing order:** Order L51-L97 picks the least nonzero derivative, factors out its power via iterated dslope, divides only by positive t^j, and uses a strictly positive residual exponent to contradict continuity at zero. In `polar_avg`, `j<(k+1)/2` implies `2*j<k`; this is the exact natural-number ceiling k/2, including k=0. rho=0 is handled separately before any division by its norm.
- **Constants/uniformity:** Witness `AG := p11PolarAverage G` depends only on G; even holomorphy holds on the larger action ball pi*r^2. The mean bound is actually S and is enlarged to `2^(2*n)*S`. Schwarz on the line through rho with radius `(pi*r^2/4)/norm rho` gives exactly the requested constant and power. There is no new constant selected after J,k,rho.
- **Clause (d)/identity:** Linear integrands are proved continuous before integral_add. The constant identity uses unit-cube volume 1. The quadratic identity uses sqrt(a)^2=a and sin^2+cos^2=1, yielding rho/(2*pi). Uniqueness works on each connected action ball at fixed J, with a positive-real basepoint R/2; no connectedness of D is needed.

These attempted mathematical refutations did not produce a blocker. All extra helper hypotheses are used in the analytic helper they describe and discharged in the core theorem; no conclusion-shaped physical/preparation hypothesis was found.

## Notes, coverage, and refutation status

**N1 — proof-plan/graph deviation, informational, confirmed after refutation.** Design L726 says `C3,P0; Taylor coefficients and termwise integration; e5`; L168-L170 list local `pa_taylor`, `pa_mono`, `pa_series`. The implementation instead proves ED and radial decay. The 45-module KAM import closure includes `Preparation.Schwarz`, but not `MaximalStep.Taylor`, `MaximalStep.Parameter` (C3), or `Preparation.AnalyticExtension`. `e5` is proved but not called by `polar_avg`. Refutation: the required conclusion and all six signature declarations remain exact, and the alternative proof discharges their analytic obligations. Therefore this is not a failed theorem. The three Taylor-series *proof-step* nodes are not independently proved by this implementation and must not be marked closed merely from PA's package PASS. No graph edits were authorized or made.

**N2 — e5 coverage, informational, confirmed after refutation.** Source `p11-cp09-preparation.tex:20` says “Termwise integration of a uniformly convergent series ... with absolute value ≤1.” The graph node `bpP:p11:e5` at `docs/graph/P/packets/P-p11.nodes.md:2019` likewise includes all three claims. Lean `e5` L41-L43 proves exactly the accepted signature's odd-exponent vanishing component. Refutation: the missing clauses are not conclusions of this signature, and the alternative proof does not rely on them; hence no signature mismatch or unpaid input in PA. Do not promote the whole external graph node to PROVED from this export. The handoff's L438 e5 source locator is stale; current source is L20. This is a coverage/locator issue, not suspected false mathematics in a pinned source.

**N3 — nonempty generated-root baseline diff, informational for this bounded audit.** The prescribed `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is not empty: `KAM.lean` has five inherited import additions (Most, BlockStability, OscillatorComposition, Loss, Remainder); Frozen/manifest/README are empty in that triple-dot comparison. Refutation: `git log -- KAM.lean` attributes these changes to inherited root-regeneration commits `686d56c` and `c8ccbea`, not P6. All seven P6 implementation/format commits modify only the six scoped files. Thus the literal whole-branch hygiene predicate fails, but this is not evidence of a P6 prohibited edit. No blanket whole-branch PASS is claimed.

No suspected pinned-source mathematical erratum; no audit-introduced source deviation. The proof-plan substitution above is explicitly retained. Unused `hr1` in `polar_avg` and `hD` in linearity/uniqueness remain in their required exact signatures. The top-level 334-line module is an interface plus core proofs, not an import-only facade; all files satisfy the hard 1500-line cap. The handoff's earlier line counts predate formatting.

## Independent verification

All audit-owned Lean/Lake calls were serial and used `LEAN_NUM_THREADS=1`; direct Lean/checker commands used `nice -n 5`, and the compile wrapper invokes that priority itself. No library rebuild, clean, update or cache operation was requested.

1. **Targeted gated build** (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ap6 KAM.Planetary.Preparation.PolarAverage
   ```

   Output: `[inp-gate] slot 1 acquired 13:52:11 for KAM.Planetary.Preparation.PolarAverage`; `Build completed successfully (9091 jobs).` The target was replayed from the build cache; independent kernel replay below checks its proof terms. Replayed warnings: Schwarz L89 unused `hM`; PolarAverage L157 unused `hr1`, L250/L299 unused `hD`. No errors or heartbeat failures.

2. **Exact-signature/definition probes and axioms** (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AP6Audit.lean
   ```

   The transient probe imported only `KAM.Planetary.Preparation.PolarAverage`. It copied each exact theorem header from the pinned signature under `audit_<name>`, with proof `by exact <implementation> <explicit binders in order>`. The explicit sequences were `a b h`; `hD hr hr1 hS hG hb`; `hD hr hG hH a b`; `C z`; and `hD hR hA hB heq`. For every copied theorem it also checked both `example : type_of% @audit_<name> := @<name>` and the reverse. The literal definition was copied under `audit_p11PolarAverage`, and `example : @audit_p11PolarAverage = @p11PolarAverage := rfl` passed. This is the applicable exact-type/assembly check; there is no P6 provider/frozen theorem pair to seal.

   `#print axioms` was generated for **all 48 public declarations**, including all seven definitions. Output contained exactly 48 axiom lines, no other output; **every line** ended in:

   ```text
   depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   In particular this holds separately for `KAM.Planetary.e5`, `polar_avg`, `polar_average_linear`, `polar_average_normalization`, and `polar_extension_unique`. No `sorryAx` or project axiom.

3. **Independent kernel replay**, one invocation (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Preparation.PolarAverage KAM.Planetary.Preparation.PolarAverage.ParamIntegral KAM.Planetary.Preparation.PolarAverage.EvenDescent KAM.Planetary.Preparation.PolarAverage.Torus KAM.Planetary.Preparation.PolarAverage.Iterate KAM.Planetary.Preparation.PolarAverage.Order
   ```

   Complete output:

   ```text
   replaying KAM.Planetary.Preparation.PolarAverage
   replaying KAM.Planetary.Preparation.PolarAverage.EvenDescent
   replaying KAM.Planetary.Preparation.PolarAverage.Iterate
   replaying KAM.Planetary.Preparation.PolarAverage.Torus
   replaying KAM.Planetary.Preparation.PolarAverage.ParamIntegral
   replaying KAM.Planetary.Preparation.PolarAverage.Order
   ```

4. **Source lint**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely the expressly permitted stale-root diagnostic. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (662 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No generated file was regenerated. The frozen-anchor guard and all 144 ABI hashes pass independently of that expected root exception.

5. **Import and source hygiene.** Recursive KAM import scan: **45 modules**, no provider and no frozen theorem. Its ten frozen dependencies are definitions, all manifest state **SEALED**: complexStrip, actionNbhd, omegaZero, IsPrimaryOnStrip, IsRealOnReals, hamiltonianVectorField, hamiltonianVectorFieldℂ, Planetary.Phase, IsDiophantine, symplecticForm. The source-facing P11 carriers and p11Bound/torusAverage bodies were checked. No manifest entry for a P6 theorem/export was found; the external graph node itself has `FROZEN_FILE: -`.

   `rg -n 'sorry|admit|axiom|unsafe|opaque|set_option|EuclideanSpace' KAM/Planetary/Preparation/PolarAverage.lean KAM/Planetary/Preparation/PolarAverage` returned no matches (exit 1, as expected). Module checks cover copyright, module, public imports, module docstring and public section; definitions are exposed by the enclosing `@[expose]` section. Maximum source length **334** lines. A repository-wide declaration-name scan excluding the six targets found **zero collisions** for all 48 new public names. Scoped triple-dot `git diff --check` and final `git diff --check` exited **0**. The protected-path triple-dot command's nonempty root result is recorded explicitly as N3 above.

6. **Integrity and cleanup:** All six input SHA-256 values and the pinned signature hash were rechecked unchanged after validation. All 48 declaration rows are present; no trailing whitespace or unmatched code fence. The audit-owned probe, inventory and three logs were removed from `.lake/abi-scratch/`; no production source changed. Final status contains only this new report and the pre-existing untracked handoff.

## Closeout

**PASS WITH NOTES**, scoped to the six requested files. Exact signatures and definition body pass; all 41 public theorems and seven definitions have clean axiom closure; six-module kernel replay passes; targeted build passes; lint passes all checks except the authorized generated-root exception. Notes N1–N3 survive the stated refutation checks as bounded coverage/provenance observations, with no mathematical blocker. No remaining unchecked declaration, temporary probe, source fix, frozen seal, or campaign/consumer closure claim. External e5 and the three bypassed Taylor-step graph nodes retain their broader proof obligations.
