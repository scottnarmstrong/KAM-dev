# W1-SINES independent package audit 1

**Overall verdict: PASS WITH NOTES (infrastructure only; no provider or frozen-theorem seal).**

All three requested blueprint nodes are implemented without additional source-level obligations or weakened conclusions. The changed polynomial estimate is an internal sufficient estimate; it does not weaken the reconstruction API. The complex feature is source-faithful on its strip, with an explicitly documented zero extension elsewhere. The compactly supported odd extension differs from the blueprint at a null endpoint and outside the integration interval; no result uses those values as the source periodic function.

## Scope, authority and frozen inputs

Date: 2026-10-30. Tier 2 focused source-correspondence/package audit. This auditor did not author the package. Scope: the complete `git diff inp...HEAD`, the three new implementation modules, and blueprint-W/parts/w1-sequences.tex:591–695, with standing conventions and the six imported frozen definitions. Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the supplied package brief and AUDIT FOCUS. The user's exact report path overrides the generic brief's main-worktree destination. The AUDIT FOCUS overrides the generic protected-root requirement for the regenerated KAM.lean and KAM/Root/Wave.lean, and prescribes the SLIM lint wrapper.

`docs/tracks/W/statement.md` does not exist; the track statement is `docs/tracks/W/W-STATEMENTS.md`, read together with D41 and `docs/tracks/W/FREEZE.md`. Its historical DRAFT heading is superseded by D41 and the actual manifest, not treated as current freeze authority.

- Audited HEAD: `234cc16154f90279065371fad31df2aab57aa4e0`.
- Comparison branch inp: `003c5a3a04b09690bc03ab763b69e159641da2b4`.

Snapshot `frozen-v1` below identifies the immutable inputs. No source, frozen, manifest, generated file or git state was edited. Temporary probes were confined to `.lake/abi-scratch/` and removed after validation. Build/lint tools create ordinary ignored build artifacts.

| Input | SHA256 |
|---|---|
| `AGENTS.md` | `9895b2a777dd546170f6c0f40ee15bc7330c377d70485c25b38c318eb3e8e804` |
| `docs/PLAN.md` | `3efa6ab0e8da45cf578fcd9c294f330d6db4372fed34c07729e9ba6f6e1fb71f` |
| `docs/DECISIONS.md` | `27b7abea7a24c8347156515cfb2f4179472f528338ee863e02fa0e898d69ae08` |
| `docs/tracks/W/W-STATEMENTS.md` | `3e6e698a076606b9f79e2a48cced8a6c1728af818746e1f59e9b6f0bae00fc30` |
| `docs/tracks/W/FREEZE.md` | `a036ae77da92340f9a7dd20a16d966dc7ef0b01de476fe05a8ab405e79022d04` |
| `docs/tracks/W/audits/W1-SINES-handoff.md` | `3a30645059db90b08b5192a35ef7ce10d05c8c71c03d9060b9b5c5e1cee5b8f8` |
| `blueprint-W/parts/w1-sequences.tex` | `32647bb0e4ebab844e3976e53b1e033a72d25de06dfab7c6c19c9199c6cff02b` |
| `blueprint-W/parts/w0-conventions.tex` | `016d51ed338af4b0dd7192cf82bc2f29783bac56e1405d5bb8542f22b9d2330d` |
| `manifest/frozen-anchors.json` | `674c73210fe8aeef703101ebe014dbc3e8569cb12f54a14dba1a7ff418d76aab` |
| `KAM/Wave/Recon/ReconAnalytic.lean` | `33725b6fd74f4c6158d553a7ef1b7c8122b66b31f8c7d84a4c83f25c6a453199` |
| `KAM/Wave/Recon/SineCompleteness.lean` | `529432bafa81fc5fbecfce96321085a68f168be8773d04db9aad27544d6182cf` |
| `KAM/Wave/Recon/SineFeature.lean` | `7a5472f70ca437e0c94ccc2f475217ef1b00cd7b9526c815515af62f51a8b7b0` |
| `KAM/Frozen/Wave/Defs/Lam.lean` | `097b70740bbedd0463d2e0ffb98e99bf508f81207b8370ac05ddc91aa3e05f81` |
| `KAM/Frozen/Wave/Defs/SineMode.lean` | `708e6e5d2d878d13e87acb6f2e2b4a057be17a33f9999b417cbaf75bac555263` |
| `KAM/Frozen/Wave/Defs/EllWeight.lean` | `88c0329883e40f8c1c852233a39eaa92482bf4b3a99041e5595e9b277d7e8722` |
| `KAM/Frozen/Wave/Defs/Coeff.lean` | `c30ede55986dd8f88f1b85544a38874a2aacb0d7f4bd072d9e4a486b72ab2622` |
| `KAM/Frozen/Wave/Defs/ReconU.lean` | `59f629f4ba2fd487e024d1a2564241010d2884e81ddc33a12a2e58f5da1a3245` |
| `KAM/Frozen/Wave/Defs/ReconV.lean` | `806e6a22726d296c11ef1c5aad0959a80445e463f3f7a864089cade9f29f3181` |

The six frozen exports are respectively `wave.lam.v1`, `wave.sineMode.v1`, `wave.ellWeight.v1`, `wave.coeff.v1`, `wave.reconU.v1`, `wave.reconV.v1`, all manifest state SEALED (definitions). Their bodies were inspected, and the frozen guard/ABI check below verifies current identities. There is no theorem anchor proved by this package. In particular `wave.nlw2.v1` remains DRAFT_SORRY and is not imported.

## Node verdicts and adversarial findings

| Blueprint node | Main Lean declarations (namespace KAM.Wave) | Verdict | Source comparison |
|---|---|---|---|
| bpW:w1:sine-completeness | ae_eq_zero_of_integral_sineMode_eq_zero; eqOn_zero_of_integral_sineMode_eq_zero | PASS WITH NOTES | Lines 593–615: exact real L² premise, all positive sine moments, a.e. zero; continuity adds equality at both endpoints. Odd-extension representation note N2 below. |
| bpW:w1:sine-feature | sineFeatureC_bound; sineFeatureC_analyticAt; sineFeatureR_analyticAt; hasSum_inner_sineFeatureR; summable_abs_inner_sineFeatureR | PASS WITH NOTES | Lines 617–646: exact majorant, every k and real p, arbitrary polynomially bounded real β, complex analyticity on the full open strip and real pairing identity with absolute convergence. Zero-extension note N1 below. |
| bpW:w1:recon-analytic | reconUIter_zero/reconVIter_zero; hasDerivAt_reconUIter/reconVIter; iteratedDeriv_reconU/reconV; derivWithin_reconU_Icc/reconV_Icc; analyticAt_iteratedDeriv_reconU/reconV | PASS WITH NOTES | Lines 648–694: exact frozen reconstructions; every k, y and real x; derivatives within the closed interval include its endpoints; joint analyticity for every real normed parameter space S. Internal estimate note N3 below. |

No mathematical blocker survived refutation. The following notes record the actual deviations and their limits.

**N1 — complex feature totalization.** Source lines 619–620 define Ψ only for `|Im z| < a`. SineFeature.lean:188–189 exports a total helper with `if h : |z.im| < a then … else 0`; it is explicitly documented as “zero outside.” The body on the strip is the exact coordinate formula, with membership proved by the summable majorant. `sineFeatureC_apply` requires strip membership; the bound derives it from `|Im z| ≤ a' < a`; analyticAt takes strict membership and chooses a smaller open neighbourhood. Real restriction uses `a > 0`. Refutation attempts: inspect every use of this helper and elaborate its on-strip equation, off-strip zero equation, analyticity and real-coordinate restriction. All pass. No theorem asserts that the zero extension is the analytic sine formula off the strip or across its boundary. This is acceptable as the domain-restricted helper under the brief's “junk values or fallbacks that a theorem relies on fail” criterion. It does not certify a globally faithful complex feature outside the source domain; consumers must retain strip guards.

**N2 — odd extension and endpoints.** Source lines 600–601: “g(x)=f(x) for 0<x≤π” and “regard it as a function on R/2πZ.” SineCompleteness.lean:37–41 instead defines zero extension from `(0,π)` and subtracts its reflection on all ℝ. Thus `oddExt f π = 0` (rather than f π), it vanishes outside `(-π,π)`, and is not a periodic lift. It is exactly odd everywhere and equals f on `(0,π)`. Refutation: endpoint/support/oddness probes, direct inspection of the interval integral conversion, and the proof's use of `fourierCoeffOn`/Parseval restricted to `Ioc (-π) π`. Endpoints are Lebesgue-null; the code never assumes periodicity of this ℝ-function. No stronger blueprint assertion of its precise L² norm is separately exported; that intermediate equality is bypassed by direct MemLp membership, not assumed. The continuous conclusion obtains endpoints by closure from `(0,π)`, independently of oddExt's endpoint values. The module prose “on AddCircle” describes interval Fourier coefficients, not a separately defined periodic function.

**N3 — polynomial bound and consumer strength.** Source line 674 uses `|β_j| ≤ (1+m)^(1/4) j^(1/2)`. ReconAnalytic.lean:105–121 proves `PolyBounded β (1+m) 1` for both β values, i.e. the weaker estimate `|β_j| ≤ (1+m) j`. This does not prove the displayed sharp estimate itself. Refutation: inspect exported conclusions and all feature instantiations: no quantitative reconstruction bound exposes B or ν, and the feature's coordinate body is independent of its membership proof. Any polynomial growth exponent gives summability of `j^(ν+k-p) exp(-(a-a')j)`. Both β definitions remain exact, no estimate becomes a consumer premise, and all reconstruction/analyticity conclusions are unchanged. This is a proof-route deviation only, not a source defect or a weakened consumer statement.

**N4 — other reported deviations.** `sin(t+kπ/2)` is the exact kth derivative convention: the zero identity and successor HasDerivAt establish it inductively, over real x, with the complex formula its usual extension. `MemLp f 2 (volume.restrict (Ioo 0 π))` is the raw-function realization of real L²(0,π). The extra continuous hypothesis in part (ii) is precisely “moreover,” not an excess premise. Parseval replaces Fourier-basis injectivity with the same zero-coefficients implication; the positive normalization `(π - -π)⁻¹` is explicitly discharged. Generic S in reconstruction is exactly the current source line 661 and includes `Fin n → ℝ`; it does not require completeness of S or analyticity away from s₀.

## Expanded binder classification

These are the source-facing theorem schemas; every binder of each member has the indicated class. TYPING includes implicit universes/carriers, numerical parameters and evaluation arguments; no conclusion-shaped premise is hidden in a class. The only project-owned hypothesis predicate, PolyBounded, expands to exactly three SOURCE premises below. No result is assumed via an instance.

| Schema | Binder | Class | Authority |
|---|---|---|---|
| feature | a | TYPING | 618–620, real width parameter |
| feature | p | TYPING | 618, arbitrary real exponent |
| feature | β | TYPING | 618, positive-index real sequence |
| feature | B | TYPING | 618, bound witness parameter |
| feature | ν | TYPING | 618, growth witness parameter |
| feature | hβ.1: 0 ≤ B | SOURCE | 618 |
| feature | hβ.2.1: 0 ≤ ν | SOURCE | 618 |
| feature | hβ.2.2: ∀ j, |β j| ≤ B*j^ν | SOURCE | 618 |
| feature | k | TYPING | 618, any natural derivative order |
| real feature | ha: 0 < a | SOURCE | 618 |
| bound/holomorphy | a' | TYPING | 622, inner strip width |
| bound/holomorphy | ha': a' < a | SOURCE | 622; dropping 0<a' is a strengthening |
| bound | z | TYPING | 619, complex point |
| bound | hz: |z.im| ≤ a' | SOURCE | 622–623 |
| bound | j | TYPING | 620, positive index |
| analyticAt | z | TYPING | 619, complex point |
| analyticAt | hz: |z.im| < a | SOURCE | 619, 624 |
| real feature/pairing | x | TYPING | 625–626, arbitrary real point |
| pairing | y | TYPING | 626, real ℓ² vector |
| reconstruction | m | TYPING | W1 standing convention, line 3 |
| reconstruction | hm: 0 < m | STANDING | bpW:w0:mass; W1 line 3 |
| reconstruction | k | TYPING | 649, arbitrary natural order |
| reconstruction | y | TYPING | 651, arbitrary real ℓ² vector |
| reconstruction | x | TYPING | 651, arbitrary real point |
| derivWithin | hx: x ∈ Icc 0 π | SOURCE | 659–660 |
| joint analyticity | S | TYPING | 661, arbitrary parameter carrier |
| joint analyticity | NormedAddCommGroup S | TYPING | 661, normed real-space formation |
| joint analyticity | NormedSpace ℝ S | TYPING | 661 |
| joint analyticity | Y | TYPING | 662, parameter map |
| joint analyticity | s₀ | TYPING | 662, parameter point |
| joint analyticity | hY: AnalyticAt ℝ Y s₀ | SOURCE | 662 |
| joint analyticity | x₀ | TYPING | 664, arbitrary real point |
| completeness | f | TYPING | 594, real-valued function |
| completeness | hf: MemLp f 2 … | SOURCE | 594, L² premise |
| completeness | h: ∀ l, integral(f*sineMode l)=0 | SOURCE | 594, all positive sine moments |
| continuous completeness | hc: ContinuousOn f (Icc 0 π) | SOURCE | 595 |

Inventory counts (distinct rows above, shared binders listed once): SOURCE 12, STANDING 1, TYPING 23, RULED 0, EXCESS 0. Each theorem uses the applicable subset, not all rows as a combined assumption list. Output-bound x and interval membership in the final completeness conclusion remain quantified in the conclusion. Auxiliary general lemmas have their own honest conditional names: e.g. `memℓp_two_of_norm_le` assumes summability and domination only as a general construction tool, then both are proved at feature consumers; `intervalIntegrable_mul_sineExtZero` assumes continuity of the multiplier and obtains it for both exponential multipliers. These internal inputs never become new premises of a source-facing theorem.

## Definition classification

All 20 new definitions are literal formulas or proved bundled constructions; no new abbrev or structure, non-unique choice, deferred characterization or hidden result package occurs. `@[expose] public noncomputable section` exposes their bodies.

| Definition(s) | Classification and whole-carrier behavior |
|---|---|
| sineModeIter; sineModeIterC | Literal real/complex phase-shift formulas for every k,j,x/z; normalization √(2/π), positive index j and j^k exact. |
| PolyBounded | Literal source predicate `0≤B ∧ 0≤ν ∧ ∀j, |β j|≤B*j^ν`; all fields audited above. |
| sineFeatCoord; sineFeatCoordC | Literal β times differentiated mode divided by frozen ellWeight; denominator strictly positive for all real a,p and positive j. |
| sineFeatMajorant | Literal √(2/π) B j^(ν+k-p) exp(-δj), all real parameters; summability theorem requires δ>0 and proves it. |
| sineFeatureR | Exact coordinate family bundled with proved ℓ² membership for every admitted input; a>0 and PolyBounded are source assumptions. |
| sineFeatureC | Exact ℓ²-bundled family on its source strip; documented zero outside. Domain/totalization note N1; every substantive consumer has the guard. |
| lpRe; lpReCLM | Exact coordinatewise real part, membership proved; real linearity and norm bound ≤1 proved, no choice. |
| betaU; betaV | Literal inverse sqrt(lambda) / sqrt(lambda) with m>0 carried into frozen lam. No default/clamped lambda input is admitted. |
| reconFeatureU; reconFeatureV | Exact sineFeatureR at a=p=1 with these β; the proved weaker growth bound only certifies membership. |
| reconUIter; reconVIter | Literal real inner products with exact feature and y; full series and absolute convergence proved. |
| reconUIterCLM; reconVIterCLM | Exact innerSL functionals; apply lemmas identify them with the literal reconstructions. |
| sineExtZero | Literal zero extension of the complex cast of f from `(0,π)`; intended operation on all ℝ. |
| oddExt | Literal zero extension minus reflection, on all ℝ; exactly odd, compactly supported, note N2. |

BODY_MATCH: OK on each intended domain (N1/N2 explicitly describe representation outside it).
PUBLIC_CARRIER: OK as documented auxiliary totalizations under this audit brief; no off-domain source identity is claimed.
WELL_DEFINEDNESS: OK, with membership/linearity/summability established where required.
CHARACTERIZATION: N/A_LITERAL.
CHOICE_INDEPENDENCE: N/A (no selected witness).
DEFINITION_VERDICT: PASS WITH NOTES N1/N2.

Frozen surface: no shadow reconU/reconV/coeff/lam is defined. The new zero-order identities unfold the frozen tsum definitions after proving absolute convergence for every y and real x. Thus no non-summable tsum default is used. `iteratedDeriv_reconU/V` explicitly applies Mathlib's iteratedDeriv to those same frozen functions, and the derivWithin theorems refer to them verbatim. Exact-type probes independently elaborate all four equations and the two joint-analytic derivative conclusions.

## Declaration inventory

Every row is a new public declaration, names below are relative to `KAM.Wave`. Public theorem/lemma count: 66; public definition count: 20. The private ellWeight_pos lemma is also checked through kernel replay and the consumers' axiom closure.

| Blueprint node | Declaration and implementation locator | Verdict | Reason |
|---|---|---|---|
| bpW:w1:recon-analytic | `hasDerivAt_sineModeIter` (ReconAnalytic.lean:42) | PASS | Exact successor derivative of the phase-shift formula. |
| bpW:w1:recon-analytic | `hasDerivAt_sineFeatCoord` (ReconAnalytic.lean:58) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:recon-analytic | `hasDerivAt_sineFeatureR` (ReconAnalytic.lean:65) | PASS | Derivative obtained by continuous coordinate evaluation and uniqueness; no derivative assumed. |
| bpW:w1:recon-analytic | `betaU` (ReconAnalytic.lean:85) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:recon-analytic | `betaV` (ReconAnalytic.lean:88) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:recon-analytic | `one_le_lam` (ReconAnalytic.lean:90) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:recon-analytic | `lam_le` (ReconAnalytic.lean:96) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:recon-analytic | `polyBounded_betaU` (ReconAnalytic.lean:105) | PASS WITH NOTES | Proved sufficient bound with B=1+m, ν=1; internal deviation N3. |
| bpW:w1:recon-analytic | `polyBounded_betaV` (ReconAnalytic.lean:113) | PASS WITH NOTES | Proved sufficient bound with B=1+m, ν=1; internal deviation N3. |
| bpW:w1:recon-analytic | `reconFeatureU` (ReconAnalytic.lean:124) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:recon-analytic | `reconFeatureV` (ReconAnalytic.lean:128) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:recon-analytic | `reconUIter` (ReconAnalytic.lean:133) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:recon-analytic | `reconVIter` (ReconAnalytic.lean:138) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:recon-analytic | `reconUIterCLM` (ReconAnalytic.lean:142) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:recon-analytic | `reconVIterCLM` (ReconAnalytic.lean:146) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:recon-analytic | `reconUIterCLM_apply` (ReconAnalytic.lean:149) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:recon-analytic | `reconVIterCLM_apply` (ReconAnalytic.lean:152) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:recon-analytic | `hasSum_reconUIter` (ReconAnalytic.lean:157) | PASS | Exact frozen coeff and sqrt(lam); unconditional HasSum for all admitted inputs. |
| bpW:w1:recon-analytic | `hasSum_reconVIter` (ReconAnalytic.lean:169) | PASS | Exact frozen coeff and sqrt(lam); unconditional HasSum for all admitted inputs. |
| bpW:w1:recon-analytic | `summable_abs_reconUIter` (ReconAnalytic.lean:180) | PASS | Absolute convergence proved, never assumed. |
| bpW:w1:recon-analytic | `summable_abs_reconVIter` (ReconAnalytic.lean:184) | PASS | Absolute convergence proved, never assumed. |
| bpW:w1:recon-analytic | `reconUIter_zero` (ReconAnalytic.lean:189) | PASS | Exact frozen tsum identified after proving summability. |
| bpW:w1:recon-analytic | `reconVIter_zero` (ReconAnalytic.lean:198) | PASS | Exact frozen tsum identified after proving summability. |
| bpW:w1:recon-analytic | `hasDerivAt_reconUIter` (ReconAnalytic.lean:209) | PASS | Exact HasDerivAt with the next derived reconstruction, all real x. |
| bpW:w1:recon-analytic | `hasDerivAt_reconVIter` (ReconAnalytic.lean:218) | PASS | Exact HasDerivAt with the next derived reconstruction, all real x. |
| bpW:w1:recon-analytic | `iteratedDeriv_reconU` (ReconAnalytic.lean:227) | PASS | Equality with derivatives of the exact frozen reconstruction, for every k and y. |
| bpW:w1:recon-analytic | `iteratedDeriv_reconV` (ReconAnalytic.lean:239) | PASS | Equality with derivatives of the exact frozen reconstruction, for every k and y. |
| bpW:w1:recon-analytic | `hasDerivAt_reconU` (ReconAnalytic.lean:250) | PASS | Exact HasDerivAt with the next derived reconstruction, all real x. |
| bpW:w1:recon-analytic | `hasDerivAt_reconV` (ReconAnalytic.lean:256) | PASS | Exact HasDerivAt with the next derived reconstruction, all real x. |
| bpW:w1:recon-analytic | `derivWithin_reconU_Icc` (ReconAnalytic.lean:263) | PASS | Exact frozen function; uniqueDiffOn_Icc handles both endpoints. |
| bpW:w1:recon-analytic | `derivWithin_reconV_Icc` (ReconAnalytic.lean:270) | PASS | Exact frozen function; uniqueDiffOn_Icc handles both endpoints. |
| bpW:w1:recon-analytic | `analyticAt_reconFeatureU` (ReconAnalytic.lean:279) | PASS | Joint analyticity by the proved feature analyticity and continuous bilinear pairing. |
| bpW:w1:recon-analytic | `analyticAt_reconFeatureV` (ReconAnalytic.lean:285) | PASS | Joint analyticity by the proved feature analyticity and continuous bilinear pairing. |
| bpW:w1:recon-analytic | `analyticAt_reconUIter` (ReconAnalytic.lean:293) | PASS | Joint analyticity by the proved feature analyticity and continuous bilinear pairing. |
| bpW:w1:recon-analytic | `analyticAt_reconVIter` (ReconAnalytic.lean:302) | PASS | Joint analyticity by the proved feature analyticity and continuous bilinear pairing. |
| bpW:w1:recon-analytic | `analyticAt_iteratedDeriv_reconU` (ReconAnalytic.lean:313) | PASS | Exact frozen derivatives; generic real normed S and only source premise hY. |
| bpW:w1:recon-analytic | `analyticAt_iteratedDeriv_reconV` (ReconAnalytic.lean:320) | PASS | Exact frozen derivatives; generic real normed S and only source premise hY. |
| bpW:w1:sine-completeness | `sineExtZero` (SineCompleteness.lean:37) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:sine-completeness | `oddExt` (SineCompleteness.lean:41) | PASS WITH NOTES | Exact odd compact extension; null-endpoint/periodic-representation note N2. |
| bpW:w1:sine-completeness | `oddExt_of_mem_Ioo` (SineCompleteness.lean:43) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-completeness | `memLp_sineExtZero` (SineCompleteness.lean:47) | PASS | Membership proved from explicit domination/integrability, no extra consumer premise. |
| bpW:w1:sine-completeness | `memLp_oddExt` (SineCompleteness.lean:52) | PASS | Membership proved from explicit domination/integrability, no extra consumer premise. |
| bpW:w1:sine-completeness | `integral_sineExtZero_mul` (SineCompleteness.lean:59) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-completeness | `fourier_neg_coe_two_pi` (SineCompleteness.lean:71) | PASS | Period π-(-π)=2π, unnormalized exponential e^(-inx) exactly. |
| bpW:w1:sine-completeness | `exp_neg_sub_exp` (SineCompleteness.lean:80) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-completeness | `integral_sin_int_mul_eq_zero` (SineCompleteness.lean:91) | PASS | All integer frequencies from all positive sine moments, including zero and negative n. |
| bpW:w1:sine-completeness | `integrable_sineExtZero` (SineCompleteness.lean:125) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-completeness | `intervalIntegrable_mul_sineExtZero` (SineCompleteness.lean:130) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-completeness | `fourierCoeffOn_oddExt_eq_zero` (SineCompleteness.lean:137) | PASS | All integer Fourier coefficients; required integrability proved before subtraction. |
| bpW:w1:sine-completeness | `ae_eq_zero_of_integral_sineMode_eq_zero` (SineCompleteness.lean:181) | PASS | Exact real L²/a.e. conclusion; positive Parseval normalization discharged. |
| bpW:w1:sine-completeness | `eqOn_zero_of_integral_sineMode_eq_zero` (SineCompleteness.lean:210) | PASS | Exact continuity premise; closure gives both endpoints independently of oddExt. |
| bpW:w1:sine-feature | `sineModeIter` (SineFeature.lean:45) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:sine-feature | `sineModeIterC` (SineFeature.lean:49) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:sine-feature | `PolyBounded` (SineFeature.lean:53) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:sine-feature | `sineFeatCoord` (SineFeature.lean:57) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:sine-feature | `sineFeatCoordC` (SineFeature.lean:61) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:sine-feature | `sineModeIter_zero` (SineFeature.lean:64) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `sineModeIterC_ofReal` (SineFeature.lean:67) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `sineFeatCoordC_ofReal` (SineFeature.lean:71) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `norm_complex_sin_le` (SineFeature.lean:79) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `summable_rpow_mul_exp_neg` (SineFeature.lean:94) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `sineFeatMajorant` (SineFeature.lean:108) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:sine-feature | `summable_sineFeatMajorant` (SineFeature.lean:111) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `sineFeatCoordC_norm_le` (SineFeature.lean:119) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `memℓp_two_of_norm_le` (SineFeature.lean:153) | PASS | Membership proved from explicit domination/integrability, no extra consumer premise. |
| bpW:w1:sine-feature | `sineFeatCoord_norm_le` (SineFeature.lean:164) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `memℓp_sineFeatCoord` (SineFeature.lean:170) | PASS | Membership proved from explicit domination/integrability, no extra consumer premise. |
| bpW:w1:sine-feature | `memℓp_sineFeatCoordC` (SineFeature.lean:174) | PASS | Membership proved from explicit domination/integrability, no extra consumer premise. |
| bpW:w1:sine-feature | `sineFeatureR` (SineFeature.lean:182) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:sine-feature | `sineFeatureC` (SineFeature.lean:188) | PASS WITH NOTES | Exact on strip; documented off-strip zero (N1). |
| bpW:w1:sine-feature | `sineFeatureR_apply` (SineFeature.lean:191) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `sineFeatureC_apply` (SineFeature.lean:194) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `sineFeatCoordC_differentiable` (SineFeature.lean:198) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `sineFeatureC_bound` (SineFeature.lean:204) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `sineFeatureC_differentiableOn` (SineFeature.lean:211) | PASS | Every smaller strip; analyticAt recovers every point of the full source strip. |
| bpW:w1:sine-feature | `sineFeatureC_analyticAt` (SineFeature.lean:232) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `memℓp_re` (SineFeature.lean:241) | PASS | Membership proved from explicit domination/integrability, no extra consumer premise. |
| bpW:w1:sine-feature | `lpRe` (SineFeature.lean:250) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:sine-feature | `lpRe_apply` (SineFeature.lean:252) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `norm_lpRe_le` (SineFeature.lean:254) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `lpReCLM` (SineFeature.lean:264) | PASS | Literal formula / proved bundled construction; definition table above. |
| bpW:w1:sine-feature | `lpReCLM_apply` (SineFeature.lean:271) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `sineFeatureR_eq_re` (SineFeature.lean:277) | PASS | Exact real restriction with a>0 proving strip membership. |
| bpW:w1:sine-feature | `sineFeatureR_analyticAt` (SineFeature.lean:284) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `hasSum_inner_sineFeatureR` (SineFeature.lean:296) | PASS | Source proof-step / literal formula identity checked in the full diff; no excess premise. |
| bpW:w1:sine-feature | `summable_abs_inner_sineFeatureR` (SineFeature.lean:306) | PASS | Absolute convergence proved, never assumed. |

## Independent verification

Every Lean/Lake/kernel command below was run sequentially with `LEAN_NUM_THREADS=1` and `nice -n 5`. No heartbeat, recursion, synthesis-budget override or clean/cache/update command was used. Build output is an independent current rerun (cached build artifacts were allowed); kernel replay independently rechecks the three module artifacts. Unrelated processes in other worktrees were not started or controlled by this audit.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpb KAM.Wave.Recon.SineFeature KAM.Wave.Recon.ReconAnalytic KAM.Wave.Recon.SineCompleteness
```

Exit 0. Exact output:

```text
[inp-gate] slot 2 acquired 16:26:14 for KAM.Wave.Recon.SineFeature KAM.Wave.Recon.ReconAnalytic KAM.Wave.Recon.SineCompleteness
Build completed successfully (3123 jobs).
```

2. Kernel replay (one invocation):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Wave.Recon.SineFeature KAM.Wave.Recon.ReconAnalytic KAM.Wave.Recon.SineCompleteness
```

Exit 0. Exact output:

```text
replaying KAM.Wave.Recon.SineCompleteness
replaying KAM.Wave.Recon.ReconAnalytic
replaying KAM.Wave.Recon.SineFeature

```

3. Full public axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/W1SinesAxioms.lean
```

Exit 0. Probe imports ReconAnalytic and SineCompleteness and emits `#print axioms KAM.Wave.<name>` for every line matching `^(lemma|theorem|def|abbrev|structure)\s+(\S+)` in the three new modules (private declarations excluded). All 86 records are exactly `[propext, Classical.choice, Quot.sound]`; no additional axiom. Exact output:

```text
'KAM.Wave.hasDerivAt_sineModeIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_sineFeatCoord' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_sineFeatureR' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.betaU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.betaV' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.one_le_lam' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lam_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.polyBounded_betaU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.polyBounded_betaV' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.reconFeatureU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.reconFeatureV' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.reconUIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.reconVIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.reconUIterCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.reconVIterCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.reconUIterCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.reconVIterCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasSum_reconUIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasSum_reconVIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.summable_abs_reconUIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.summable_abs_reconVIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.reconUIter_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.reconVIter_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_reconUIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_reconVIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.iteratedDeriv_reconU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.iteratedDeriv_reconV' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_reconU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasDerivAt_reconV' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.derivWithin_reconU_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.derivWithin_reconV_Icc' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.analyticAt_reconFeatureU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.analyticAt_reconFeatureV' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.analyticAt_reconUIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.analyticAt_reconVIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.analyticAt_iteratedDeriv_reconU' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.analyticAt_iteratedDeriv_reconV' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineExtZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.oddExt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.oddExt_of_mem_Ioo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.memLp_sineExtZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.memLp_oddExt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.integral_sineExtZero_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.fourier_neg_coe_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.exp_neg_sub_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.integral_sin_int_mul_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.integrable_sineExtZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.intervalIntegrable_mul_sineExtZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.fourierCoeffOn_oddExt_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.ae_eq_zero_of_integral_sineMode_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.eqOn_zero_of_integral_sineMode_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineModeIter' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineModeIterC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.PolyBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatCoord' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatCoordC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineModeIter_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineModeIterC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatCoordC_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_complex_sin_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.summable_rpow_mul_exp_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatMajorant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.summable_sineFeatMajorant' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatCoordC_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.memℓp_two_of_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatCoord_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.memℓp_sineFeatCoord' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.memℓp_sineFeatCoordC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatureR' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatureC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatureR_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatureC_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatCoordC_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatureC_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatureC_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatureC_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.memℓp_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lpRe' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lpRe_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_lpRe_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lpReCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.lpReCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatureR_eq_re' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.sineFeatureR_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.hasSum_inner_sineFeatureR' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.summable_abs_inner_sineFeatureR' depends on axioms: [propext, Classical.choice, Quot.sound]

```

4. Independent exact-type and definition probes:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/W1SinesTypes.lean
```

Final exit 0; empty output. Fifteen examples check: frozen iteratedDeriv equations U/V; frozen derivWithin equations U/V; generic-S joint analyticity of frozen iteratedDeriv U/V; exact a.e./continuous completeness statements; complex on-strip coordinate equation; explicit off-strip zero; full-strip analyticAt; complex feature coordinates equal real-feature coordinates at real x; oddExt at π; exact global oddness; zero support when π≤|x|. A first audit-probe run failed solely on an unnecessary tactic after simp and an omitted local inequality in a linarith step; correcting those transient probe proofs gave the stated pass. Package sources were unchanged.

5. Required SLIM lint wrapper (runs scripts/lint_sources.sh with the prescribed full-build ABI overlay):

```sh
LEAN_NUM_THREADS=1 nice -n 5 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpb
```

Exit 0. Complete output:

```text
check_lean_modules: PASS (1631 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

No stale-root exception or other lint waiver was needed.

6. Protected paths and diff hygiene:

```sh
git diff inp...HEAD -- KAM/Frozen manifest README.md
git diff --check inp...HEAD
```

Both exit 0, empty output. Full three-dot diff consists only of the three new modules, the package handoff, KAM.lean's single generated Wave import and the new 19-line generated KAM/Root/Wave.lean. Those generated changes are the explicit AUDIT FOCUS exception; they contain only root imports/header, and were not regenerated during this audit. The three implementation files have 315 / 331 / 224 physical lines (SineFeature / ReconAnalytic / SineCompleteness), below 1500. Direct token scan of the new implementation found no sorry/admit/axiom/unsafe/opaque/set_option/EuclideanSpace. Every implementation is a module with copyright, public imports, module docstring and exposed public noncomputable section. All project imports are the other package module or the six SEALED frozen definitions; their import closure contains no provider or draft theorem.

## Source defects, uncertainties and closeout

Suspected pinned-source or blueprint mathematical defects: **none found within the requested slice**. N2 quotes the exact blueprint endpoint convention and records its a.e.-equivalent implementation deviation; N3 records the unproved sharp intermediate bound rather than claiming the package proves it. No deviations were introduced by the auditor.

Audit limits: no W2 consumer implementation or entire PDE theorem was audited or compiled; only the exact generic theorem applications needed for those consumers were checked. No P96-W PDF re-audit was attempted; mathematical authority for this package is the specified blueprint slice and frozen definitions. The existing frozen NLW2 statement remains unproved. These results supply infrastructure, not PDE KAM closure, seal readiness of NLW2, or completion of all W1.

Closeout: source/type/definition inspection complete; all 86 public declarations inventoried and axiom-checked; targeted gate and three-module kernel replay passed; exact-type/boundary probes passed; protected paths unchanged; scratch probes removed; only this requested report is a repository edit. Lint outcome is recorded above.
