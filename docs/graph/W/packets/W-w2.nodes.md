NODE: bpW:w2:ext-deriv
KIND: external
TITLE: One-variable calculus
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-deriv@L40-L48
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:ext-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: a continuous linear map composed with a curve differentiable at t is differentiable at t with the image derivative; d/ds <Psi(s),y> = <Psi'(s),y>; derivatives are unique; translation: if F has derivative d at 0 then s -> F(s-t) has derivative d at t; a two-sided derivative is a derivative within any set; on [0,pi] (pi > 0) derivatives within are unique, so derivWithin f (Icc 0 pi) x equals any f' with HasDerivWithinAt f f' (Icc 0 pi) x
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:ext-an
KIND: external
TITLE: Analytic maps on $\R\times\R$
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-an@L49-L54
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:ext-an
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: the projections of R x R and the affine maps t -> theta_0 + t nu are analytic; sums, products and powers of real analytic functions are analytic; analytic maps are differentiable and continuous; continuity at every point of a set gives ContinuousOn
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:ext-sums
KIND: external
TITLE: Series and norms
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-sums@L55-L60
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:ext-sums
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: tsum_congr (termwise equal series have equal tsum, no summability needed); Summable.tsum_sub, Summable.tsum_add, tsum_mul_left for summable series; tsum_zero; comparison; summability of j^k e^{-j} for every k in N, and sum_{j>=1} e^{-2j} = (e^2-1)^{-1} (geometric series); Cauchy-Schwarz ¦<Psi,y>¦ <= ¦¦Psi¦¦ ¦¦y¦¦; on a product norm_fst_le, norm_snd_le
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w2
REVIEWER: sol-delta-W-w2
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: -

NODE: bpW:w2:ext-trig
KIND: external
TITLE: Trigonometry
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:ext-trig@L61-L64
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:ext-trig
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: none (Mathlib-level external fact)
SOURCE_QUANTIFIERS: as stated in the item
SOURCE_CONCLUSION: sin 0 = 0, sin(n pi) = 0 for n in N; ¦sin¦, ¦cos¦ <= 1; d/dx sin(jx) = j cos(jx), d/dx cos(jx) = -j sin(jx); sqrt(lambda) sqrt(lambda) = lambda and lambda/sqrt(lambda) = sqrt(lambda) for lambda > 0; lambda_j^2 = j^2 + m
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: -
ROUTES: -
ROUTE_FOR: -
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w2
REVIEWER: sol-delta-W-w2
LEAN_STATUS: EXTERNAL
LEAN_REF: -
LEAN_NOTE: -
NOTE: Writer adjudication of the sol-review-W-w2 replacement: an external must be a dependency leaf (linter), so the proposed edge to bpW:w0:basis#lam is dropped; the identity lambda_j^2 = j^2 + m is applied to the frozen lambda_j at the consumers (stepW:w2:flin, stepW:w2:t1), which depend on bpW:w0:basis#lam.

NODE: bpW:w2:derived
KIND: definition
TITLE: Derived reconstructions
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:derived@L70-L76
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:derived
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: y in l^2_R, x in R (standing data a = p = 1, kappa = kappa_{1,1})
SOURCE_QUANTIFIERS: y, x
SOURCE_CONCLUSION: defines D^0 y(x) = U_m(y)(x) (frozen reconU m hm y x), D^1 y(x) = sum_j kappa(y)_j/sqrt(lambda_j) sqrt(2/pi) j cos(jx), D^2 y(x) = -sum_j kappa(y)_j/sqrt(lambda_j) sqrt(2/pi) j^2 sin(jx) as tsums over N_+ (non-frozen helpers)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:ellap#coeff, bpW:w0:basis#lam, bpW:w0:reconstruction#reconU
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:derived@L72-L72 | kappa(y)_j = coeff y j
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:derived@L72-L72 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:derived@L71-L71 | U_m occurs directly here (frozen reconU)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.reconUx, KAM.Wave.reconUxx, KAM.Wave.reconUx_eq_iter, KAM.Wave.reconUxx_eq_iter, KAM.Wave.reconWaveC0, KAM.Wave.reconWaveBound (KAM/Wave/Recon2/Functionals.lean)
LEAN_NOTE: definition formalized by W2-RECON; W2-RECON audit 1 PASS WITH NOTES; D^0 is frozen reconU; (1+m)^{1/4} written sqrt(sqrt(1+m)) (equal, bridge checked)
NOTE: -

NODE: bpW:w2:functionals
KIND: lemma
TITLE: Reconstruction functionals
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L81-L92
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L94-L124
CONTRACT_ID: bpW:w2:functionals
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing data (m > 0, a = p = 1); c_0 = sqrt(2/pi) (e^2-1)^{-1/2}
SOURCE_QUANTIFIERS: there exist Psi^0, Psi^1, Psi^2, Psi^V; then for all y in l^2_R and x in R
SOURCE_CONCLUSION: there are real analytic Psi^0, Psi^1, Psi^2, Psi^V : R -> l^2_R (AnalyticOnNhd R Psi univ) such that (i) D^k y(x) = <Psi^k(x),y> (k = 0,1,2) and V_m(y)(x) = <Psi^V(x),y>, the four series absolutely convergent; (ii) ¦¦Psi^0(x)¦¦, ¦¦Psi^1(x)¦¦ <= c_0, ¦¦Psi^V(x)¦¦ <= (1+m)^{1/4} c_0, hence ¦D^0y(x)¦, ¦D^1y(x)¦ <= c_0 ¦¦y¦¦ and ¦V_m(y)(x)¦ <= (1+m)^{1/4} c_0 ¦¦y¦¦; (iii) D^k y has derivative D^{k+1} y(x) at x (k = 0,1); (iv) D^0 y(0) = D^0 y(pi) = 0
CONSTANT_SCOPE: c_0 absolute; Psi^k independent of y and x
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:derived, stepW:w2:features, stepW:w2:pairing, stepW:w2:norms, stepW:w2:xder, stepW:w2:bdry, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:derived | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L85-L85 | D^k y
EDGE: stepW:w2:features | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L95-L95 | proof step
EDGE: stepW:w2:pairing | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L103-L103 | proof step
EDGE: stepW:w2:norms | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L108-L108 | proof step
EDGE: stepW:w2:xder | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L114-L114 | proof step
EDGE: stepW:w2:bdry | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L120-L120 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L96-L96 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L101-L101 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L88-L88 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L85-L85 | V_m occurs directly here (frozen reconV)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:functionals@L107-L107 | the frozen coeff occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.reconWave_functionals, KAM.Wave.norm_reconFeatureU_le, KAM.Wave.norm_reconFeatureV_le, KAM.Wave.abs_reconU_le, KAM.Wave.abs_reconUx_le, KAM.Wave.abs_reconV_le, KAM.Wave.summable_abs_reconU_terms, KAM.Wave.summable_abs_reconUx_terms, KAM.Wave.summable_abs_reconUxx_terms, KAM.Wave.summable_abs_reconV_terms, KAM.Wave.reconU_apply_zero, KAM.Wave.reconU_apply_pi (KAM/Wave/Recon2/Functionals.lean)
LEAN_NOTE: W2-RECON audit 1 PASS WITH NOTES; bundle plus separate exports jointly supply all items
NOTE: -

NODE: stepW:w2:features
KIND: step
TITLE: Choice of the features
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L95-L102
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L95-L102
CONTRACT_ID: stepW:w2:features
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:functionals: standing data (m > 0, a = p = 1); c_0 = sqrt(2/pi) (e^2-1)^{-1/2}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:functionals (there exist Psi^0, Psi^1, Psi^2, Psi^V; then for all y in l^2_R and x in R); m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Lemma bpW:w1:sine-feature with a = p = 1 applies to beta_j = lambda_j^{-1/2} (B = 1, nu = 0) and beta_j = lambda_j^{1/2} (B = (1+m)^{1/4}, nu = 1/2); the real restrictions Psi^k, Psi^V are real analytic with coordinates Psi^k(x)_j = lambda_j^{-1/2} phi_j^(k)(x)/omega(j), Psi^V(x)_j = lambda_j^{1/2} phi_j(x)/omega(j)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:sine-feature, bpW:w0:basis#lambda-facts, bpW:w0:mass, bpW:w0:basis#lam, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L96-L96 | with a = p = 1 and the two choices of beta; (ii) real analyticity
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L97-L97 | lambda_j > j >= 1
EDGE: bpW:w0:mass | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L98-L98 | lambda_j^2 = j^2 + m <= (1+m) j^2
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L96-L96 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:features@L101-L101 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.reconWave_functionals, KAM.Wave.reconFeatureU_coord_sq_le, KAM.Wave.reconFeatureV_coord_sq_le (KAM/Wave/Recon2/Functionals.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:functionals; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:pairing
KIND: step
TITLE: Pairings
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L103-L107
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L103-L107
CONTRACT_ID: stepW:w2:pairing
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:functionals: standing data (m > 0, a = p = 1); c_0 = sqrt(2/pi) (e^2-1)^{-1/2}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:functionals (there exist Psi^0, Psi^1, Psi^2, Psi^V; then for all y in l^2_R and x in R); within the step: y, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: <Psi^k(x),y> and <Psi^V(x),y> equal termwise the summands of reconU, of D^1, D^2 and of reconV, so the tsums agree; this is (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:sine-feature, stepW:w2:features, bpW:w2:derived, bpW:w2:ext-sums, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:sine-feature | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L104-L104 | (iii): the pairings as absolutely convergent series
EDGE: stepW:w2:features | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L104-L104 | the feature maps Psi^k, Psi^V
EDGE: bpW:w2:derived | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L106-L106 | the summands of D^1, D^2
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L107-L107 | tsum_congr
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L104-L104 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L104-L104 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L106-L106 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L106-L106 | V_m occurs directly here (frozen reconV)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:pairing@L107-L107 | the frozen coeff occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.reconU_eq_inner, KAM.Wave.reconUx_eq_inner, KAM.Wave.reconUxx_eq_inner, KAM.Wave.reconV_eq_inner (KAM/Wave/Recon2/Functionals.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:functionals; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:norms
KIND: step
TITLE: Norms
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L108-L113
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L108-L113
CONTRACT_ID: stepW:w2:norms
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:functionals: standing data (m > 0, a = p = 1); c_0 = sqrt(2/pi) (e^2-1)^{-1/2}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:functionals (there exist Psi^0, Psi^1, Psi^2, Psi^V; then for all y in l^2_R and x in R); within the step: x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: ¦¦Psi^k(x)¦¦^2 <= (2/pi) sum_j lambda_j^{-1} j^{2k-2} e^{-2j} <= c_0^2 for k = 0,1, and ¦¦Psi^V(x)¦¦^2 <= (1+m)^{1/2} c_0^2; with Cauchy-Schwarz this gives (ii)
CONSTANT_SCOPE: c_0 absolute
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:features, bpW:w0:basis#lambda-facts, bpW:w1:ext-lp, bpW:w2:ext-sums, stepW:w2:pairing, bpW:w0:basis#lam, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:features | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L109-L109 | the coordinates of Psi^k, Psi^V
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L110-L110 | lambda_j^{-1} < 1 and lambda_j j^{-2} <= (1+m)^{1/2} j^{-1}
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L113-L113 | norm bounds from finite partial sums
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L113-L113 | Cauchy-Schwarz
EDGE: stepW:w2:pairing | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L113-L113 | (i) for the pointwise bounds
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L109-L109 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:norms@L109-L109 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.norm_reconFeatureU_le, KAM.Wave.norm_reconFeatureV_le, KAM.Wave.abs_reconU_le, KAM.Wave.abs_reconUx_le, KAM.Wave.abs_reconV_le (KAM/Wave/Recon2/Functionals.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:functionals; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:xder
KIND: step
TITLE: $x$-derivatives
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L114-L119
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L114-L119
CONTRACT_ID: stepW:w2:xder
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:functionals: standing data (m > 0, a = p = 1); c_0 = sqrt(2/pi) (e^2-1)^{-1/2}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:functionals (there exist Psi^0, Psi^1, Psi^2, Psi^V; then for all y in l^2_R and x in R); within the step: x, y; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (Psi^k)'(x) = Psi^{k+1}(x) for k = 0,1, and x -> <Psi^k(x),y> has derivative <Psi^{k+1}(x),y>; with (i) this is (iii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:recder, bpW:w2:ext-trig, bpW:w2:ext-deriv, stepW:w2:pairing, bpW:w0:basis#lam, bpW:w0:basis#sineMode
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:recder | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L115-L115 | the derivative of the analytic feature map has the coordinatewise derivatives
EDGE: bpW:w2:ext-trig | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L116-L116 | derivatives of sin(jx), cos(jx)
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L119-L119 | derivative of the pairing with fixed y
EDGE: stepW:w2:pairing | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L119-L119 | (i)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L117-L117 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:xder@L117-L117 | the sine modes phi_j occur directly here (frozen sineMode)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.hasDerivAt_reconU_reconUx, KAM.Wave.hasDerivAt_reconUx_reconUxx (KAM/Wave/Recon2/Functionals.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:functionals; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:bdry
KIND: step
TITLE: Boundary values
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L120-L123
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L120-L123
CONTRACT_ID: stepW:w2:bdry
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:functionals: standing data (m > 0, a = p = 1); c_0 = sqrt(2/pi) (e^2-1)^{-1/2}
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:functionals (there exist Psi^0, Psi^1, Psi^2, Psi^V; then for all y in l^2_R and x in R); within the step: y; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: phi_j(0) = phi_j(pi) = 0 for j in N_+, so every summand of reconU m hm y 0 and reconU m hm y pi vanishes and the tsum is 0; this is (iv)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-trig, bpW:w2:ext-sums, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-trig | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L121-L121 | sin 0 = 0, sin(j pi) = 0
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L123-L123 | tsum_zero
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L121-L121 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bdry@L122-L122 | U_m occurs directly here (frozen reconU)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.reconU_apply_zero, KAM.Wave.reconU_apply_pi (KAM/Wave/Recon2/Functionals.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:functionals; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: bpW:w2:force
KIND: lemma
TITLE: Force identity in frozen form
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L128-L137
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L139-L160
CONTRACT_ID: bpW:w2:force
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: standing data; y in l^2_R; Sigma_lin(x) = sum_j sqrt(lambda_j) lambda_j kappa(y)_j phi_j(x), Sigma_cub(x) = sum_j sqrt(lambda_j) G(y)_j phi_j(x) with G(y)_j = cubicGrad m hm y j
SOURCE_QUANTIFIERS: for all y; for every x in R (convergence, (i)); for every x in [0,pi] ((ii))
SOURCE_CONCLUSION: both series converge absolutely; (i) Sigma_lin(x) = -D^2 y(x) + m D^0 y(x) for every x in R; (ii) Sigma_cub(x) = U_m(y)(x)^3 for every x in [0,pi]
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:derived, stepW:w2:fsum, stepW:w2:flin, stepW:w2:fcub, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:derived | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L134-L134 | D^0 y and D^2 y
EDGE: stepW:w2:fsum | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L140-L140 | proof step
EDGE: stepW:w2:flin | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L148-L148 | proof step
EDGE: stepW:w2:fcub | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L154-L154 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L130-L130 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L130-L130 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L134-L134 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L131-L131 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:force@L130-L130 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w2
REVIEWER: sol-delta-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.reconWave_force, KAM.Wave.reconWave_force_summable_lin, KAM.Wave.reconWave_force_summable_cub, KAM.Wave.reconWave_force_lin, KAM.Wave.reconWave_force_cub (KAM/Wave/Recon2/Force.lean)
LEAN_NOTE: W2-RECON audit 1 PASS WITH NOTES; cubic identity on [0,pi], its source domain
NOTE: -

NODE: stepW:w2:fsum
KIND: step
TITLE: Summability
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L140-L147
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L140-L147
CONTRACT_ID: stepW:w2:fsum
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:force: standing data; y in l^2_R; Sigma_lin(x) = sum_j sqrt(lambda_j) lambda_j kappa(y)_j phi_j(x), Sigma_cub(x) = sum_j sqrt(lambda_j) G(y)_j phi_j(x) with G(y)_j = cubicGrad m hm y j
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:force (for all y; for every x in R (convergence, (i)); for every x in [0,pi] ((ii))); within the step: y, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: the summands of Sigma_lin are at most sqrt(2/pi)(1+m)^{3/4} ¦¦y¦¦ j e^{-j}, those of Sigma_cub at most sqrt(2/pi)(1+m)^{1/4} ¦¦G^w(y)¦¦ e^{-j}; both majorants are summable; D^0 y(x), D^2 y(x) converge absolutely
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:ext-lp, bpW:w0:basis#lambda-facts, bpW:w1:cubic-analytic, bpW:w2:ext-sums, bpW:w2:functionals, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:ext-lp | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L141-L141 | ¦kappa(y)_j¦ <= ¦¦y¦¦/(j e^j)
EDGE: bpW:w0:basis#lambda-facts | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L141-L141 | sqrt(lambda_j) lambda_j <= (1+m)^{3/4} j^{3/2}
EDGE: bpW:w1:cubic-analytic | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L143-L143 | (iv): G(y)_j = G^w(y)_j/omega_{1,2}(j), G^w(y) in l^2_R
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L146-L146 | comparison and summability of the majorants
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L147-L147 | (i): absolute convergence of D^0 y(x), D^2 y(x)
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L141-L141 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L142-L142 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L146-L146 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L143-L143 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fsum@L141-L141 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w2
REVIEWER: sol-delta-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.reconWave_force_summable_lin, KAM.Wave.reconWave_force_summable_cub (KAM/Wave/Recon2/Force.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:force; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:flin
KIND: step
TITLE: Linear part
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L148-L153
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L148-L153
CONTRACT_ID: stepW:w2:flin
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:force: standing data; y in l^2_R; Sigma_lin(x) = sum_j sqrt(lambda_j) lambda_j kappa(y)_j phi_j(x), Sigma_cub(x) = sum_j sqrt(lambda_j) G(y)_j phi_j(x) with G(y)_j = cubicGrad m hm y j
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:force (for all y; for every x in R (convergence, (i)); for every x in [0,pi] ((ii))); within the step: y, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: termwise sqrt(lambda_j) lambda_j = (j^2+m)/sqrt(lambda_j), so the j-th summand of Sigma_lin is minus that of D^2 y plus m times that of D^0 y; summing gives (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-trig, bpW:w2:derived, stepW:w2:fsum, bpW:w2:ext-sums, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-trig | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L149-L149 | lambda/sqrt(lambda) identities and lambda_j^2 = j^2 + m
EDGE: bpW:w2:derived | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L151-L151 | the summands of D^0, D^2
EDGE: stepW:w2:fsum | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L151-L151 | absolute convergence of both series
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L152-L152 | Summable.tsum_add, tsum_mul_left
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L149-L149 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L150-L150 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L151-L151 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:flin@L150-L150 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w2
REVIEWER: sol-delta-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.lam_sq_eq, KAM.Wave.reconWave_lin_term, KAM.Wave.reconWave_force_lin (KAM/Wave/Recon2/Force.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:force; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:fcub
KIND: step
TITLE: Cubic part
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L154-L159
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L154-L159
CONTRACT_ID: stepW:w2:fcub
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:force: standing data; y in l^2_R; Sigma_lin(x) = sum_j sqrt(lambda_j) lambda_j kappa(y)_j phi_j(x), Sigma_cub(x) = sum_j sqrt(lambda_j) G(y)_j phi_j(x) with G(y)_j = cubicGrad m hm y j
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:force (for all y; for every x in R (convergence, (i)); for every x in [0,pi] ((ii))); within the step: y, x in [0,pi]; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: U_m(y) = U_m(q) and G(y) = G_q(q) for q = kappa(y) in l^{1,1}; the first identity of (bpW:w0n:force) gives U_m(q)^3 = sum_l sqrt(lambda_l) G_q(q)_l phi_l on [0,pi], which is (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w1:trifrozen, stepW:w0n:force, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w1:trifrozen | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L155-L155 | the frozen reconU and cubicGrad are U_m and G_q of q = kappa(y)
EDGE: stepW:w0n:force | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L157-L157 | the force identity U_m(q)^3 = sum sqrt(lambda_l) G_q(q)_l phi_l
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L158-L158 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L158-L158 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L155-L155 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L155-L155 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:fcub@L156-L156 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w2
REVIEWER: sol-delta-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.reconWave_force_cub (KAM/Wave/Recon2/Force.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:force; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: bpW:w2:coeffsol
KIND: definition
TITLE: Analytic coefficient solution
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:coeffsol@L166-L174
PROOF_SOURCE: -
CONTRACT_ID: bpW:w2:coeffsol
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: typing data: Y : R -> WaveSpace (standing data)
SOURCE_QUANTIFIERS: Y
SOURCE_CONCLUSION: defines: Y is an analytic coefficient solution iff (C1) Y is real analytic at every t (forall t, AnalyticAt R Y t) and (C2) for all t and j in N_+, s -> coeff (Y s).1 j has derivative lambda_j coeff (Y t).2 j at t and s -> coeff (Y s).2 j has derivative -lambda_j coeff (Y t).1 j - cubicGrad m hm (Y t).1 j at t (HasDerivAt)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w0:eqmotion, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w0:eqmotion | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:coeffsol@L176-L176 | (C2) is the coefficient system (bpW:w0:coeffsys) read coordinatewise
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:coeffsol@L171-L171 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:coeffsol@L172-L172 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:coeffsol@L170-L170 | the frozen coeff occurs directly here
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:coeffsol@L167-L167 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.IsAnalyticCoeffSolution (KAM/Wave/Recon2/Orbit.lean)
LEAN_NOTE: definition formalized by W2-RECON; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: bpW:w2:orbit
KIND: lemma
TITLE: Torus orbits are analytic coefficient solutions
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L178-L190
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L192-L202
CONTRACT_ID: bpW:w2:orbit
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: K : (Fin 2 -> R) -> WaveSpace with AnalyticOnNhd R K univ; nu : Fin 2 -> R such that for all theta and j in N_+ the invariance (bpW:w2:inv) holds, each as a HasDerivAt at 0 of t -> coeff (K(theta + t nu)).i j (the frozen conclusion (4) of nlw2 for one I)
SOURCE_QUANTIFIERS: for all K, nu as stated; for every theta_0
SOURCE_CONCLUSION: Y(t) = K(theta_0 + t nu) is an analytic coefficient solution
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:coeffsol, stepW:w2:oan, stepW:w2:oshift, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff, bpW:w0:ellap#WaveSpace
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:coeffsol | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L189-L189 | the notion of analytic coefficient solution
EDGE: stepW:w2:oan | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L193-L193 | proof step
EDGE: stepW:w2:oshift | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L196-L196 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L183-L183 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L184-L184 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L197-L197 | the frozen coeff occurs directly here
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:orbit@L179-L179 | the frozen WaveSpace occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.isAnalyticCoeffSolution_orbit (KAM/Wave/Recon2/Orbit.lean)
LEAN_NOTE: W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:oan
KIND: step
TITLE: Analyticity
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oan@L193-L195
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oan@L193-L195
CONTRACT_ID: stepW:w2:oan
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:orbit: K : (Fin 2 -> R) -> WaveSpace with AnalyticOnNhd R K univ; nu : Fin 2 -> R such that for all theta and j in N_+ the invariance (bpW:w2:inv) holds, each as a HasDerivAt at 0 of t -> coeff (K(theta + t nu)).i j (the frozen conclusion (4) of nlw2 for one I)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:orbit (for all K, nu as stated; for every theta_0); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: t -> theta_0 + t nu is analytic and K is analytic at its value, so Y is analytic at t ((C1))
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-an
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-an | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oan@L195-L195 | affine maps are analytic; AnalyticAt.comp
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.isAnalyticCoeffSolution_orbit (KAM/Wave/Recon2/Orbit.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:orbit; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:oshift
KIND: step
TITLE: Shift
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L196-L201
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L196-L201
CONTRACT_ID: stepW:w2:oshift
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:orbit: K : (Fin 2 -> R) -> WaveSpace with AnalyticOnNhd R K univ; nu : Fin 2 -> R such that for all theta and j in N_+ the invariance (bpW:w2:inv) holds, each as a HasDerivAt at 0 of t -> coeff (K(theta + t nu)).i j (the frozen conclusion (4) of nlw2 for one I)
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:orbit (for all K, nu as stated; for every theta_0); within the step: t, j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: applying (bpW:w2:inv) at theta = theta_0 + t nu and translating, s -> coeff (Y s).i j has the derivative required by (C2) at t
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-deriv, bpW:w0:basis#lam, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L198-L198 | the translation rule for derivatives
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L201-L201 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:oshift@L197-L197 | the frozen coeff occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.isAnalyticCoeffSolution_orbit (KAM/Wave/Recon2/Orbit.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:orbit; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: bpW:w2:curve-deriv
KIND: lemma
TITLE: Coefficients of the curve derivative
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L206-L210
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L212-L220
CONTRACT_ID: bpW:w2:curve-deriv
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Y an analytic coefficient solution; t in R
SOURCE_QUANTIFIERS: for all Y, t; j in N_+
SOURCE_CONCLUSION: Y_1 = (Y .).1 and Y_2 = (Y .).2 are differentiable at t as maps R -> l^2_R and, with Y_i'(t) their derivatives, kappa(Y_1'(t))_j = lambda_j kappa(Y_2(t))_j and kappa(Y_2'(t))_j = -lambda_j kappa(Y_1(t))_j - G(Y_1(t))_j
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:coeffsol, stepW:w2:cdiff, stepW:w2:ccoord, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:coeffsol | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L207-L207 | analytic coefficient solution
EDGE: stepW:w2:cdiff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L213-L213 | proof step
EDGE: stepW:w2:ccoord | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L216-L216 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L209-L209 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L209-L209 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve-deriv@L209-L209 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w2
REVIEWER: sol-delta-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.hasDerivAt_coeffSol, KAM.Wave.hasDerivAt_coeffSol_fst, KAM.Wave.hasDerivAt_coeffSol_snd, KAM.Wave.coeff_deriv_coeffSol_fst, KAM.Wave.coeff_deriv_coeffSol_snd (KAM/Wave/Recon2/Orbit.lean)
LEAN_NOTE: W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:cdiff
KIND: step
TITLE: Differentiability
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L213-L215
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L213-L215
CONTRACT_ID: stepW:w2:cdiff
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve-deriv: Y an analytic coefficient solution; t in R
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve-deriv (for all Y, t; j in N_+); within the step: t; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: Y_i is analytic at t (composite with the continuous linear projection), hence differentiable
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:ext-an, bpW:w2:coeffsol
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:ext-an | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L215-L215 | analytic maps are differentiable
EDGE: bpW:w2:coeffsol | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:cdiff@L214-L214 | analyticity of Y comes from C1 of the analytic coefficient solution package
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w2
REVIEWER: sol-delta-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.hasDerivAt_coeffSol, KAM.Wave.hasDerivAt_coeffSol_fst, KAM.Wave.hasDerivAt_coeffSol_snd (KAM/Wave/Recon2/Orbit.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:curve-deriv; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:ccoord
KIND: step
TITLE: Coordinates
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L216-L219
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L216-L219
CONTRACT_ID: stepW:w2:ccoord
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve-deriv: Y an analytic coefficient solution; t in R
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve-deriv (for all Y, t; j in N_+); within the step: t, j; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: s -> kappa(Y_i(s))_j has derivative kappa(Y_i'(t))_j and, by (C2), the derivative stated there; uniqueness gives the identities
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w1:coordinatewise, stepW:w2:cdiff, bpW:w2:ext-deriv, bpW:w2:coeffsol, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w1:coordinatewise | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L217-L217 | with (a,p) = (a',p') = (1,1), hat iota = id, v = Y_i'(t)
EDGE: stepW:w2:cdiff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L217-L217 | Y_i differentiable at t
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L219-L219 | uniqueness of derivatives
EDGE: bpW:w2:coeffsol | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L218-L218 | the second derivative value is supplied by C2 of the package
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:ccoord@L218-L218 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w2
REVIEWER: sol-delta-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.coeff_deriv_coeffSol_fst, KAM.Wave.coeff_deriv_coeffSol_snd (KAM/Wave/Recon2/Orbit.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:curve-deriv; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: bpW:w2:curve
KIND: theorem
TITLE: P96-W Lemma~1 in frozen form
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L233-L249
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L251-L296
CONTRACT_ID: bpW:w2:curve
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]
SOURCE_CONCLUSION: (i) each of the five functions, uncurried, is real analytic at every point of R x R; (ii) s -> u(s,x) has derivative u_t(t,x) at t; (iii) for x in [0,pi], s -> u_t(s,x) has derivative u_tt(t,x) at t; (iv) u(t,.) has derivative u_x(t,x) and u_x(t,.) has derivative u_xx(t,x) at x; (v) IsClassicalSolution m hm u with witnesses (u_t,u_x,u_tt,u_xx); (vi) for x in [0,pi], derivWithin (u t) (Icc 0 pi) x = u_x(t,x) and ¦u(t,x)¦ + ¦derivWithin (u t) (Icc 0 pi) x¦ + ¦V_m(Y_2(t))(x)¦ <= M_m ¦¦Y(t)¦¦
CONSTANT_SCOPE: M_m depends only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:coeffsol, bpW:w2:derived, bpW:w2:functionals, stepW:w2:joint, stepW:w2:t1, stepW:w2:t2, stepW:w2:x, stepW:w2:frozen, stepW:w2:bound, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:Gq#cubicGrad, bpW:w0:nlw#IsClassicalSolution
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:coeffsol | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L234-L234 | analytic coefficient solution
EDGE: bpW:w2:derived | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L236-L236 | u_x = D^1 Y_1(t), u_xx = D^2 Y_1(t)
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L238-L238 | c_0
EDGE: stepW:w2:joint | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L252-L252 | proof step
EDGE: stepW:w2:t1 | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L263-L263 | proof step
EDGE: stepW:w2:t2 | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L271-L271 | proof step
EDGE: stepW:w2:x | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L279-L279 | proof step
EDGE: stepW:w2:frozen | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L281-L281 | proof step
EDGE: stepW:w2:bound | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L290-L290 | proof step
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L267-L267 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L268-L268 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L235-L235 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L235-L235 | V_m occurs directly here (frozen reconV)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L274-L274 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:curve@L245-L245 | the frozen IsClassicalSolution occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.reconWave_curve, KAM.Wave.analyticAt_reconWave_u, KAM.Wave.analyticAt_reconWave_ux, KAM.Wave.analyticAt_reconWave_uxx, KAM.Wave.analyticAt_reconWave_ut, KAM.Wave.analyticAt_reconWave_utt, KAM.Wave.hasDerivAt_reconWave_ut, KAM.Wave.hasDerivAt_reconWave_utt, KAM.Wave.hasDerivAt_reconWave_ux, KAM.Wave.isClassicalSolution_reconWave, KAM.Wave.reconWave_bound (KAM/Wave/Recon2/Curve.lean)
LEAN_NOTE: W2-RECON audit 1 PASS WITH NOTES; (iv) and (vi) proved for arbitrary vector/curve, no coefficient ODE needed (stronger)
NOTE: -

NODE: stepW:w2:joint
KIND: step
TITLE: Joint analyticity
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L252-L262
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L252-L262
CONTRACT_ID: stepW:w2:joint
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve (for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]); within the step: (s_0,x_0) in R^2; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (s,x) -> <Psi(x),Y_i(s)> are real analytic at every point; by (i) of Lemma bpW:w2:functionals these are u, u_x, u_xx, u_t; u_tt is a polynomial in u, u_xx; this is (i)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:cdiff, bpW:w1:recon-analytic, bpW:w2:ext-an, bpW:w1:ext-analytic, bpW:w2:functionals, bpW:w0:reconstruction#reconV
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:cdiff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L253-L253 | Y_1, Y_2 analytic at every t
EDGE: bpW:w1:recon-analytic | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L253-L253 | (iii) with parameter domain R
EDGE: bpW:w2:ext-an | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L257-L257 | pairs, projections and polynomials of analytic maps
EDGE: bpW:w1:ext-analytic | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L259-L259 | the continuous bilinear inner product is analytic
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L259-L259 | (i): the functions are the pairings
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:joint@L254-L254 | V_m occurs directly here (frozen reconV)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.analyticAt_coeffSol_fst, KAM.Wave.analyticAt_coeffSol_snd, KAM.Wave.analyticAt_reconWave_u, KAM.Wave.analyticAt_reconWave_ux, KAM.Wave.analyticAt_reconWave_uxx, KAM.Wave.analyticAt_reconWave_ut, KAM.Wave.analyticAt_reconWave_utt (KAM/Wave/Recon2/Curve.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:curve; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:t1
KIND: step
TITLE: First time derivative
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L263-L270
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L263-L270
CONTRACT_ID: stepW:w2:t1
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve (for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]); within the step: t, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: s -> u(s,x) has derivative <Psi^0(x),Y_1'(t)> = U_m(Y_1'(t))(x) = V_m(Y_2(t))(x) = u_t(t,x); this is (ii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:functionals, bpW:w2:ext-deriv, bpW:w2:curve-deriv, bpW:w2:ext-trig, bpW:w2:ext-sums, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L265-L265 | (i): D^0 y(x) = <Psi^0(x),y> continuous linear in y
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L266-L266 | derivative of a continuous linear image of a curve
EDGE: bpW:w2:curve-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L267-L267 | kappa(Y_1'(t))_j = lambda_j kappa(Y_2(t))_j
EDGE: bpW:w2:ext-trig | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L267-L267 | lambda/sqrt(lambda) = sqrt(lambda)
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L270-L270 | tsum_congr
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L267-L267 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L268-L268 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L264-L264 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L270-L270 | V_m occurs directly here (frozen reconV)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t1@L268-L268 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w2
REVIEWER: sol-delta-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.reconU_eq_reconV_of_coeff, KAM.Wave.hasDerivAt_reconWave_ut (KAM/Wave/Recon2/Curve.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:curve; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:t2
KIND: step
TITLE: Second time derivative
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L271-L278
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L271-L278
CONTRACT_ID: stepW:w2:t2
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve (for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]); within the step: t, x in [0,pi]; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: s -> u_t(s,x) has derivative V_m(Y_2'(t))(x) = -Sigma_lin(x) - Sigma_cub(x) = u_tt(t,x) for x in [0,pi]; this is (iii)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:functionals, bpW:w2:ext-deriv, bpW:w2:curve-deriv, stepW:w2:fsum, bpW:w2:ext-sums, bpW:w2:force, bpW:w0:basis#lam, bpW:w0:basis#sineMode, bpW:w0:reconstruction#reconV, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L272-L272 | (i): V_m(y)(x) = <Psi^V(x),y>
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L272-L272 | derivative of a continuous linear image of a curve
EDGE: bpW:w2:curve-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L273-L273 | the coordinates of Y_2'(t)
EDGE: stepW:w2:fsum | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L275-L275 | absolute convergence of Sigma_lin, Sigma_cub with y = Y_1(t)
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L276-L276 | Summable.tsum_sub
EDGE: bpW:w2:force | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L277-L277 | (i), (ii) on [0,pi]
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L274-L274 | lambda occurs directly here (frozen lam)
EDGE: bpW:w0:basis#sineMode | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L274-L274 | the sine modes phi_j occur directly here (frozen sineMode)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L272-L272 | V_m occurs directly here (frozen reconV)
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L274-L274 | the cubic gradient G_q occurs directly here (frozen cubicGrad)
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:t2@L274-L274 | kappa is the frozen coefficient map by the standing dictionary L28
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w2
REVIEWER: sol-delta-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.lam_mul_div_sqrt_lam, KAM.Wave.hasDerivAt_reconWave_utt (KAM/Wave/Recon2/Curve.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:curve; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:x
KIND: step
TITLE: Space derivatives
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:x@L279-L280
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:x@L279-L280
CONTRACT_ID: stepW:w2:x
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve (for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]); within the step: t, x; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (iv) is (iii) of Lemma bpW:w2:functionals with y = Y_1(t)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:functionals
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:x@L280-L280 | (iii)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.hasDerivAt_reconWave_ux (KAM/Wave/Recon2/Curve.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:curve; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:frozen
KIND: step
TITLE: The frozen definition
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L281-L289
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L281-L289
CONTRACT_ID: stepW:w2:frozen
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve (for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]); within the step: t, x in [0,pi]; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: unfolding IsClassicalSolution m hm u with witnesses (u_t,u_x,u_tt,u_xx): continuity on univ x Icc 0 pi from (i), the two time derivatives from (ii), (iii), the two x-derivatives within [0,pi] from (iv), the equation by definition of u_tt, the boundary values from (iv) of Lemma bpW:w2:functionals; this is (v)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:joint, bpW:w2:ext-an, stepW:w2:t1, stepW:w2:t2, stepW:w2:x, bpW:w2:ext-deriv, bpW:w2:functionals, bpW:w0:nlw#IsClassicalSolution
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:joint | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L283-L283 | (i): analyticity, hence continuity
EDGE: bpW:w2:ext-an | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L283-L283 | analytic implies continuous; ContinuousOn
EDGE: stepW:w2:t1 | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L286-L286 | (ii)
EDGE: stepW:w2:t2 | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L286-L286 | (iii)
EDGE: stepW:w2:x | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L287-L287 | (iv)
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L287-L287 | HasDerivAt.hasDerivWithinAt
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L289-L289 | (iv): boundary values
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:frozen@L282-L282 | the frozen IsClassicalSolution occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.isClassicalSolution_reconWave (KAM/Wave/Recon2/Curve.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:curve; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:bound
KIND: step
TITLE: Bound
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L290-L295
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L290-L295
CONTRACT_ID: stepW:w2:bound
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:curve: Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:curve (for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]); within the step: t, x in [0,pi]; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: derivWithin (u t) (Icc 0 pi) x = u_x(t,x) (endpoints included) and ¦u¦ + ¦u_x¦ + ¦V_m(Y_2(t))(x)¦ <= M_m ¦¦Y(t)¦¦; this is (vi)
CONSTANT_SCOPE: M_m depends only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: stepW:w2:frozen, bpW:w2:ext-deriv, bpW:w2:functionals, bpW:w2:ext-sums, bpW:w0:reconstruction#reconV
ROUTES: -
ROUTE_FOR: -
EDGE: stepW:w2:frozen | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L291-L291 | the derivative within [0,pi]
EDGE: bpW:w2:ext-deriv | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L292-L292 | uniqueness of derivatives within [0,pi]
EDGE: bpW:w2:functionals | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L293-L293 | (ii): the pointwise bounds
EDGE: bpW:w2:ext-sums | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L295-L295 | norm_fst_le, norm_snd_le
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:bound@L294-L294 | V_m occurs directly here (frozen reconV)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.reconWave_bound (KAM/Wave/Recon2/Curve.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:curve; W2-RECON audit 1 PASS WITH NOTES; derivWithin identified incl. endpoints
NOTE: -

NODE: bpW:w2:main
KIND: theorem
TITLE: PDE solutions on invariant tori
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L303-L321
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L323-L332
CONTRACT_ID: bpW:w2:main
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0; M_m as in Theorem bpW:w2:curve; K : (Fin 2 -> R) -> WaveSpace, nu : Fin 2 -> R, B in R with (H1) IsAnalyticTorusEmbedding K, (H2) the invariance (bpW:w2:inv) for every theta and j in N_+, (H3) ¦¦K(theta)¦¦ <= B for every theta
SOURCE_QUANTIFIERS: for all m > 0, K, nu, B as stated; for every theta_0; (a) for every z in univ x Icc 0 pi; (c), (d) for all t in R, x in [0,pi]
SOURCE_CONCLUSION: with u(t,x) = reconU m hm (K(theta_0 + t nu)).1 x: (a) AnalyticAt R (z -> reconU m hm (K(theta_0 + z.1 nu)).1 z.2) z; (b) IsClassicalSolution m hm u; (c) HasDerivAt (s -> reconU m hm (K(theta_0 + s nu)).1 x) (reconV m hm (K(theta_0 + t nu)).2 x) t; (d) ¦u(t,x)¦ + ¦derivWithin (u t) (Icc 0 pi) x¦ + ¦V_m(K(theta_0 + t nu).2)(x)¦ <= M_m B
CONSTANT_SCOPE: M_m depends only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:curve, bpW:w2:orbit, stepW:w2:mred, stepW:w2:mconc, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:ellap#WaveSpace, bpW:w0:nlw#IsClassicalSolution, bpW:wh:embedding#IsAnalyticTorusEmbedding
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:curve | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L304-L304 | M_m
EDGE: bpW:w2:orbit | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L308-L308 | (H2) is its invariance hypothesis (bpW:w2:inv)
EDGE: stepW:w2:mred | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L324-L324 | proof step
EDGE: stepW:w2:mconc | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L328-L328 | proof step
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L311-L311 | U_m occurs directly here (frozen reconU)
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L319-L319 | V_m occurs directly here (frozen reconV)
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L304-L304 | the frozen WaveSpace occurs directly here
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L315-L315 | the frozen IsClassicalSolution occurs directly here
EDGE: bpW:wh:embedding#IsAnalyticTorusEmbedding | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:main@L307-L307 | the frozen IsAnalyticTorusEmbedding occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.reconWave_main, KAM.Wave.reconWave_main_le (KAM/Wave/Recon2/Main.lean)
LEAN_NOTE: W2-RECON audit 1 PASS WITH NOTES; exact H1-H3, no EXCESS binders, bound M_m B
NOTE: -

NODE: stepW:w2:mred
KIND: step
TITLE: Reduction to a curve
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L324-L327
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L324-L327
CONTRACT_ID: stepW:w2:mred
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:main: m > 0; M_m as in Theorem bpW:w2:curve; K : (Fin 2 -> R) -> WaveSpace, nu : Fin 2 -> R, B in R with (H1) IsAnalyticTorusEmbedding K, (H2) the invariance (bpW:w2:inv) for every theta and j in N_+, (H3) ¦¦K(theta)¦¦ <= B for every theta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:main (for all m > 0, K, nu, B as stated; for every theta_0; (a) for every z in univ x Icc 0 pi; (c), (d) for all t in R, x in [0,pi]); within the step: theta_0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: from the analyticity conjunct of (H1) and (H2), Y(t) = K(theta_0 + t nu) is an analytic coefficient solution, and the u of the two theorems coincide
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:orbit, bpW:wh:embedding#IsAnalyticTorusEmbedding, bpW:w0:reconstruction#reconU
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:orbit | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L326-L326 | torus orbits are analytic coefficient solutions
EDGE: bpW:wh:embedding#IsAnalyticTorusEmbedding | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L325-L325 | the analyticity premise is projected from the frozen embedding predicate
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mred@L327-L327 | the functions u are identified using their reconU definitions
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W+sol-review-W-w2
REVIEWER: sol-delta-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.reconWave_main, KAM.Wave.isAnalyticCoeffSolution_orbit (KAM/Wave/Recon2/Main.lean, KAM/Wave/Recon2/Orbit.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:main; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: stepW:w2:mconc
KIND: step
TITLE: Conclusions
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L328-L331
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L328-L331
CONTRACT_ID: stepW:w2:mconc
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of bpW:w2:main: m > 0; M_m as in Theorem bpW:w2:curve; K : (Fin 2 -> R) -> WaveSpace, nu : Fin 2 -> R, B in R with (H1) IsAnalyticTorusEmbedding K, (H2) the invariance (bpW:w2:inv) for every theta and j in N_+, (H3) ¦¦K(theta)¦¦ <= B for every theta
SOURCE_QUANTIFIERS: for every choice of the data of bpW:w2:main (for all m > 0, K, nu, B as stated; for every theta_0; (a) for every z in univ x Icc 0 pi; (c), (d) for all t in R, x in [0,pi]); within the step: theta_0; m > 0 fixed (standing assumption)
SOURCE_CONCLUSION: (a) is (i) of Theorem bpW:w2:curve restricted to R x [0,pi]; (b) is (v); (c) is (ii) restricted to [0,pi]; (d) is (vi) with ¦¦Y(t)¦¦ <= B by (H3) and M_m > 0
CONSTANT_SCOPE: M_m depends only on m
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:curve, stepW:w2:mred, bpW:w0:reconstruction#reconV
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:curve | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L329-L329 | (i), (ii), (v), (vi)
EDGE: stepW:w2:mred | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L329-L329 | Y is an analytic coefficient solution
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#stepW:w2:mconc@L330-L330 | V_m occurs directly here (frozen reconV)
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.reconWave_main (KAM/Wave/Recon2/Main.lean)
LEAN_NOTE: step of PROVED parent bpW:w2:main; W2-RECON audit 1 PASS WITH NOTES
NOTE: -

NODE: bpW:w2:clause5
KIND: corollary
TITLE: Clause (5) with the common constant
STATEMENT_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L347-L353
PROOF_SOURCE: blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L355-L360
CONTRACT_ID: bpW:w2:clause5
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: m > 0, C_3 > 0, Gamma subset Fin 2 -> R, nu : (Fin 2 -> R) -> Fin 2 -> R, K : (Fin 2 -> R) -> (Fin 2 -> R) -> WaveSpace; for every I in Gamma: K_I satisfies IsAnalyticTorusEmbedding, ¦¦K_I(theta)¦¦ <= C_3 sqrt(I_0+I_1) for all theta, and the invariance (4) of nlw2 holds; C = max(1,M_m) C_3
SOURCE_QUANTIFIERS: for all such m, C_3, Gamma, nu, K
SOURCE_CONCLUSION: C > 0, C >= C_3, ¦¦K_I(theta)¦¦ <= C sqrt(I_0+I_1), and conclusion (5) of nlw2 holds verbatim with this C
CONSTANT_SCOPE: C depends only on m and C_3 (C = max(1,M_m) C_3)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: bpW:w2:main, bpW:w2:curve, bpW:w0:basis#lam, bpW:w0:Gq#cubicGrad, bpW:w0:ellap#coeff, bpW:w0:reconstruction#reconU, bpW:w0:reconstruction#reconV, bpW:w0:nlw#IsClassicalSolution, bpW:w0:ellap#WaveSpace, bpW:wh:embedding#IsAnalyticTorusEmbedding
ROUTES: -
ROUTE_FOR: -
EDGE: bpW:w2:main | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L358-L358 | applied with K = K_I, nu = nu(I), B = C_3 sqrt(I_0+I_1)
EDGE: bpW:w2:curve | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L351-L351 | the constant M_m
EDGE: bpW:w0:basis#lam | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L351-L351 | (4) of nlw2 involves lambda_j
EDGE: bpW:w0:Gq#cubicGrad | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L351-L351 | (4) of nlw2 involves cubicGrad
EDGE: bpW:w0:ellap#coeff | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L351-L351 | (4) of nlw2 involves coeff
EDGE: bpW:w0:reconstruction#reconU | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L352-L352 | (5) of nlw2 involves reconU
EDGE: bpW:w0:reconstruction#reconV | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L352-L352 | (5) of nlw2 involves reconV
EDGE: bpW:w0:nlw#IsClassicalSolution | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L352-L352 | (5) of nlw2 involves IsClassicalSolution
EDGE: bpW:w0:ellap#WaveSpace | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L349-L349 | the frozen WaveSpace occurs directly here
EDGE: bpW:wh:embedding#IsAnalyticTorusEmbedding | blueprint-W/parts/w2-reconstruction.tex#bpW:w2:clause5@L350-L350 | the frozen IsAnalyticTorusEmbedding occurs directly here
TOPOLOGY_STATUS: REVIEWED
EXTRACTOR: claude-suborch-W
REVIEWER: sol-review-W-w2
LEAN_STATUS: PROVED
LEAN_REF: KAM.Wave.reconWave_clause5 (KAM/Wave/Recon2/Main.lean)
LEAN_NOTE: W2-RECON audit 1 PASS WITH NOTES; C = max 1 M_m * C_3; frozen clause (5) text consumed in a term-level probe; nlw2 itself stays DRAFT_SORRY
NOTE: Consumer: the W8 assembly (later wave) for the root bpW:wh:nlw2. The statement speaks of the form of conclusions (4)-(5) of nlw2; that is not a use of the root.
