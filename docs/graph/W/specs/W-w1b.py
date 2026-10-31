# Writer spec for slice W-w1b (blueprint-W/parts/w1-sequences.tex L591-end). Rendered by w_depgraph_fill.py.
F = "blueprint-W/parts/w1-sequences.tex"

NODES = {
    "bpW:w1:sine-completeness": dict(
        H="(i) f in L^2(0,pi) with int_0^pi f phi_l = 0 for all l >= 1; (ii) moreover f continuous on [0,pi]",
        Q="for all f", C="(i) f = 0 a.e. on (0,pi); (ii) f = 0 on [0,pi]", S="none",
        deps=[("bpW:w0:basis#sineMode", "L594", "the sine modes phi_l"),
              ("stepW:w1:odd", "L599", "proof step"), ("stepW:w1:coeffs", "L602", "proof step"),
              ("stepW:w1:basis", "L606", "proof step"), ("stepW:w1:cont", "L610", "proof step")]),
    "stepW:w1:odd": dict(
        H="f in L^2(0,pi)", Q="none", C="the odd extension g of f to R/2piZ lies in L^2 with ||g||^2 = 2||f||^2",
        S="none", deps=[]),
    "stepW:w1:coeffs": dict(
        H="g of Step stepW:w1:odd; the hypothesis of (i)", Q="n in Z",
        C="int_{-pi}^{pi} g e^{-inx} = -2i int_0^pi f sin(nx) = 0 for all n", S="none",
        deps=[("stepW:w1:odd", "L603", "the odd extension g"),
              ("bpW:w0:basis#sineMode", "L605", "sin(nx) = sqrt(pi/2) phi_n(x)")]),
    "stepW:w1:basis": dict(
        H="Step stepW:w1:coeffs", Q="none", C="the Fourier coefficients of g for the normalized Haar measure vanish, so "
        "g = 0 in L^2 and f = 0 a.e. on (0,pi)", S="none",
        deps=[("stepW:w1:coeffs", "L607", "the vanishing integrals"),
              ("bpW:w1:ext-fourier", "L608", "the characters form a Hilbert basis (injective coefficient map)")]),
    "stepW:w1:cont": dict(
        H="f continuous; (i)", Q="x_0 in [0,pi]", C="f(x_0) != 0 would give ¦f¦ > ¦f(x_0)¦/2 on a subinterval of positive "
        "length, contradicting (i); so f = 0 on [0,pi]", S="none",
        deps=[("stepW:w1:basis", "L612", "(i): f = 0 a.e.")]),
    "bpW:w1:sine-feature": dict(
        H="a > 0, p in R, k in N; beta : N_+ -> R with ¦beta_j¦ <= B j^nu for some B, nu >= 0; Psi(x)_j = beta_j "
          "phi_j^(k)(x)/omega_{a,p}(j), phi_j^(k)(x) = sqrt(2/pi) j^k sin^(k)(jx), for x in C with ¦Im x¦ < a",
        Q="for all a > 0, p, k, beta, B, nu; (i) for 0 < a' < a; (iii) for real x, y in l^2_R",
        C="(i) with b_j = sqrt(2/pi) B j^{nu+k-p} e^{-(a-a')j}, ¦Psi(x)_j¦ <= b_j for ¦Im x¦ <= a' and sum b_j < infinity; "
          "(ii) Psi is holomorphic on {¦Im x¦ < a}, hence C-analytic there, real for real x, and Psi_R = re o Psi¦_R : "
          "R -> l^2_R is real analytic; (iii) <Psi_R(x),y> = sum_j beta_j (kappa_{a,p} y)_j phi_j^(k)(x), absolutely "
          "convergent", S="none",
        deps=[("bpW:w0:basis#sineMode", "L620", "the modes phi_j and their derivatives"),
              ("bpW:w1:transport", "L620", "the weights omega_{a,p} and kappa_{a,p}"),
              ("stepW:w1:growth", "L632", "proof step"), ("stepW:w1:normal", "L636", "proof step"),
              ("stepW:w1:sinereal", "L641", "proof step")]),
    "stepW:w1:growth": dict(
        H="¦Im x¦ <= a' < a", Q="j", C="¦sin^(k)(jx)¦ <= e^{j¦Im x¦}, so ¦Psi(x)_j¦ <= b_j, and sum b_j < infinity since "
        "a - a' > 0", S="none", deps=[]),
    "stepW:w1:normal": dict(
        H="Step stepW:w1:growth", Q="N", C="the partial sums Psi^N are holomorphic and converge to Psi uniformly on "
        "¦Im x¦ <= a', hence locally uniformly on the strip; Psi is holomorphic and analytic", S="none",
        deps=[("stepW:w1:growth", "L638", "the tail bound sum_{j>N} b_j"),
              ("bpW:w1:ext-onevar", "L640", "locally uniform limits of holomorphic maps are holomorphic; holomorphic "
               "on open subsets of C implies analytic")]),
    "stepW:w1:sinereal": dict(
        H="Step stepW:w1:normal", Q="real x, y", C="Psi(x) = iota Psi_R(x) for real x and Psi_R = re o Psi o (R -> C) is "
        "real analytic; (iii) by lp.inner_eq_tsum and y_j/omega(j) = (kappa y)_j", S="none",
        deps=[("bpW:w1:complexification-lemma", "L643", "(ii): R-analyticity of re o f o l"),
              ("bpW:w1:ext-lp", "L643", "the inner product of l^2 as a tsum"),
              ("bpW:w1:transport", "L644", "kappa_{a,p}")]),
    "bpW:w1:recon-analytic": dict(
        H="k in N; Psi^{U,k}_R, Psi^{V,k}_R the real feature maps of Lemma bpW:w1:sine-feature with a = p = 1 and "
          "beta_j = lambda_j^{-1/2}, resp. lambda_j^{1/2}; U^(k)_y(x) = <Psi^{U,k}_R(x),y> = sum coeff y j/sqrt(lambda_j) "
          "phi_j^(k)(x), V^(k)_y(x) = sum sqrt(lambda_j) coeff y j phi_j^(k)(x) for y in l^2_R, x in R; (iii) S a real "
          "normed space and Y : S -> l^2_R real analytic at s_0",
        Q="for all k, y, real x; (iii) for all S, Y, s_0, x_0",
        C="the series converge absolutely; (i) U^(0)_y(x) = reconU m hm y x and V^(0)_y(x) = reconV m hm y x; (ii) "
          "x -> U^(k)_y(x) has derivative U^(k+1)_y(x) (HasDerivAt), likewise V; U^(k)_y is the k-th derivative of "
          "reconU m hm y (iteratedDeriv k), and derivWithin (reconU m hm y) (Icc 0 pi) x = U^(1)_y(x) for x in [0,pi]; "
          "(iii) (s,x) -> U^(k)_{Y(s)}(x) and V^(k)_{Y(s)}(x) are real analytic on S x R at (s_0,x_0); in particular "
          "for S = R^n the iterated x-derivatives of reconU m hm (Y s) and reconV m hm (Y s) are real analytic", S="none",
        deps=[("bpW:w1:sine-feature", "L650", "the feature maps"),
              ("bpW:w0:basis#lam", "L650", "beta_j = lambda_j^{+-1/2}"),
              ("bpW:w0:ellap#coeff", "L652", "coeff y j in the series"),
              ("bpW:w0:reconstruction#reconU", "L656", "the frozen reconU in (i), (ii)"),
              ("bpW:w0:reconstruction#reconV", "L656", "the frozen reconV in (i)"),
              ("stepW:w1:bil", "L673", "proof step"), ("stepW:w1:recanalytic", "L677", "proof step"),
              ("stepW:w1:recder", "L683", "proof step")]),
    "stepW:w1:bil": dict(
        H="a = p = 1", Q="y, x", C="¦beta_j¦ <= (1+m)^{1/4} j^{1/2}, so Lemma bpW:w1:sine-feature applies; (iii) gives the "
        "series forms and absolute convergence; for k = 0 the series is the frozen tsum termwise, which is (i)",
        S="none",
        deps=[("bpW:w1:sine-feature", "L674", "(iii) and its hypothesis ¦beta_j¦ <= B j^nu"),
              ("bpW:w0:basis#lambda-facts", "L674", "lambda_j^{+-1/2} <= (1+m)^{1/4} j^{1/2}"),
              ("bpW:w0:ellap#coeff", "L675", "coeff y j = (kappa_{1,1} y)_j"),
              ("bpW:w0:reconstruction#reconU", "L676", "the frozen tsum of reconU"),
              ("bpW:w0:reconstruction#reconV", "L676", "the frozen tsum of reconV")]),
    "stepW:w1:recanalytic": dict(
        H="Y analytic at s_0; Psi^{U,k}_R analytic", Q="(s_0,x_0)", C="the composite of the continuous bilinear inner "
        "product with the analytic pair (Psi^{U,k}_R(x), Y(s)) is analytic at (s_0,x_0); this is (iii)", S="none",
        deps=[("bpW:w1:sine-feature", "L680", "(ii): Psi_R is analytic"),
              ("bpW:w1:ext-analytic", "L679", "bilinear maps, pairs and compositions of analytic maps are analytic")]),
    "stepW:w1:recder": dict(
        H="Psi^{U,k}_R analytic", Q="k, y, x", C="(Psi^{U,k}_R)' = Psi^{U,k+1}_R coordinatewise, so d/dx U^(k)_y = "
        "U^(k+1)_y; iterating from (i) gives the iterated derivatives of reconU m hm y; at x in [0,pi] the derivative "
        "within [0,pi] equals the two-sided derivative (uniqueDiffOn_Icc); the same for V; this is (ii)", S="none",
        deps=[("bpW:w1:sine-feature", "L684", "(ii): Psi_R analytic, hence differentiable"),
              ("bpW:w1:ext-analytic", "L684", "analytic maps are differentiable"),
              ("bpW:w1:space", "L686", "(ii): coordinate evaluation is continuous linear"),
              ("stepW:w1:bil", "L689", "(i): U^(0)_y = reconU m hm y")]),
    "bpW:w1:complexification": dict(
        H="typing data: l^2_R, l^2_C and products", Q="none",
        C="defines iota : l^2_R -> l^2_C, re : l^2_C -> l^2_R, conjugation, componentwise on products (E^C_{a,p} "
          "represented by (l^2_C)^2), and: f is real on reals if f(iota y) in iota(l^2_R) whenever defined", S="none",
        deps=[]),
    "bpW:w1:complexification-lemma": dict(
        H="(ii) F_1, F_2 complex Banach, V real normed, l : V -> F_1 and pi : F_2 -> W continuous R-linear, f C-analytic "
          "at l(x); (iii) f defined near iota y, C-analytic at iota y and real on reals near iota y",
        Q="for all such data",
        C="(i) iota, re are continuous R-linear, ||iota y|| = ||y||, ||re z|| <= ||z||, re o iota = id, ||iota y + i iota "
          "y'||^2 = ||y||^2 + ||y'||^2, conjugation is a conjugate-linear isometry, and all commute with tau, kappa and "
          "real multipliers; (ii) pi o f o l is R-analytic at x; (iii) g = re o f o iota is R-analytic at y, iota o g = "
          "f o iota near y, and Dg(y)h = re Df(iota y) iota h", S="none",
        deps=[("bpW:w1:complexification", "L709", "iota, re, conjugation"),
              ("bpW:w1:transport", "L711", "commutation with tau, kappa"),
              ("bpW:w1:ext-analytic", "L722", "C-analytic is R-analytic; composition with continuous linear maps")]),
    "bpW:w1:holomorphic": dict(
        H="typing data: F_1, F_2 complex Banach spaces, U subset F_1 open", Q="f : U -> F_2",
        C="defines: f is holomorphic iff complex Frechet differentiable at every point of U (DifferentiableOn C f U); "
          "bounds are hypotheses ||f(z)|| <= M for z in U, never an unguarded supremum", S="none", deps=[]),
    "bpW:w1:cauchy": dict(
        H="r > 0, M >= 0, f holomorphic on B(v,r) subset F_1 with ||f(z)|| <= M there; for the consequences delta > 0, f "
          "holomorphic on open V with ||f|| <= M, B(w,delta) subset V, C convex with C + B(0,delta) subset V",
        Q="for all such data",
        C="||Df(v)|| <= M/r; ||Df(w)|| <= M/delta; f is (M/delta)-Lipschitz on C", S="none",
        deps=[("bpW:w1:holomorphic", "L738", "holomorphic maps on Banach domains"),
              ("stepW:w1:lines", "L745", "proof step"), ("stepW:w1:onevar", "L748", "proof step"),
              ("stepW:w1:margins", "L750", "proof step")]),
    "stepW:w1:lines": dict(
        H="u in F_1, ||u|| = 1, 0 < r' < r", Q="u, r'", C="phi(zeta) = f(v + zeta u) is holomorphic on ¦zeta¦ < r', "
        "continuous on ¦zeta¦ <= r', phi'(0) = Df(v)u, ||phi|| <= M", S="none", deps=[]),
    "stepW:w1:onevar": dict(
        H="Step stepW:w1:lines", Q="u", C="||Df(v)u|| <= M/r'; letting r' -> r and taking sup over u, ||Df(v)|| <= M/r",
        S="none", deps=[("stepW:w1:lines", "L749", "the one-variable function phi"),
                        ("bpW:w1:ext-onevar", "L749", "the Cauchy estimate in one variable")]),
    "stepW:w1:margins": dict(
        H="the consequences' hypotheses", Q="w, C", C="apply on B(w,delta) for ||Df(w)|| <= M/delta; the Lipschitz bound "
        "on C by the mean value inequality", S="none",
        deps=[("stepW:w1:onevar", "L751", "the estimate on balls"),
              ("bpW:w1:ext-unifderiv", "L751", "the mean value inequality on convex sets")]),
    "bpW:w1:deriv-continuous": dict(
        H="U subset F_1 open, f : U -> F_2 holomorphic; w_0 in U, rho > 0, B >= 0 with B(w_0,2rho) subset U and ||f|| <= B "
          "on B(w_0,2rho)", Q="for all such data; w, w' in B(w_0,rho/2)",
        C="||Df(w) - Df(w')|| <= 2 B rho^{-2} ||w - w'||; such rho, B exist for every w_0, so Df : U -> L(F_1,F_2) is "
          "continuous (ContinuousOn (fderiv C f) U)", S="none",
        deps=[("bpW:w1:holomorphic", "L756", "holomorphic maps"),
              ("stepW:w1:dcbound", "L763", "proof step"), ("stepW:w1:dcintegral", "L765", "proof step"),
              ("stepW:w1:dclip", "L769", "proof step")]),
    "stepW:w1:dcbound": dict(
        H="f continuous at w_0", Q="w_0", C="||f(z)|| <= ||f(w_0)|| + 1 =: B on some ball B(w_0,2rho) subset U", S="none",
        deps=[]),
    "stepW:w1:dcintegral": dict(
        H="w in B(w_0,rho/2), ||u|| = 1", Q="w, u", C="phi(zeta) = f(w + zeta u) is holomorphic for ¦zeta¦ < 3rho/2 and "
        "Df(w)u = (1/(2 pi i)) oint_{¦zeta¦=rho/2} f(w + zeta u) zeta^{-2} dzeta", S="none",
        deps=[("bpW:w1:ext-onevar", "L767", "the Cauchy integral formula for phi'(0)")]),
    "stepW:w1:dclip": dict(
        H="Steps stepW:w1:dcbound, stepW:w1:dcintegral", Q="w, w', u", C="||Df|| <= B/rho on B(w_0,rho), so the "
        "integrands differ by at most (B/rho)||w - w'||; subtracting the Cauchy integrals gives ||(Df(w) - Df(w'))u|| "
        "<= 2 B rho^{-2} ||w - w'||; sup over u", S="none",
        deps=[("bpW:w1:cauchy", "L771", "margin rho inside B(w_0,2rho)"),
              ("stepW:w1:dcintegral", "L772", "the two Cauchy integrals"),
              ("stepW:w1:dcbound", "L771", "the bound B on B(w_0,2rho)")]),
    "bpW:w1:uniform-limit": dict(
        H="U subset F_1 open, f_k : U -> F_2 holomorphic, f_k -> f uniformly on U; (ii) moreover M >= 0 with ||f(z)|| <= M "
          "on U", Q="for all such data; (i) balls B(w,delta), delta > 0, B(w,2delta) subset U; (ii) delta > 0 with "
          "B(w,delta) subset U",
        C="(i) f is holomorphic on U and Df_k -> Df uniformly on every such B(w,delta); if every f_k is real on reals, so is "
          "f; no boundedness of f assumed; (ii) ||Df(w)|| <= M/delta", S="none",
        deps=[("bpW:w1:holomorphic", "L779", "holomorphic maps"),
              ("bpW:w1:complexification", "L782", "real on reals"),
              ("stepW:w1:ulcauchy", "L789", "proof step"), ("stepW:w1:ullimit", "L794", "proof step")]),
    "stepW:w1:ulcauchy": dict(
        H="f_k -> f uniformly; eps > 0", Q="w' in B(w,delta)", C="(Df_k) is uniformly Cauchy on B(w,delta) in the "
        "complete space of bounded C-linear maps, with a uniform limit g", S="none",
        deps=[("bpW:w1:cauchy", "L791", "applied to f_k - f_l with bound eps")]),
    "stepW:w1:ullimit": dict(
        H="Step stepW:w1:ulcauchy", Q="w", C="f is C-differentiable on the ball with Df = g, hence holomorphic on U; real on "
        "reals since iota(l^2_R) is closed; (ii) is the Cauchy estimate for f", S="none",
        deps=[("stepW:w1:ulcauchy", "L795", "the uniform limit g of Df_k"),
              ("bpW:w1:ext-unifderiv", "L795", "uniform limits of derivatives"),
              ("bpW:w1:cauchy", "L797", "(ii) applied to f itself")]),
    "bpW:w1:holo-analytic-fd": dict(
        H="U subset C^n open (max norm), F complex Banach, f : U -> F holomorphic; for the quantitative part n >= 1, "
          "r > 0 with bar P(z_0,r) subset U; for the real part F = E^C_{a,p} and f real on reals at the real points of U",
        Q="for all such data",
        C="f is C-analytic on U (AnalyticOnNhd C f U; n = 0 trivial); there are r_1 > r and M_1 >= 0 with bar P(z_0,r_1) "
          "subset U, ||f|| <= M_1 there, and f = sum_alpha c_alpha (z - z_0)^alpha absolutely on P(z_0,r_1) with "
          "||c_alpha|| <= M_1 r_1^{-¦alpha¦}; grouped by degree a FormalMultilinearSeries (p_m) with ||p_m|| <= "
          "binom(m+n-1,n-1) M_1 r_1^{-m} and HasFPowerSeriesOnBall f p z_0 r_1; re o f¦_{U cap R^n} is real analytic "
          "into E_{a,p}", S="r_1, M_1 depend on f, z_0, r",
        deps=[("bpW:w1:holomorphic", "L802", "holomorphic maps"),
              ("bpW:w1:complexification", "L809", "real on reals"),
              ("stepW:w1:hamargin", "L814", "proof step"), ("stepW:w1:hacoef", "L817", "proof step"),
              ("stepW:w1:hagroup", "L824", "proof step"), ("stepW:w1:hareal", "L834", "proof step")]),
    "stepW:w1:hamargin": dict(
        H="bar P(z_0,r) subset U compact, U open", Q="none", C="bar P(z_0,r_1) subset U for some r_1 > r, and f is "
        "bounded by some M_1 on the compact bar P(z_0,r_1)", S="none", deps=[]),
    "stepW:w1:hacoef": dict(
        H="Step stepW:w1:hamargin; F complete", Q="alpha in N^n",
        C="there are c_alpha in F with ||c_alpha|| <= M_1 r_1^{-¦alpha¦} and f(z) = sum_alpha c_alpha (z - z_0)^alpha "
          "absolutely on P(z_0,r_1)", S="none",
        note="Uses the proof of track K's Lemma bp:p1:holomorphic-analytic (steps han-cauchy to han-bounds) with radius "
             "r_1 and K's target W replaced by the complete space F (a carrier change); the text justifies the transfer "
             "(L821-L823: only the one-variable Cauchy formula for complete F and Bochner integration on the domain "
             "torus are used). Reviewer: check that the import and the two externals cover the transfer.",
        deps=[("stepW:w1:hamargin", "L819", "the radius r_1 and the bound M_1"),
              ("K:bp:p1:holomorphic-analytic", "L818", "K's Cauchy-coefficient argument (steps han-cauchy..han-bounds), "
               "applied with W replaced by the complete F"),
              ("bpW:w1:ext-onevar", "L821", "the one-variable Cauchy formula for complete F"),
              ("bpW:w1:ext-integral", "L823", "Fubini and termwise integration of Bochner integrals on the torus")]),
    "stepW:w1:hagroup": dict(
        H="Step stepW:w1:hacoef", Q="m >= 0", C="p_m(h_1..h_m) = sum_{¦alpha¦=m} (prod (h_l)_{iota_alpha(l)}) c_alpha is a "
        "continuous m-linear map with ||p_m|| <= binom(m+n-1,n-1) M_1 r_1^{-m}; sum ||p_m|| rho^m < infinity for rho < "
        "r_1; regrouping gives HasFPowerSeriesOnBall f p z_0 r_1; f is analytic at every point of U", S="none",
        deps=[("stepW:w1:hacoef", "L829", "the coefficients c_alpha and their bounds"),
              ("bpW:w3:ext-tsum", "L831", "regrouping an absolutely convergent multi-index series by degree",
               F),
              ("bpW:w1:ext-analytic", "L832", "a power series with positive radius gives analyticity (HasFPowerSeriesOnBall)")]),
    "stepW:w1:hareal": dict(
        H="F = E^C_{a,p}, f real on reals", Q="real points", C="re o f¦_{U cap R^n} is real analytic", S="none",
        deps=[("bpW:w1:complexification-lemma", "L835", "(iii)")]),
    "bpW:w1:torus-analytic": dict(
        H="s > 0, T_s = {theta in C^2 : max_i ¦Im theta_i¦ < s}; tilde K : T_s -> E^C_{1,1} holomorphic, real on reals, "
          "1-periodic", Q="for all such s, tilde K",
        C="K = re o tilde K¦_{R^2} : R^2 -> WaveSpace satisfies AnalyticOnNhd R K univ, is Z^2-periodic, and fderiv R K "
          "theta h = re D tilde K(theta) h for h in R^2", S="none",
        deps=[("bpW:w1:holo-analytic-fd", "L847", "with U = T_s"),
              ("bpW:w1:complexification-lemma", "L847", "(iii): real restriction and its derivative"),
              ("bpW:w0:ellap#WaveSpace", "L841", "K takes values in WaveSpace (E_{1,1})")]),
    "bpW:w1:flow": dict(
        H="F complex Banach, V subset F open, X : V -> F holomorphic with ||X(z)|| <= M on V; U subset V open with "
          "B(w,2delta) subset V for all w in U; 0 < M < delta; L = M/delta < 1; (iii) F = E^C and X real on reals; (iv) "
          "X(.,xi), xi in Pi, each satisfying the hypotheses with the same V, U, M, delta, and N >= 0 with "
          "||X(z,xi) - X(z,zeta)|| <= N on V",
        Q="for all such data; w in U, t in [-1,1]",
        C="(i) a unique C^1 curve t -> phi^t(w), t in [-1,1], phi^0(w) = w, d/dt phi^t = X(phi^t), values in V, with "
          "||phi^t(w) - w|| <= ¦t¦M <= M; (ii) w -> phi^t(w) is holomorphic on U with ||D phi^t(w)|| <= e^{L¦t¦}; (iii) "
          "phi^t is real on reals; (iv) ||phi^t(w,xi) - phi^t(w,zeta)|| <= ¦t¦ e^{L¦t¦} N", S="none",
        deps=[("bpW:w1:holomorphic", "L853", "holomorphic fields"),
              ("bpW:w1:complexification", "L861", "real on reals"),
              ("stepW:w1:flowlip", "L869", "proof step"), ("stepW:w1:picard", "L872", "proof step"),
              ("stepW:w1:picardholo", "L876", "proof step"), ("stepW:w1:flowlim", "L889", "proof step"),
              ("stepW:w1:flowreal", "L895", "proof step"), ("stepW:w1:flowpar", "L897", "proof step")]),
    "stepW:w1:flowlip": dict(
        H="w in U, w' in B(w,delta)", Q="w, w'", C="||DX(w')|| <= L and X is L-Lipschitz on the convex ball B(w,delta)",
        S="none", deps=[("bpW:w1:cauchy", "L871", "margin delta inside B(w,2delta) subset V")]),
    "stepW:w1:picard": dict(
        H="Step stepW:w1:flowlip", Q="k, w, t", C="the Picard iterates phi_k stay in B(w,delta) (||phi_k - w|| <= ¦t¦M < "
        "delta), are continuous in (w,t), and ||phi_{k+1} - phi_k|| <= M L^k ¦t¦^{k+1}/(k+1)! uniformly in w", S="none",
        deps=[("stepW:w1:flowlip", "L875", "L-Lipschitz on B(w,delta)"),
              ("bpW:w1:ext-integral", "L873", "the integral equation (Bochner integral)")]),
    "stepW:w1:picardholo": dict(
        H="Steps stepW:w1:flowlip, stepW:w1:picard", Q="k", C="by induction w -> phi_k(w,t) is holomorphic on U, "
        "||D_w phi_k|| <= sum_{i<=k} (L¦t¦)^i/i! <= e^{L¦t¦}, t -> D_w phi_k continuous; differentiation under the "
        "integral with domination L e^L", S="none",
        deps=[("bpW:w1:deriv-continuous", "L881", "DX is continuous on V"),
              ("bpW:w1:ext-integral", "L883", "differentiation under the integral (hasFDerivAt_integral_of_dominated_of_fderiv_le)"),
              ("stepW:w1:flowlip", "L884", "||DX|| <= L on B(w,delta)"),
              ("stepW:w1:picard", "L879", "the iterates and their continuity")]),
    "stepW:w1:flowlim": dict(
        H="Steps stepW:w1:picard, stepW:w1:picardholo", Q="w, t", C="the iterates converge uniformly to phi, a C^1 "
        "solution of the integral equation; uniqueness among solutions in V; phi^t holomorphic with the derivative "
        "bound; this proves (i), (ii)", S="none",
        deps=[("stepW:w1:picard", "L890", "geometric convergence of the iterates"),
              ("bpW:w1:ext-ode", "L891", "uniqueness of ODE solutions for Lipschitz fields"),
              ("bpW:w1:uniform-limit", "L893", "holomorphy of the uniform limit"),
              ("stepW:w1:picardholo", "L893", "holomorphy and bounds of the iterates")]),
    "stepW:w1:flowreal": dict(
        H="X real on reals", Q="none", C="every Picard iterate of a real point is real and the real subspace is closed, so "
        "phi^t is real on reals", S="none",
        deps=[("stepW:w1:picard", "L896", "the Picard iterates"), ("stepW:w1:flowlim", "L896", "phi is their limit")]),
    "stepW:w1:flowpar": dict(
        H="(iv)", Q="w, t", C="psi^t = phi^t(w,xi) - phi^t(w,zeta) satisfies ||dpsi/dt|| <= N + L||psi||, psi^0 = 0, so "
        "||psi^t|| <= N(e^{L¦t¦} - 1)/L <= ¦t¦ e^{L¦t¦} N (both curves stay in the convex ball B(w,delta))", S="none",
        deps=[("stepW:w1:flowlip", "L899", "X(.,zeta) is L-Lipschitz on B(w,delta)"),
              ("stepW:w1:flowlim", "L898", "both trajectories lie in B(w,delta) by (i)"),
              ("bpW:w1:ext-ode", "L900", "Gronwall's inequality")]),
    "bpW:w1:kam-space": dict(
        H="typing data: a >= 0, p in R, bar p; s, r > 0", Q="none",
        C="defines P^{a,p}_C = C^2 x C^2 x l^{a,p}_C x l^{a,p}_C (points (theta,y,u,v), weighted coordinates, max norm on "
          "C^2), D(s,r) = {max ¦Im theta_i¦ < s, ¦y¦ < r^2, ||u||_{a,p} + ||v||_{a,p} < r}, ¦W¦_{bar p,r} = ¦Theta¦ + "
          "¦Y¦/r^2 + ||U||_{a,bar p}/r + ||V||_{a,bar p}/r, the operator norm ¦L¦_{r,s}, and period one: x = 2 pi theta "
          "is P96-K's angle, a strip ¦Im x¦ < s_K is ¦Im theta¦ < s_K/(2pi), theta-components are (2pi)^{-1} times "
          "x-components", S="none",
        deps=[("bpW:w1:transport", "L918", "weighted coordinates of l^{a,p}_C")]),
    "bpW:w1:kam-domain": dict(
        H="0 < sigma <= 1, 0 < 2sigma < s, r > 0", Q="for all such sigma, s, r; W_0, W",
        C="D(s,r) is open and convex; D(s',r') subset D(s,r) for s' <= s, r' <= r; every W_0 in D(s-2sigma,r/2) has "
          "W_0 + W in D(s-sigma,r) whenever ¦W¦_{p,r} < sigma/2; ¦W¦_{bar p,r} <= ¦W¦_{p,r} for bar p <= p and "
          "¦W¦_{p,r} <= ¦W¦_{p,r'} for r' <= r", S="none",
        deps=[("bpW:w1:kam-space", "L940", "D(s,r) and the norms"),
              ("bpW:w1:embed", "L950", "(i): norm comparison for bar p <= p")]),
    "bpW:w1:fourier-l2": dict(
        H="H complex Hilbert space, n >= 1, s > 0, T_s = {max ¦Im theta_i¦ < s}, u : T_s -> H holomorphic, 1-periodic, "
          "||u|| <= M on T_s (M >= 0); hat u_k = int_{[0,1]^n} u(x) e^{-2 pi i k.x} dx; (ii) c_k in H with sum ||c_k|| "
          "e^{2pi¦k¦_1 s} < infinity", Q="for all such data",
        C="(i) sum_k ||hat u_k||^2 e^{4 pi ¦k¦_1 s} <= 2^n M^2; (ii) v(theta) = sum c_k e^{2 pi i k.theta} converges "
          "absolutely and uniformly on T_s, is holomorphic and 1-periodic, hat v_k = c_k, ||v|| <= sum ||c_k|| "
          "e^{2pi¦k¦_1 s}; (iii) u is the sum of its Fourier series on T_{s'} for s' < s", S="none",
        deps=[("bpW:w1:holomorphic", "L957", "holomorphic maps"),
              ("stepW:w1:shift", "L969", "proof step"), ("stepW:w1:parseval", "L975", "proof step"),
              ("stepW:w1:orthants", "L980", "proof step"), ("stepW:w1:fsum", "L984", "proof step")]),
    "stepW:w1:shift": dict(
        H="eta in R^n, max ¦eta_i¦ < s", Q="k", C="hat u_k e^{-2 pi k.eta} is the k-th Fourier coefficient of the "
        "continuous periodic x -> u(x + i eta)", S="none",
        note="The text cites \"the contour shift of track K's bp:p1:fourier-basic\" (L973); fourier-basic contains no "
             "contour shift. The shift is K's step:p1:dec-shift (in the proof of bp:p1:decay), used here with an "
             "arbitrary shift eta instead of K's t_j = -rho' sgn(k_j). Suspected blueprint misreference (reported).",
        deps=[("K:step:p1:dec-shift", "L973", "the contour shift (cited as fourier-basic) applied to the scalar "
               "holomorphic functions <e,u>"),
              ("bpW:w1:ext-lp", "L974", "vectors of H are determined by the functionals <e,.>")]),
    "stepW:w1:parseval": dict(
        H="g continuous periodic H-valued with ||g|| <= M", Q="eta", C="sum_k ||hat g_k||^2 = int ||g||^2 <= M^2; hence "
        "sum_k ||hat u_k||^2 e^{-4 pi k.eta} <= M^2", S="none",
        deps=[("bpW:w1:ext-fourier", "L978", "scalar Parseval"),
              ("bpW:w1:ext-series", "L978", "Tonelli over the orthonormal basis"),
              ("stepW:w1:shift", "L979", "the shifted coefficients")]),
    "stepW:w1:orthants": dict(
        H="Step stepW:w1:parseval; s' < s", Q="eps in {+-1}^n", C="e^{4 pi s' ¦k¦_1} <= sum_eps e^{4 pi s' eps.k}; summing "
        "the 2^n shifts eta = -s' eps gives (i) with s', and monotone convergence gives s", S="none",
        deps=[("stepW:w1:parseval", "L981", "the bound for each eta")]),
    "stepW:w1:fsum": dict(
        H="(ii): sum ||c_k|| e^{2 pi ¦k¦_1 s} < infinity; (iii): u as in (i), s' < s", Q="none",
        C="(ii) uniform convergence of holomorphic partial sums, holomorphy of the limit, coefficients termwise; (iii) "
          "sum ||hat u_k|| e^{2pi¦k¦_1 s'} <= 2^{n/2} M (sum e^{-4pi¦k¦_1(s-s')})^{1/2} < infinity, and the sum v of (ii) "
          "equals u on R^n (scalar uniqueness) and on T_{s'} (identity theorem)", S="none",
        deps=[("bpW:w1:uniform-limit", "L986", "holomorphy of the uniform limit"),
              ("bpW:w1:ext-integral", "L986", "term-by-term integration of the coefficients"),
              ("stepW:w1:orthants", "L987", "(i) in the Cauchy-Schwarz bound"),
              ("K:bp:p1:fourier-basic", "L989", "(b): a continuous periodic function with vanishing coefficients is 0"),
              ("K:bp:p1:strip-identity", "L989", "identity theorem on strips")]),
    "bpW:w1:fourier-banach": dict(
        H="F complex Banach, n >= 1, s > 0, M >= 0, u : T_s -> F holomorphic, 1-periodic, ||u|| <= M on T_s; hat u_k "
          "(Bochner integral); (ii) 0 < sigma < s, c >= 0; (iii) c_k in F with sum ||c_k|| e^{2pi¦k¦_1 rho} < infinity "
          "for some rho > 0", Q="for all such data; k in Z^n",
        C="(i) ||hat u_k|| <= M e^{-2 pi ¦k¦_1 s}; (ii) sum_k ||hat u_k|| e^{2pi¦k¦_1(s-sigma)} <= M coth(pi sigma)^n and "
          "sum_k (1+¦k¦_1)^c ||hat u_k|| e^{2pi¦k¦_1(s-sigma)} <= M S_{n,c}(sigma); (iii) v = sum c_k e^{2pi i k.theta} "
          "converges absolutely and uniformly on T_rho, is holomorphic and 1-periodic, hat v_k = c_k, ||v|| <= sum "
          "||c_k|| e^{2pi¦k¦_1 rho}; (iv) everything is linear in u (parameter-difference versions)", S="none",
        deps=[("bpW:w1:holomorphic", "L999", "holomorphic maps"),
              ("bpW:w1:lattice", "L1005", "S_{n,c}"),
              ("stepW:w1:fbdual", "L1015", "proof step"), ("stepW:w1:fbdecay", "L1019", "proof step"),
              ("stepW:w1:fbsum", "L1023", "proof step"), ("stepW:w1:fbconv", "L1025", "proof step")]),
    "stepW:w1:fbdual": dict(
        H="phi in F*, ||phi|| <= 1", Q="phi", C="phi o u is holomorphic, 1-periodic, bounded by M, and phi(hat u_k) = "
        "(phi o u)^_k", S="none",
        deps=[("bpW:w1:ext-onevar", "L1018", "continuous linear maps commute with Bochner integrals")]),
    "stepW:w1:fbdecay": dict(
        H="Step stepW:w1:fbdual", Q="k", C="¦(phi o u)^_k¦ <= e^{-2pi¦k¦_1 s'} M for 0 <= s' < s; s' -> s; for all "
        "norm-one phi, ||hat u_k|| <= M e^{-2pi¦k¦_1 s}; this is (i)", S="none",
        deps=[("stepW:w1:fbdual", "L1020", "the scalar functions phi o u"),
              ("K:bp:p1:decay", "L1020", "scalar coefficient decay"),
              ("bpW:w1:ext-onevar", "L1022", "the norm is attained by norm-one functionals")]),
    "stepW:w1:fbsum": dict(
        H="(i)", Q="sigma", C="||hat u_k|| e^{2pi¦k¦_1(s-sigma)} <= M e^{-2pi¦k¦_1 sigma}, summed with Lemma bpW:w1:lattice; "
        "this is (ii)", S="none",
        deps=[("stepW:w1:fbdecay", "L1024", "(i)"), ("bpW:w1:lattice", "L1024", "(i), (iii): the lattice sums")]),
    "stepW:w1:fbconv": dict(
        H="(iii)", Q="none", C="the partial sums converge uniformly on T_rho; the limit is holomorphic; coefficients by "
        "term-by-term integration; (iv) by linearity", S="none",
        deps=[("bpW:w1:uniform-limit", "L1027", "(i): holomorphy of the uniform limit"),
              ("bpW:w1:ext-integral", "L1028", "term-by-term integration")]),
    "bpW:w1:lattice": dict(
        H="n >= 1, sigma > 0, eps = 2 pi sigma, ¦k¦_1 = sum ¦k_i¦; (iii) c >= 0, b = c + n - 1; (iv) tau >= 1, gamma, "
          "beta >= 0", Q="for all such data",
        C="(i) sum_k e^{-eps¦k¦_1} = coth(eps/2)^n = coth(pi sigma)^n; (ii) #{k : ¦k¦_1 = m} <= 2^n binom(m+n-1,n-1) <= "
          "2^n (m+1)^{n-1}; (iii) sum_k (1+¦k¦_1)^c e^{-eps¦k¦_1} <= S_{n,c}(sigma) := 2^n (2b/(e eps))^b e^{eps/2} "
          "(1 + 2/eps) ((2b/(e eps))^b := 1 for b = 0); (iv) A_k = 1 + ¦k¦_1^tau <= (1+¦k¦_1)^tau, so sum A_k^gamma "
          "(1+¦k¦_1)^beta e^{-eps¦k¦_1} <= S_{n,gamma tau + beta}(sigma), and P96-K's B_sigma^2 <= 2^n S_{n,4tau+2}(sigma/pi) "
          "in period-one units", S="S_{n,c}(sigma) explicit in n, c, sigma",
        deps=[("stepW:w1:latprod", "L1050", "proof step"), ("stepW:w1:latcount", "L1054", "proof step"),
              ("stepW:w1:latweight", "L1057", "proof step"), ("stepW:w1:latdiv", "L1062", "proof step")]),
    "stepW:w1:latprod": dict(H="eps > 0", Q="none", C="the sum factorizes and sum_{m in Z} e^{-eps¦m¦} = coth(eps/2)",
        S="none", deps=[("bpW:w1:ext-series", "L1052", "Tonelli for the product sum")]),
    "stepW:w1:latcount": dict(H="m >= 0", Q="m", C="#{k : ¦k¦_1 = m} <= 2^n binom(m+n-1,n-1) <= 2^n (m+1)^{n-1}",
        S="none", deps=[]),
    "stepW:w1:latweight": dict(H="(ii)", Q="none", C="the sum in (iii) is at most 2^n sum_m (m+1)^b e^{-eps m} <= "
        "S_{n,c}(sigma), using t^b e^{-eps t/2} <= (2b/(e eps))^b and 1 - e^{-x} >= x/(1+x)", S="none",
        deps=[("stepW:w1:latcount", "L1058", "(ii)")]),
    "stepW:w1:latdiv": dict(H="tau >= 1", Q="x >= 0", C="1 + x^tau <= (1+x)^tau; the B_sigma statement by the "
        "substitution ¦k¦ = ¦k¦_1, e^{-2¦k¦sigma_K} = e^{-2pi¦k¦_1(sigma_K/pi)}", S="none",
        deps=[("stepW:w1:latweight", "L1064", "(iii) with c = gamma tau + beta")]),
    "bpW:w1:schur": dict(
        H="A bounded on l^2_K with matrix A_ij = (A e_j)_i; (iii) F_ij with ¦F_ij¦ <= c¦A_ij¦/¦i-j¦ (i != j), ¦F_ii¦ <= "
          "c¦A_ii¦; (iv) A : l^{a,p}_K -> l^{a,bar p}_K via its representative", Q="for all such A, F, c",
        C="(i) B_ij = ¦A_ij¦/¦i-j¦ (i != j), B_ii = 0 defines a bounded operator with absolutely convergent rows and "
          "||B|| <= (pi/sqrt3)||A||; (ii) the diagonal (A_ii) is a multiplier with norm <= ||A||; (iii) ||F|| <= "
          "c(1 + pi/sqrt3)||A|| <= 3c||A||; (iv) the same for weighted spaces via the representative hat A (ratios "
          "unchanged by the weights)", S="none",
        deps=[("bpW:w1:transport", "L1119", "the representative hat A"),
              ("stepW:w1:rows", "L1124", "proof step"), ("stepW:w1:schurtest", "L1128", "proof step"),
              ("stepW:w1:diagcomb", "L1131", "proof step"), ("stepW:w1:schurweights", "L1136", "proof step")]),
    "stepW:w1:rows": dict(H="A bounded", Q="i, j", C="sum_j ¦A_ij¦^2 <= ||A||^2, sum_i ¦A_ij¦^2 <= ||A||^2; row and "
        "column sums of B at most (pi/sqrt3)||A||", S="none",
        deps=[("bpW:w1:ext-series", "L1126", "sum_{k != 0} k^{-2} = pi^2/3")]),
    "stepW:w1:schurtest": dict(H="Step stepW:w1:rows", Q="v", C="||Bv||^2 <= Lambda^2 ||A||^2 ||v||^2 (Schur test)",
        S="none", deps=[("stepW:w1:rows", "L1129", "row and column sums"),
                        ("bpW:w1:ext-lp", "L1130", "norm bounds via finite partial sums")]),
    "stepW:w1:diagcomb": dict(H="A bounded; (iii)", Q="none", C="¦A_ii¦ <= ||A||; the diagonal is a multiplier; F is "
        "dominated entrywise by cB + c diag(¦A_ii¦), so ||F|| <= c(1 + pi/sqrt3)||A|| < 3c||A||", S="none",
        deps=[("bpW:w1:multiplier", "L1132", "diagonal multipliers"),
              ("stepW:w1:schurtest", "L1133", "the bound on B")]),
    "stepW:w1:schurweights": dict(H="A : l^{a,p} -> l^{a,bar p}", Q="i, j", C="hat A_ij = omega_{a,bar p}(i) A_ij/"
        "omega_{a,p}(j), likewise for F, so the hypotheses of (iii) transfer", S="none",
        deps=[("bpW:w1:transport", "L1137", "the representative")]),
}

DELETE = ["bpW:w1:kam-conventions", "bpW:w1:operator-fourier"]

COV = {
    "bpW:w1:kam-conventions": ("EXCLUDED", "administrative remark (conventions to carry into W4-W6: P96-K's z is the "
                               "conjugate of W0's; sum versus max norm); no wave-1 proof consumes it; re-examine when "
                               "W4-W6 are added"),
    "bpW:w1:operator-fourier": ("EXCLUDED", "administrative remark (counterexample to the operator-valued square-sum "
                                "bound printed on P96-K p. 127 and what W4 must use instead); no wave-1 proof consumes "
                                "it; re-examine when W4 is added"),
    "w1-sequences:sourcegap-L906": ("NODE stepW:w1:flowpar", "P96-K Lemma A.4's mean value step needs a segment in V; "
                                    "the blueprint repairs it by keeping both trajectories in the convex ball "
                                    "B(w,delta) (ball margin 2 delta, M < delta) in the parameter step"),
    "w1-sequences:sourcegap-L1105": ("NODE bpW:w1:fourier-banach, bpW:w1:lattice", "the false operator-valued "
                                     "square-sum bound of P96-K p. 127 is replaced by these lemmas; the homological "
                                     "estimate itself is W4's (later wave)"),
    "w1-sequences:prose-L1143-L1152": ("EXCLUDED", "ledger: PLAN-node mapping (administrative)"),
    "w1-sequences:prose-L1154-L1162": ("EXCLUDED", "ledger: added nodes and their consumers (administrative pointers)"),
    "w1-sequences:prose-L1164-L1168": ("EXCLUDED", "ledger: source gaps and conventions (administrative; each gap is "
                                       "mapped at its \\sourcegap item)"),
}

STEP_CONTEXT = True
SYMBOL_EDGES = True

for _k, _src in {'w1-sequences:sourcegap-L906': 'blueprint-W/parts/w1-sequences.tex#sourcegap@L906-L912', 'w1-sequences:sourcegap-L1105': 'blueprint-W/parts/w1-sequences.tex#sourcegap@L1105-L1108'}.items():
    COV[_k] = (COV[_k][0], COV[_k][1], _src)
