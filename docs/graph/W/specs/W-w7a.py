# Writer spec for slice W-w7a (blueprint-W/parts/w7-measure.tex L1-L459). Wave 2. Rendered by w_depgraph_fill.py.
F = "blueprint-W/parts/w7-measure.tex"
STEP_CONTEXT = True
SYMBOL_EDGES = True
SYMBOL_OVERRIDE = {"bpW:w0:basis#lam": r"\\lambda_(?:[1-9JjiIn]|\{[jJiI])",
                   "bpW:w0:basis#sineMode": r"\\Lean\{sineMode"}   # phi_{kl} here is a zone function, not a sine mode
PS = "proof step"
EXT = dict(H="none (Mathlib-level external fact)", Q="as stated in the item", S="none", deps=[])
SD = "W7 standing data (L33-L41): m > 0, lambda_j = sqrt(j^2+m), corrected A, B, max norms on R^2, Leb, |k| = |k_1| + |k_2|"
FIX = "the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta, frequency pairs, phi_kl"

NODES = {
    "bpW:w7:ext-tonelli": dict(EXT, C="for Borel S subset R^2, Leb(S) = int Leb_1{t : (t,y) in S} dy = int Leb_1{t : (y,t) in S} dy"),
    "bpW:w7:ext-diam": dict(EXT, C="a set S subset R with |t - t'| <= d for all t, t' in S has Leb_1(S) <= d"),
    "bpW:w7:ext-linear": dict(EXT, C="Leb(T(S) + c) = |det T| Leb(S) for invertible linear T of R^2 and c in R^2"),
    "bpW:w7:ext-borel": dict(EXT, C="if D subset R^2 is Borel and f : D -> R continuous on D then {xi in D : |f(xi)| < eta} is "
        "Borel; countable unions, intersections, differences of Borel sets are Borel; Z^2 and the finitely supported l with "
        "|l| <= 2 are countable; measure is countably subadditive and monotone"),
    "bpW:w7:ext-zeta": dict(EXT, C="#{k in Z^2 : |k| = N} = 4N for N >= 1; sum N^{-2} = pi^2/6; hence Z_3 = sum_{k != 0} |k|^{-3} "
        "= 4 zeta(2) = 2 pi^2/3 < 7"),
    "bpW:w7:ext-ball": dict(EXT, C="Metric.ball 0 h in Fin 2 -> R is (-h,h)^2; Leb of a product of intervals is the product "
        "of lengths"),
    "bpW:w7:ext-ennreal": dict(EXT, C="extended-real arithmetic: x/y <= 1, (y - s)/y = 1 - s/y for 0 < x <= y < infinity, s <= "
        "x; squeeze to 1; real powers monotone, x^a x^b = x^{a+b}; ceil(x) <= 2x for x >= 1"),
    "bpW:w7#data": dict(
        new=True, kind="definition", title="W7 standing data", stmt=f"{F}#bpW:w7@L33-L41", proof="-",
        H="none", Q="none",
        C="Standing assumption m > 0 and the conventions of W0: lambda_j = sqrt(j^2+m), I_j = |z_j|^2, period-one angles, "
          "corrected A, B (printed P96-W values not used); max norm |.|_infty on R^2, induced operator norm (maximal row sum); "
          "Leb = volume on Fin 2 -> R; |k| = |k_1| + |k_2| (the norm of KAM.IsDiophantine); diam_infty; tangential modes "
          "J = {1,2} (Fin 2 index i is mode i+1), normal modes j >= 3", S="none",
        note="Unlabelled 'Standing data' paragraph (SPEC hypothesis packages).",
        deps=[("bpW:w0:mass", "L33", "standing assumption m > 0"), ("bpW:w0:basis#lam", "L34", "lambda_j"),
              ("bpW:w0:periodone#linearTorus", "L35", "period-one convention"), ("bpW:w0n:AB", "L35", "the corrected A, B"),
              ("bpW:wh:dioph#IsDiophantine", "L39", "the norm |k| of KAM.IsDiophantine")]),
    "bpW:w7:indexdef": dict(
        H=SD, Q="none",
        C="defines N_3, finitely supported l on N_3 with |l|, <l,x>, e_j, Lambda = {1 <= |l| <= 2}, Lambda^-, Lambda^+, the "
          "Dirichlet weight <l> = max(1,|sum j l_j|) (<l> >= 3 on Lambda^+, <l> = i - j on Lambda^-), |l|_delta, Z, the fixed "
          "exponents tau = 24, varpi = 1/2, beta = 1/4, A_k = 1 + |k|^tau, and the modified weight hat w(l) = (i-j) j^{-1/4} "
          "on Lambda^-, <l> otherwise", S="none",
        deps=[("bpW:w7#data", "L83", "|k| and indices")]),
    "bpW:w7:omega0": dict(
        H=SD + "; lambda_J = (lambda_1,lambda_2), b = (1/lambda_1, 1/lambda_2), A of Theorem bpW:w0n:AB", Q="xi in R^2",
        C="defines omega^0(xi) = lambda_J + A xi and Omega^0_j(xi) = lambda_j + (B xi)_j = lambda_j + (3/(2 pi lambda_j))<b,xi> "
          "(j >= 3)", S="none",
        deps=[("bpW:w0n:AB", "L130", "A and B")]),
    "bpW:w7:freqcoords": dict(
        H=SD, Q="for Borel F subset R^2; xi, xi'",
        C="(i) A^{-1} = (8pi/21)((-3 lambda_1^2, 4 lambda_1 lambda_2),(4 lambda_1 lambda_2, -3 lambda_2^2)), |det A| = D_A = "
          "63/(64 pi^2 lambda_1^2 lambda_2^2), A^{-1} b = (8pi/21) lambda_J; (ii) ||A||_infty = N_A < 3/5, ||A^{-1}||_infty = "
          "L_A = N_A/D_A; (iii) omega^0 is an affine bijection and Omega^0_j = lambda_j + (4/(7 lambda_j)) s(zeta), s(zeta) = "
          "<lambda_J, zeta - lambda_J>; (iv) Leb(omega^0(F)) = D_A Leb(F), diam omega^0(F) <= N_A diam F, |xi - xi'| <= L_A "
          "|omega^0(xi) - omega^0(xi')|", S="D_A, N_A, L_A explicit in m",
        deps=[("bpW:w7:omega0", "L141", "omega^0, Omega^0"),
              ("stepW:w7:inverse", "L152", PS), ("stepW:w7:norms", "L158", PS), ("stepW:w7:Omegazeta", "L163", PS),
              ("stepW:w7:measure-affine", "L166", PS)]),
    "stepW:w7:inverse": dict(H="", Q="none", C="the inverse of A (Sherman-Morrison), A^{-1} b, det A", S="none",
        deps=[("bpW:w0n:AB", "L153", "A = (3/(8pi))(4bb^T - D^2)"), ("bpW:w0n:nondeg", "L157", "(i) det A")]),
    "stepW:w7:norms": dict(H="", Q="none", C="N_A < 3/5 and L_A", S="none",
        deps=[("bpW:w0:basis#lambda-facts", "L160", "lambda_1 > 1, lambda_2 > 2, lambda increasing")]),
    "stepW:w7:Omegazeta": dict(H="", Q="zeta", C="Omega^0_j in zeta", S="none",
        deps=[("stepW:w7:inverse", "L164", "A^{-1} b"), ("bpW:w7:omega0", "L165", "the definition")]),
    "stepW:w7:measure-affine": dict(H="", Q="F", C="(iv)", S="none",
        deps=[("bpW:w7:ext-linear", "L167", "Lebesgue measure under affine maps"), ("stepW:w7:norms", "L167", "operator norms")]),
    "bpW:w7:unpert-bounds": dict(
        H=SD + "; |xi|_infty <= 1/2, zeta = omega^0(xi); beta_* = 1/(2 sqrt(9+m)), a_kappa = m/2 + 1", Q="for such xi; l in Lambda; i > j >= 3",
        C="(i) |s(zeta)| <= 1 and |omega^0(xi)|_infty <= lambda_2 + 3/10; (ii) |<l,Omega^0(xi)>| >= 3 beta_* <l>; (iii) "
          "|Omega^0_i - Omega^0_j - (i-j)| <= a_kappa (i-j) j^{-2}; (iv) zeta -> <l,Omega^0> affine with Lipschitz constant "
          "(4/7)(lambda_1 + lambda_2)|l|_{-1}", S="beta_*, a_kappa depend only on m",
        deps=[("bpW:w7:freqcoords", "L172", "zeta and s"), ("bpW:w7:indexdef", "L176", "Lambda, <l>, |l|_{-1}"),
              ("stepW:w7:ssize", "L183", PS), ("stepW:w7:plus", "L186", PS), ("stepW:w7:minus", "L190", PS),
              ("stepW:w7:kappa", "L195", PS), ("stepW:w7:liplOmega", "L201", PS)]),
    "stepW:w7:ssize": dict(H="", Q="xi", C="|s| <= 1 and |A xi| < 3/10", S="none",
        deps=[("bpW:w7:freqcoords", "L185", "(ii), (iii)")]),
    "stepW:w7:plus": dict(H="", Q="l in Lambda^+", C="|<l,Omega^0>| >= (8/9)<l> >= 3 beta_* <l>", S="none",
        deps=[("stepW:w7:ssize", "L187", "|s| <= 1"), ("bpW:w0:basis#lambda-facts", "L188", "lambda_j >= j")]),
    "stepW:w7:minus": dict(H="", Q="i > j", C="Omega^0_i - Omega^0_j >= 3 beta_*(i-j)", S="none",
        deps=[("stepW:w7:ssize", "L192", "|s| <= 1"), ("bpW:w0:basis#lambda-facts", "L193", "f' increasing")]),
    "stepW:w7:kappa": dict(H="", Q="i > j", C="the kappa = 2 asymptotics", S="none",
        deps=[("bpW:w0:basis#lambda-facts", "L196", "lambda_n - n = m/(lambda_n + n), f' < 1"), ("stepW:w7:ssize", "L199", "|s| <= 1")]),
    "stepW:w7:liplOmega": dict(H="", Q="zeta, zeta'", C="(iv) the Lipschitz bound", S="none", deps=[]),
    "bpW:w7:constdef": dict(
        H=SD + "; m > 0", Q="none",
        C="defines in order (C1) tau = 24, varpi = 1/2, beta = 1/4, w = 1/47; (C2) lambda_1, lambda_2, D_A, N_A, L_A, beta_*, "
          "a_kappa, W = lambda_2 + 1, vartheta = beta_*/W, c_Lambda = (4/7)(lambda_1 + lambda_2) + 1, K_* = 16 c_Lambda, j_* = "
          "(16 c_Lambda)^2; (C3) X, N_X, sigma_X, c_X; (C4) theta_0 and alpha_0; (C5) C_P, C_I, C_7 = L_A(C_P + C_I); (C6) per "
          "application Pi, alpha in (0,alpha_0], hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; every constant of "
          "(C1)-(C5) depends on m only", S="(C1)-(C5) depend on m only",
        deps=[("bpW:w7:freqcoords", "L215", "D_A, N_A, L_A"), ("bpW:w7:unpert-bounds", "L216", "beta_*, a_kappa"),
              ("bpW:w7:Xdef", "L218", "X"), ("bpW:w7:Xzones#consts", "L219", "sigma_X, c_X (defined in the statement of Lemma bpW:w7:Xzones)"),
              ("bpW:w7:ext-zeta", "L225", "Z_3")]),
    "bpW:w7:zones": dict(
        H="Pi subset {|xi|_infty <= 1/2} Borel, 0 < alpha <= alpha_0", Q="(k,l) in Z; D, omega', Omega'_j, a > 0",
        C="defines (i) the preparatory zones S_kl = {xi in Pi : |<k,omega^0> + <l,Omega^0>| < hat alpha hat w(l)/A_k} and Xi = "
          "union S_kl; (ii) zones R_kl(a) = {xi in D : |<k,omega'> + <l,Omega'>| < a <l>/A_k} for maps omega', Omega' on a "
          "Borel D subset Pi", S="none",
        deps=[("bpW:w7:constdef", "L256", "alpha_0, hat alpha"), ("bpW:w7:omega0", "L259", "omega^0, Omega^0"),
              ("bpW:w7:indexdef", "L259", "Z, A_k, hat w, <l>")]),
    "bpW:w7:family": dict(
        H="Pi, alpha as in Definition bpW:w7:zones", Q="none",
        C="defines an admissible family (D_nu,omega_nu,Omega_nu,K_nu)_{nu>=0}: D_nu subset Pi Borel, K_nu >= 2^nu, K_{-1} = 0, "
          "numbers eps_omega, eps_1, eps_2 in [0,alpha], theta in [0,theta_0] with (H1) |omega_nu - omega^0| <= eps_omega and "
          "Lipschitz theta; (H2) |Omega_{nu,j} - Omega^0_j| <= eps_1 j^{-1} + eps_2 j^{-1/2} and Lipschitz theta j^{-1/2}; its "
          "iteration zones R^nu_kl = R_kl(check alpha) and the excluded set E = Xi cup union R^nu_kl (|k| > K_{nu-1})", S="none",
        deps=[("bpW:w7:zones", "L277", "Xi and R_kl"), ("bpW:w7:constdef", "L269", "theta_0, check alpha"),
              ("bpW:w7:omega0", "L272", "omega^0, Omega^0")]),
    "bpW:w7:slab": dict(
        H="E subset R^2 Borel, nonempty, diam_infty E <= rho; phi : E -> R continuous on E; i in {1,2}, sigma > 0 with |phi(zeta "
          "+ t e_i) - phi(zeta)| >= sigma |t| whenever zeta, zeta + t e_i in E", Q="for every eta > 0",
        C="{zeta in E : |phi(zeta)| < eta} is Borel with measure <= 2 eta rho/sigma", S="none",
        deps=[("stepW:w7:slab-borel", "L324", PS), ("stepW:w7:slab-line", "L326", PS), ("stepW:w7:slab-int", "L330", PS)]),
    "stepW:w7:slab-borel": dict(H="", Q="none", C="the set is Borel", S="none", deps=[("bpW:w7:ext-borel", "L325", "Borel sets")]),
    "stepW:w7:slab-line": dict(H="", Q="y", C="Leb_1(T_y) <= 2 eta/sigma", S="none", deps=[("bpW:w7:ext-diam", "L329", "small diameter")]),
    "stepW:w7:slab-int": dict(H="", Q="none", C="integrating gives <= 2 eta rho/sigma", S="none",
        deps=[("bpW:w7:ext-tonelli", "L332", "Tonelli"), ("stepW:w7:slab-line", "L333", "one line")]),
    "bpW:w7:basic#data": dict(
        new=True, kind="definition", title="Fixed data for the zone estimates", stmt=f"{F}#bpW:w7:basic@L339-L343", proof="-",
        H="Pi, alpha in (0,alpha_0], an admissible family", Q="none",
        C="fixes Pi, alpha, an admissible family; rho = diam_infty Pi, rho_zeta = diam_infty omega^0(Pi) <= N_A rho; a "
          "frequency pair on Borel D subset Pi is (omega^0,Omega^0) (eps's and theta = 0) or some (omega_nu,Omega_nu) on D_nu; "
          "phi_kl = <k,omega'> + <l,Omega'> as a function of zeta in omega^0(D)", S="none",
        note="Unlabelled prose L339-L343 fixing the data of the zone lemmas (SPEC section-data rule).",
        deps=[("bpW:w7:family", "L339", "admissible family"), ("bpW:w7:freqcoords", "L340", "N_A, omega^0")]),
    "bpW:w7:sep": dict(
        H=FIX, Q="for a frequency pair on D and l in Lambda",
        C="|<l,Omega'(xi)>| >= 2 beta_* <l> on D; in particular |<l,Omega'>| >= a<l>/A_0 for a <= 2 beta_*, and R_{0l}(a) = "
          "S_{0l} = empty", S="none",
        deps=[("bpW:w7:basic#data", "L346", "frequency pairs"), ("stepW:w7:sep-drift", "L350", PS), ("stepW:w7:sep-concl", "L353", PS)]),
    "stepW:w7:sep-drift": dict(H="", Q="l", C="|<l,Omega' - Omega^0>| <= 4 alpha <= beta_* <l>", S="none",
        deps=[("bpW:w7:family", "L351", "(H2)"), ("bpW:w7:constdef", "L352", "(C4)")]),
    "stepW:w7:sep-concl": dict(H="", Q="l", C="the separation; S_{0l}, R_{0l} empty", S="none",
        deps=[("bpW:w7:unpert-bounds", "L354", "(ii)"), ("stepW:w7:sep-drift", "L354", "the drift")]),
    "bpW:w7:largek": dict(
        H=FIX + "; l in Lambda, a <= beta_*", Q="for a frequency pair on D",
        C="if {xi in D : |phi_kl(xi)| < a<l>/A_k} is nonempty then |k| >= vartheta <l>, in particular k != 0; likewise for "
          "S_kl (a = hat alpha)", S="none",
        deps=[("bpW:w7:basic#data", "L360", "frequency pairs, phi_kl"), ("stepW:w7:largek-tan", "L365", PS),
              ("stepW:w7:largek-cmp", "L368", PS)]),
    "stepW:w7:largek-tan": dict(H="", Q="none", C="|<k,omega'>| <= W|k|", S="none",
        deps=[("bpW:w7:unpert-bounds", "L366", "(i)"), ("bpW:w7:family", "L366", "(H1)")]),
    "stepW:w7:largek-cmp": dict(H="", Q="none", C="W|k| >= beta_* <l>", S="none",
        deps=[("bpW:w7:sep", "L370", "separation"), ("stepW:w7:largek-tan", "L369", "the tangential bound")]),
    "bpW:w7:zone": dict(
        H=FIX + "; k != 0; psi : D -> R with |psi(xi) - psi(xi')| <= (|k|/8)|omega^0(xi) - omega^0(xi')|", Q="for eta > 0",
        C="Leb{xi in D : |<k,omega'(xi)> + psi(xi)| < eta} <= 8 eta rho_zeta/(|k| D_A); this applies to psi = <l,Omega'> when "
          "l = 0 or l in Lambda with |k| >= 8 c_Lambda |l|_{-1/2}, and to constants", S="none",
        deps=[("bpW:w7:basic#data", "L375", "frequency pairs, rho_zeta"), ("stepW:w7:zone-lower", "L382", PS),
              ("stepW:w7:zone-slab", "L387", PS), ("stepW:w7:zone-psi", "L390", PS)]),
    "stepW:w7:zone-lower": dict(H="", Q="zeta", C="|phi(zeta + t e_i) - phi(zeta)| >= (|k|/4)|t|", S="none",
        deps=[("bpW:w7:family", "L385", "(H1)"), ("bpW:w7:freqcoords", "L385", "(iv)"), ("bpW:w7:constdef", "L385", "theta_0")]),
    "stepW:w7:zone-slab": dict(H="", Q="none", C="the measure bound via slicing", S="none",
        deps=[("bpW:w7:slab", "L388", "slicing"), ("bpW:w7:freqcoords", "L389", "(iv)"), ("stepW:w7:zone-lower", "L388", "sigma = |k|/4")]),
    "stepW:w7:zone-psi": dict(H="", Q="l", C="the admissible psi", S="none",
        deps=[("bpW:w7:unpert-bounds", "L391", "(iv)"), ("bpW:w7:family", "L391", "(H2)"), ("bpW:w7:constdef", "L392", "c_Lambda")]),
    "bpW:w7:Xdef": dict(
        H=SD + "; the constants K_*, vartheta, j_* of (C2)", Q="none",
        C="defines X = {(k,l) in Z^2 x Lambda : 1 <= |k| < K_*, <l> < K_*/vartheta, and l in Lambda^+ or l = +-(e_i - e_j) with "
          "i > j, j < j_*}", S="none",
        deps=[("bpW:w7:indexdef", "L399", "Lambda^+-, <l>")]),
    "bpW:w7:dichotomy": dict(
        H=FIX, Q="(k,l) in Z minus X, l in Lambda",
        C="X is finite; if a zone of Lemma bpW:w7:largek for (k,l) is nonempty then k != 0, <l> <= |k|/vartheta and |k| >= 8 "
          "c_Lambda |l|_{-1/2}", S="none",
        deps=[("bpW:w7:Xdef", "L404", "X"), ("stepW:w7:Xfinite", "L408", PS), ("stepW:w7:dich-large", "L411", PS),
              ("stepW:w7:dich-small", "L414", PS)]),
    "stepW:w7:Xfinite": dict(H="", Q="none", C="X is finite", S="none", deps=[("bpW:w7:indexdef", "L409", "<l> on Lambda^+")]),
    "stepW:w7:dich-large": dict(H="", Q="none", C="k != 0, <l> <= |k|/vartheta, and the |k| bound when |k| >= K_*", S="none",
        deps=[("bpW:w7:largek", "L412", "large k"), ("bpW:w7:constdef", "L412", "K_* = 16 c_Lambda")]),
    "stepW:w7:dich-small": dict(H="", Q="none", C="for |k| < K_*, (k,l) not in X forces l in Lambda^- with j >= j_*, whence the "
        "|k| bound", S="none", deps=[("bpW:w7:constdef", "L416", "j_*")]),
    "bpW:w7:Xzones#consts": dict(
        new=True, kind="definition", title="The exceptional-zone constants sigma_X, c_X", stmt=f"{F}#bpW:w7:Xzones@L422-L426", proof="-",
        H="m > 0; X (Definition bpW:w7:Xdef)", Q="(k,l) in X",
        C="defines g_kl(zeta) = <k,zeta> + <l,Omega^0(zeta)> = c_kl + <p_kl,zeta> with p_kl = k + (4/7)(sum_j l_j/lambda_j) lambda_J, "
          "sigma_X = min{|p_kl|_infty : (k,l) in X, p_kl != 0} and c_X = min{|<k,lambda_J> + <l,lambda>| : (k,l) in X, p_kl = 0} "
          "(minimum over the empty set := 1)", S="depend on m only",
        note="Definitional part of Lemma bpW:w7:Xzones, split off so that Definition bpW:w7:constdef (C3) can use sigma_X, c_X "
             "without depending on the lemma, whose proof uses (C4) (otherwise a dependency cycle).",
        deps=[("bpW:w7:Xdef", "L422", "X"), ("bpW:w7:freqcoords", "L423", "(iii) affine Omega^0"), ("bpW:w7:omega0", "L422", "Omega^0")]),
    "bpW:w7:Xzones": dict(
        H=FIX + "; for (k,l) in X, g_kl(zeta) = <k,zeta> + <l,Omega^0(zeta)> = c_kl + <p_kl,zeta>, p_kl = k + (4/7)(sum l_j/"
          "lambda_j) lambda_J; sigma_X, c_X as displayed", Q="for a frequency pair on D, (k,l) in X, 0 < a <= hat alpha",
        C="g_kl is not identically 0; sigma_X, c_X > 0; the zone Y = {xi in D : |phi_kl| < a<l>/A_k} is empty if p_kl = 0 and "
          "Leb(Y) <= 4 rho_zeta a K_*/(vartheta sigma_X D_A) if p_kl != 0", S="sigma_X, c_X depend only on m",
        deps=[("bpW:w7:Xdef", "L422", "X"), ("bpW:w7:freqcoords", "L423", "(iii)"), ("bpW:w7:Xzones#consts", "L424", "sigma_X, c_X"),
              ("stepW:w7:X-A3", "L431", PS), ("stepW:w7:X-const", "L436", PS), ("stepW:w7:X-slope", "L439", PS)]),
    "stepW:w7:X-A3": dict(H="", Q="(k,l) in X", C="g_kl not identically zero; constant case value nonzero; sigma_X, c_X > 0",
        S="none", deps=[("bpW:w0n:nondeg", "L433", "(iii) (A3)"), ("bpW:w7:freqcoords", "L434", "omega^0 bijective")]),
    "stepW:w7:X-const": dict(H="", Q="none", C="Y is empty when p_kl = 0", S="none",
        deps=[("bpW:w7:family", "L437", "(H1), (H2)"), ("bpW:w7:constdef", "L438", "(C4)"), ("stepW:w7:X-A3", "L437", "c_X")]),
    "stepW:w7:X-slope": dict(H="", Q="none", C="the measure bound when p_kl != 0", S="none",
        deps=[("bpW:w7:family", "L441", "(H1)-(H2)"), ("bpW:w7:constdef", "L442", "(C4)"), ("bpW:w7:slab", "L442", "slicing"),
              ("bpW:w7:freqcoords", "L443", "(iv)")]),
    "bpW:w7:count": dict(
        H="none", Q="N >= 1; k != 0",
        C="(i) #{l in Lambda^+ : <l> <= N} <= 4N^2; (ii) if K_nu >= 2^nu and K_{-1} = 0 then #{nu >= 0 : |k| > K_{nu-1}} <= |k|; "
          "(iii) sum_{k != 0} |k|^{-3} = Z_3 < 7", S="none", note="Inline proof (L454-L456).",
        deps=[("bpW:w7:indexdef", "L450", "Lambda^+ and <l>"), ("bpW:w7:ext-zeta", "L456", "(iii)")]),
}

DELETE = ["bpW:w7:reindex", "bpW:w7:choices", "bpW:w7:w6-needs"]

COV = {
    "bpW:w7:Xzones": ("NODE bpW:w7:Xzones, bpW:w7:Xzones#consts", "the lemma; its definitional part (sigma_X, c_X) is a separate definition node so that Definition bpW:w7:constdef (C3) does not depend on the lemma (cycle)"),
    "bpW:w7:reindex": ("EXCLUDED", "administrative remark (comparison of the Dirichlet labels and weights with P96-K's); W5-W6 "
                       "use the Dirichlet weights directly"),
    "bpW:w7:choices": ("EXCLUDED", "administrative remark (why tau = 24, varpi = 1/2, beta = 1/4); the values are fixed in "
                       "Definitions bpW:w7:indexdef and bpW:w7:constdef"),
    "bpW:w7:w6-needs": ("EXCLUDED", "administrative remark (what W6 must supply; forward references)"),
    "w7-measure:prose-L3-L8": ("EXCLUDED", "introduction"),
    "w7-measure:prose-L10-L21": ("EXCLUDED", "motivation (why the coarse estimate is not enough)"),
    "w7-measure:prose-L23-L31": ("EXCLUDED", "route paragraph (outline)"),
    "w7-measure:prose-L33-L41": ("NODE bpW:w7#data", "standing data of W7"),
    "w7-measure:prose-L45-L46": ("EXCLUDED", "layout"),
    "w7-measure:prose-L77-L78": ("EXCLUDED", "layout"),
    "w7-measure:prose-L124-L125": ("NODE bpW:w7:omega0", "notation lambda_J, b, A used in Definition bpW:w7:omega0"),
    "w7-measure:prose-L339-L343": ("NODE bpW:w7:basic#data", "fixed data of the zone lemmas"),
}
