# Writer spec for slice W-w8a (blueprint-W/parts/w8-assembly.tex L1-L410). Wave 2. Rendered by w_depgraph_fill.py.
F = "blueprint-W/parts/w8-assembly.tex"
STEP_CONTEXT = True
SYMBOL_EDGES = True
SYMBOL_OVERRIDE = {"bpW:w0:basis#lam": r"\\lambda_(?:[1-9JjiIn]|\{[jJiI])|\\Lean\{lam ",
                   "bpW:w0:basis#sineMode": r"\\Lean\{sineMode",
                   "bpW:w0:periodone#linearTorus": r"K\^0_|\\Lean\{linearTorus"}
PS = "proof step"
EXT = dict(H="none (Mathlib-level external fact)", Q="as stated in the item", S="none", deps=[])
SD = "W8 standing data (bpW:w8#data, L36-L53): m > 0, a = p = 1, max norms, Leb = volume, the constants of W2-W7, tau_E, r(I)"

NODES = {
    "bpW:w8:ext-inner": dict(EXT, C="if c_1, c_2 : R -> l^2_R are differentiable at t then s -> <c_1(s),c_2(s)> has derivative "
        "<c_1'(t),c_2(t)> + <c_1(t),c_2'(t)>; <f,g> = sum f_j g_j with absolutely summable terms; termwise sums and "
        "differences of summable series; Cauchy-Schwarz"),
    "bpW:w8:ext-mono": dict(EXT, C="a real function differentiable on an interval with nonpositive (nonnegative) derivative is "
        "antitone (monotone) there; derivatives of products and of t -> e^{ct}"),
    "bpW:w8:ext-compact": dict(EXT, C="a continuous map on [-T,T] is bounded; analytic maps are continuous"),
    "bpW:w8:ext-exp": dict(EXT, C="e^z = 1 iff z in 2 pi i Z; |e^{ix}| = 1 and |e^{ix} - 1| <= |x| for real x; a continuous "
        "integer-valued function on a connected space (R or R^2) is constant; if t -> tc is bounded on R then c = 0"),
    "bpW:w8:ext-sqrt": dict(EXT, C="for a > 0 and a + b >= 0: |sqrt(a+b) - sqrt(a)| <= |b|/sqrt(a)"),
    "bpW:w8:ext-dist": dict(EXT, C="x -> dist(x,S) is 1-Lipschitz, so {dist(x,S) > a} is open; it is 0 on S and <= |x - y| "
        "for y in S"),
    "bpW:w8:ext-rpow": dict(EXT, C="for x > 0: x^a x^b = x^{a+b}; x -> x^a monotone on [0,infinity) for a >= 0; x^a <= x^b for "
        "0 < x <= 1, a >= b; x^a >= 0 for x >= 0; x -> x^a continuous at 0 with value 0 for a > 0, hence tends to 0 along "
        "nhdsWithin 0 (Ioi 0)"),
    "bpW:w8:ext-local": dict(EXT, C="local continuity gives continuity on S; continuity transfers to maps agreeing on S; "
        "continuous linear maps preserve AnalyticOnNhd and compose with fderiv by the chain rule; inequalities pass to limits"),
    "bpW:w8#data": dict(
        new=True, kind="definition", title="W8 standing data and notation", stmt=f"{F}#bpW:w8@L36-L53", proof="-",
        H="none", Q="none",
        C="m > 0 and the W0 conventions, a = p = 1; max norms on R^2, C^2; Leb = volume on Fin 2 -> R; Fin 2 index i is mode "
          "i+1; shells indexed by n, W6's iteration index mu; the exponent 52 of W5-W6; W3's rho_1, C_*, C'_K, C_F, Z, Gamma, "
          "Gamma^R, r_1 = rho_1/sqrt2; W5's c_A and A_xi; W6's s, sigma_P, s_0, sigma_0, M, gamma_0, gamma_1, gamma, c_F, "
          "c^natural_F, C^natural_2, t^natural = 53; W7's tau = 24, theta_0, alpha_0, C_7, L_A, N_A, omega^0, Omega^0; W2's M_m; "
          "the transport tau_E = tau_{1,1} x tau_{1,1} : E_{1,1} -> WaveSpace, a linear isometric bijection with inverse coeff "
          "in each factor; r(I) = sqrt(I_1 + I_2); linearTorus I hI = tau_E o K^0_I (independent of hI)", S="none",
        note="Unlabelled 'Standing data and notation' paragraph (SPEC hypothesis packages).",
        deps=[("bpW:w0:mass", "L36", "m > 0"), ("bpW:w3:main", "L42", "Gamma"), ("bpW:w3:gamma-real", "L42", "Gamma^R"),
              ("bpW:w3:coords", "L41", "Z"), ("bpW:w5:action-angle", "L43", "c_A, A_xi"), ("bpW:w6:constants", "L45", "W6's constants"),
              ("bpW:w7:constdef", "L47", "W7's constants"), ("bpW:w7:omega0", "L47", "omega^0, Omega^0"),
              ("bpW:w7:freqcoords", "L48", "L_A, N_A"), ("bpW:w2:curve", "L48", "M_m"),
              ("bpW:w1:space", "L50", "(iv) tau_E isometric with inverse coeff"), ("bpW:w0:ellap#coeff", "L50", "coeff"),
              ("bpW:w0:ellap#WaveSpace", "L49", "WaveSpace"), ("bpW:w0:periodone#linearTorus", "L52", "linearTorus = tau_E o K^0_I"),
              ("bpW:w3:majorant", "L40", "C_*"), ("bpW:w3:F", "L40", "C_F")]),
    "bpW:w8:const": dict(
        H=SD, Q="none",
        C="defines E_1 = 1 + 2C_* + 6(2c_A)^{5/2} C'_K, E_3 = (1 + 8/M)E_1, E_4 = c^natural_F gamma sigma_P^{-52} + 5 c_F "
          "gamma_1 sigma_0^{-51}, E_5 = E_3 E_4/gamma, E_6 = 6 sqrt2 C_F (2c_A)^{3/2}, E_7 = 162 E_5 + E_6, t_0 = min{4^{-64}, "
          "alpha_0^{64/95}, rho_1^2/(8c_A), (gamma/E_3)^64, (7/(256 E_5))^64}, and the headline data tau = 24, r_0 = sqrt(2t_0), "
          "C_3 = 4 sqrt(c_A), C = max(1,M_m) C_3, eta(r) = 2^{33/64} E_7 r^{1/32}; all fixed after m and depending on m only",
        S="all depend on m only",
        deps=[("bpW:w8#data", "L101", "the constants of the standing data")]),
    "bpW:w8:shells": dict(
        H=SD + "; the constants of Definition bpW:w8:const", Q="n >= 0",
        C="defines q = 1/2, t_n = 2^{-n} t_0, R_n (W7's shells with q = 1/2), alpha_n = t_n^{95/64}, r_n = t_n^{3/4}, rho_{xi,n} "
          "= alpha_n/2, rho_n = (c_A(t_n + r_n^2))^{1/2}, eps^sharp_n = E_3 t_n^{3/2}, kappa_n = (E_3/gamma) t_n^{1/64}, eps_{0,n} = "
          "kappa_n^{4/3} gamma_1 check alpha_n (check alpha_n = alpha_n^{48/47}), hat alpha_n = alpha_n^{44/47}, and the trimmed "
          "shell Pi_n = U_{-alpha_n} R_n", S="depend on m and n",
        deps=[("bpW:w8:const", "L118", "t_0, E_3"), ("bpW:w7:shells", "L119", "W7's shells")]),
    "bpW:w8:shell-data": dict(
        H="Definitions bpW:w8:const and bpW:w8:shells", Q="for every n >= 0",
        C="(i) 0 < t_n <= t_0 <= 4^{-64}; alpha_n <= min(alpha_0, t_n); r_n <= 1; r_n^2 <= alpha_n/4; kappa_n <= 1 so eps^sharp_n "
          "<= gamma alpha_n; rho_n^2 <= 2 c_A t_n < rho_1^2/2 = r_1^2; (ii) Pi_n open, Pi_n subset R_n subset (0,t_n)^2 subset "
          "{|xi| <= 1/2}, alpha_n < xi_i < t_n - alpha_n, and |xi - xi'| > alpha_n for xi' not in R_n; (iii) the hypotheses of "
          "Proposition bpW:w5:initial hold (s = 1/8, r = r_n, t = t_n, rho_xi = rho_{xi,n}, Pi = Pi_n) with eps_in(1 + 8/M) <= "
          "eps^sharp_n, so |X_P|^lambda <= eps^sharp_n for lambda = alpha_n/M; (iv) the hypotheses of Lemma bpW:w6:prep-step hold "
          "(alpha = alpha_n, r = r_n, eps = eps^sharp_n) and those of Remark bpW:w6:to-w8", S="none",
        deps=[("bpW:w8:shells", "L133", "the shell data"),
              ("stepW:w8:sd-size", "L150", PS), ("stepW:w8:sd-trim", "L154", PS), ("stepW:w8:sd-init", "L160", PS),
              ("stepW:w8:sd-prep", "L168", PS)]),
    "stepW:w8:sd-size": dict(H="", Q="n", C="(i)", S="none", deps=[("bpW:w8:ext-rpow", "L151", "real powers"),
                                                                   ("bpW:w8:const", "L152", "the entries of t_0")]),
    "stepW:w8:sd-trim": dict(H="", Q="xi", C="(ii)", S="none",
        deps=[("bpW:w8:ext-dist", "L154", "distance to a set"), ("bpW:w7:shell-geom", "L159", "(i) disjoint shells")]),
    "stepW:w8:sd-init": dict(H="", Q="xi, zeta", C="(iii) eps_in <= E_1 t_n^{3/2} and |X_P|^lambda <= eps^sharp_n", S="none",
        deps=[("bpW:w5:initial", "L160", "its hypotheses and bound"), ("stepW:w8:sd-trim", "L162", "(ii)"),
              ("stepW:w8:sd-size", "L162", "(i)")]),
    "stepW:w8:sd-prep": dict(H="", Q="none", C="(iv)", S="none",
        deps=[("bpW:w6:prep-step", "L168", "its hypotheses"), ("bpW:w5:initial", "L170", "P real periodic in S_{p+1}"),
              ("stepW:w8:sd-init", "L171", "(iii)"), ("bpW:w6:to-w8", "L146", "its conditions")]),
    "bpW:w8:sharp-prep": dict(
        H="n fixed; Lemma bpW:w6:prep-step run with the data of Lemma bpW:w8:shell-data(iv), eps = eps^sharp_n", Q="none",
        C="eta_P = (eps^sharp_n/(hat alpha_n sigma_P^{53}))^{1/3} and |X_{P_0}|^{lambda_0}_{r_0,D_0} <= eps^flat_{0,n} := 2 "
          "C^natural_2 (eps^sharp_n)^{4/3}(hat alpha_n sigma_P^{53})^{-1/3} <= eps_{0,n} <= gamma_1 check alpha_n with lambda_0 "
          "= check alpha_n/(2M); eps^flat_{0,n} > 0", S="none",
        deps=[("bpW:w8:shell-data", "L179", "(iv)"), ("bpW:w6:prep-step", "L179", "the preparatory step"),
              ("stepW:w8:sp-step", "L187", PS), ("stepW:w8:sp-cmp", "L189", PS)]),
    "stepW:w8:sp-step": dict(H="", Q="none", C="the sharp bound", S="none", deps=[("bpW:w6:prep-step", "L187", "(v)")]),
    "stepW:w8:sp-cmp": dict(H="", Q="none", C="eps^flat_{0,n} <= eps_{0,n} <= gamma_1 check alpha_n", S="none",
        deps=[("bpW:w6:constants", "L192", "gamma"), ("bpW:w8:shell-data", "L193", "(i) kappa_n <= 1")]),
    "bpW:w8:shell-iter": dict(
        H="n >= 0; the shell data", Q="n",
        C="defines the shell iteration: Definition bpW:w6:wave-iteration with the data of Lemma bpW:w8:shell-data(iv) and eps_0 "
          "= eps_{0,n} (in [eps^flat_{0,n}, gamma_1 check alpha_n]); its outputs Pi^(n)_*, omega^(n)_*, nu^(n)_*, Phi^(n)_*, "
          "Phi^(n)_P, tilde Psi^(n)_xi, the admissible family and E^(n), e^(n)_tor, eps^(n)_omega; Gamma_n = Pi^(n)_*", S="none",
        deps=[("bpW:w6:wave-iteration", "L199", "W6's wave iteration"), ("bpW:w8:shell-data", "L200", "(iv)"),
              ("bpW:w8:sharp-prep", "L201", "the starting size is admissible"), ("bpW:w6:tori", "L203", "tilde Psi"),
              ("bpW:w7:family", "L204", "admissible family and excluded set")]),
    "bpW:w8:w6-general": dict(
        H="the shell iteration (Definition bpW:w8:shell-iter)", Q="for every n",
        C="the conclusions of Lemmas bpW:w6:applicable, bpW:w6:freq-lip (eps_omega = eps^(n)_omega, eps_1 = 3 gamma alpha_n, "
          "eps_2 = 4 eps_{0,n}, theta = 425(1+M) max(gamma,gamma_1) <= theta_0), bpW:w6:exclusion, bpW:w6:final-freq and "
          "Theorem bpW:w6:tori hold for the shell iteration, with e_tor = e^(n)_tor", S="none",
        deps=[("bpW:w8:shell-iter", "L213", "the shell iteration"),
              ("stepW:w8:g-app", "L219", PS), ("stepW:w8:g-freq", "L222", PS), ("stepW:w8:g-excl", "L224", PS),
              ("stepW:w8:g-tori", "L225", PS)]),
    "stepW:w8:g-app": dict(H="", Q="none", C="Lemma bpW:w6:applicable for the value eps_{0,n}", S="none",
        deps=[("bpW:w6:applicable", "L219", "applicability"), ("bpW:w8:sharp-prep", "L221", "eps_{0,n} admissible"),
              ("bpW:w6:to-w8", "L219", "the results hold for every eps_0 in the interval")]),
    "stepW:w8:g-freq": dict(H="", Q="none", C="Lemma bpW:w6:freq-lip for this value", S="none",
        deps=[("bpW:w6:freq-lip", "L222", "Lipschitz frequencies")]),
    "stepW:w8:g-excl": dict(H="", Q="none", C="Lemmas bpW:w6:exclusion and bpW:w6:final-freq for this value", S="none",
        deps=[("bpW:w6:exclusion", "L224", "exclusion"), ("bpW:w6:final-freq", "L224", "final frequencies")]),
    "stepW:w8:g-tori": dict(H="", Q="none", C="Theorem bpW:w6:tori with e_tor = e^(n)_tor", S="none",
        deps=[("bpW:w6:tori", "L225", "the tori")]),
    "bpW:w8:etor": dict(
        H="the shell iteration", Q="for every n",
        C="e^(n)_tor <= E_4 kappa_n = E_5 t_n^{1/64} <= 7/256, and eps^(n)_omega <= alpha_n/(70 L_A) <= alpha_n", S="none",
        deps=[("bpW:w8:shell-iter", "L232", "e^(n)_tor, eps^(n)_omega"), ("stepW:w8:e-tor", "L236", PS), ("stepW:w8:e-om", "L240", PS)]),
    "stepW:w8:e-tor": dict(H="", Q="n", C="e^(n)_tor <= E_5 t_n^{1/64} <= 7/256", S="none",
        deps=[("bpW:w8:const", "L238", "E_4, E_5, t_0")]),
    "stepW:w8:e-om": dict(H="", Q="n", C="eps^(n)_omega <= alpha_n/(70 L_A) <= alpha_n", S="none",
        deps=[("bpW:w6:constants", "L242", "gamma, gamma_1"), ("bpW:w7:constdef", "L242", "(C4) theta_0"),
              ("bpW:w7:freqcoords", "L243", "(ii) L_A")]),
    "bpW:w8:freq-shell": dict(
        H="the shell iteration", Q="for every n and xi, xi' in Gamma_n",
        C="(i) |(omega^(n)_* - omega^0)(xi) - (omega^(n)_* - omega^0)(xi')| <= theta_0 |xi - xi'|; (ii) |omega^(n)_*(xi) - "
          "omega^(n)_*(xi')| >= (7/(8 L_A))|xi - xi'|; (iii) |omega^(n)_*(xi) - omega^0(xi)| <= eps^(n)_omega <= alpha_n/(70 L_A) "
          "and |<k,omega^(n)_*(xi)>| >= check alpha_n/(2 A_k) for k != 0; (iv) nu^(n)_* is Lipschitz on Gamma_n and Gamma_n is Borel",
        S="none",
        deps=[("bpW:w8:shell-iter", "L249", "Gamma_n, omega^(n)_*"),
              ("stepW:w8:fs-lim", "L259", PS), ("stepW:w8:fs-low", "L262", PS), ("stepW:w8:fs-size", "L264", PS),
              ("stepW:w8:fs-reg", "L266", PS)]),
    "stepW:w8:fs-lim": dict(H="", Q="xi, xi'", C="(i) by passing (H1) to the limit", S="none",
        deps=[("bpW:w8:w6-general", "L260", "(H1)"), ("bpW:w6:convergence", "L261", "(ii)"), ("bpW:w8:ext-local", "L261", "limits")]),
    "stepW:w8:fs-low": dict(H="", Q="xi, xi'", C="(ii)", S="none",
        deps=[("bpW:w7:freqcoords", "L262", "(iv)"), ("bpW:w0n:nondeg", "L263", "(i) det A != 0"),
              ("stepW:w8:fs-lim", "L263", "(i)"), ("bpW:w7:constdef", "L263", "theta_0 <= 1/(8 L_A)")]),
    "stepW:w8:fs-size": dict(H="", Q="xi", C="(iii)", S="none",
        deps=[("bpW:w6:final-freq", "L264", "via Lemma bpW:w8:w6-general"), ("bpW:w8:w6-general", "L264", "transfer"),
              ("bpW:w8:etor", "L265", "eps_omega bound")]),
    "stepW:w8:fs-reg": dict(H="", Q="none", C="(iv)", S="none",
        deps=[("bpW:w6:tori", "L266", "(ii)"), ("bpW:w8:w6-general", "L266", "transfer"), ("bpW:w6:convergence", "L267", "(i)"),
              ("bpW:w8:shell-data", "L267", "(ii)"), ("bpW:w7:measurable", "L267", "Borel"), ("stepW:w6:fl-borel", "L268", "continuity")]),
    "bpW:w8:torus-shape": dict(
        H="n >= 0, xi in Gamma_n, Psi = tilde Psi^(n)_xi, Phi^(n)_P Phi^(n)_*(theta) = (theta + X(theta), y(theta), u(theta), "
          "v(theta)) on T_{s_0/2}, e = e^(n)_tor", Q="theta (complex or real as stated)",
        C="(i) X, y holomorphic with |X| <= e, |y| <= r_n^2 e and ||hat Psi|| <= r_n e; (ii) for real theta, X, y real, xi_i + "
          "y_i >= (3/4) alpha_n > 0 and Psi_{+-i} = sqrt(xi_i + y_i) e^{-+2 pi i(theta_i + X_i)}; (iii) X(theta + k) = X(theta); "
          "(iv) ||DX(theta)|| <= 128e/7 <= 1/2 and X is 1/2-Lipschitz on R^2; (v) ||Psi(theta)|| < rho_n <= r_1 and x(theta) = "
          "Z^{-1} Psi(theta) in B^E_{r_1} is real", S="none",
        deps=[("bpW:w8:shell-iter", "L276", "tilde Psi, Phi_P, Phi_*"), ("bpW:w6:tori", "L277", "(iv)"),
              ("stepW:w8:ts-bd", "L291", PS), ("stepW:w8:ts-real", "L294", PS), ("stepW:w8:ts-per", "L300", PS),
              ("stepW:w8:ts-cauchy", "L303", PS), ("stepW:w8:ts-ball", "L307", PS)]),
    "stepW:w8:ts-bd": dict(H="", Q="theta", C="(i)", S="none",
        deps=[("bpW:w6:tori", "L291", "(iv)"), ("bpW:w8:w6-general", "L291", "transfer"), ("bpW:w5:action-angle", "L293", "(vi)")]),
    "stepW:w8:ts-real": dict(H="", Q="real theta", C="(ii)", S="none",
        deps=[("bpW:w6:tori", "L294", "(i), (iv)"), ("bpW:w3:coords", "L295", "rho"), ("bpW:w8:shell-data", "L297", "(i), (ii)"),
              ("bpW:w8:ext-exp", "L299", "complex exponential"), ("stepW:w8:ts-bd", "L297", "(i)")]),
    "stepW:w8:ts-per": dict(H="", Q="k", C="(iii)", S="none",
        deps=[("bpW:w6:tori", "L300", "(i) periodicity"), ("bpW:w8:ext-exp", "L301", "integer-valued continuous functions"),
              ("stepW:w8:ts-real", "L300", "(ii)")]),
    "stepW:w8:ts-cauchy": dict(H="", Q="real theta", C="(iv)", S="none",
        deps=[("bpW:w1:cauchy", "L304", "Cauchy estimate"), ("bpW:w8:etor", "L304", "e <= 7/256"), ("stepW:w8:ts-bd", "L304", "|X| <= e")]),
    "stepW:w8:ts-ball": dict(H="", Q="real theta", C="(v)", S="none",
        deps=[("bpW:w5:action-angle", "L308", "(ii)"), ("bpW:w8:shell-data", "L308", "(i)"), ("bpW:w3:coords", "L309", "Z^{-1}")]),
    "bpW:w8:Kshell": dict(
        H="n >= 0, xi in Gamma_n, theta in R^2", Q="n, xi, theta",
        C="defines K^(n)_xi(theta) = tau_E(Gamma^R(Z^{-1} tilde Psi^(n)_xi(theta))) = tau_E(Z^{-1} Gamma(tilde Psi^(n)_xi(theta))) "
          "in WaveSpace", S="none",
        deps=[("bpW:w8#data", "L316", "tau_E, Gamma, Gamma^R, Z"), ("bpW:w8:torus-shape", "L318", "(v) well defined"),
              ("bpW:w3:gamma-real", "L318", "Gamma^R")]),
    "bpW:w8:shell-embedding": dict(
        H="n >= 0, xi in Gamma_n", Q="for every n, xi", C="IsAnalyticTorusEmbedding K^(n)_xi", S="none",
        deps=[("bpW:w8:Kshell", "L324", "K^(n)_xi"),
              ("stepW:w8:se-per", "L328", PS), ("stepW:w8:se-an", "L329", PS), ("stepW:w8:se-inj", "L331", PS),
              ("stepW:w8:se-der", "L338", PS)]),
    "stepW:w8:se-per": dict(H="", Q="k", C="K(theta + k) = K(theta)", S="none", deps=[("bpW:w6:tori", "L328", "(i)")]),
    "stepW:w8:se-an": dict(H="", Q="none", C="AnalyticOnNhd R K univ", S="none",
        deps=[("bpW:w6:tori", "L329", "(v)"), ("bpW:w8:ext-local", "L330", "continuous linear maps preserve AnalyticOnNhd")]),
    "stepW:w8:se-inj": dict(H="", Q="theta, theta'", C="injectivity modulo Z^2", S="none",
        deps=[("bpW:w3:gamma-real", "L332", "(iii) injectivity"), ("bpW:w8:torus-shape", "L333", "(ii)-(v)"),
              ("bpW:w8:ext-exp", "L335", "e^z = 1")]),
    "stepW:w8:se-der": dict(H="", Q="theta, h", C="fderiv R K theta is injective", S="none",
        deps=[("bpW:w1:torus-analytic", "L339", "fderiv via the complex derivative"), ("stepW:w6:t-an", "L339", "holomorphy"),
              ("bpW:w8:ext-local", "L340", "chain rule"), ("bpW:w3:flow", "L342", "(iii) invertible, (iv) real"),
              ("bpW:w8:torus-shape", "L345", "(ii), (iv)")]),
    "bpW:w8:shell-close": dict(
        H="n >= 0, xi in Gamma_n, theta in R^2; K^0_xi the linear torus", Q="for all such n, xi, theta",
        C="||K^(n)_xi(theta) - tau_E K^0_xi(theta)|| <= E_7 t_n^{33/64} and ||K^(n)_xi(theta)|| <= 2 rho_n", S="E_7 depends on m only",
        deps=[("bpW:w8:Kshell", "L357", "K^(n)_xi"), ("bpW:w8:const", "L357", "E_7"),
              ("stepW:w8:sc-tan", "L362", PS), ("stepW:w8:sc-dist", "L366", PS), ("stepW:w8:sc-gamma", "L370", PS),
              ("stepW:w8:sc-close", "L373", PS), ("stepW:w8:sc-size", "L376", PS)]),
    "stepW:w8:sc-tan": dict(H="", Q="i", C="|w_{+-i} - w^0_{+-i}| <= (1 + 2pi) sqrt(t_n) e", S="none",
        deps=[("bpW:w8:torus-shape", "L362", "(ii)"), ("bpW:w8:ext-sqrt", "L365", "square roots"), ("bpW:w8:ext-exp", "L365", "|e^{ix}-1| <= |x|"),
              ("bpW:w8:shell-data", "L365", "(ii)"), ("bpW:w5:action-angle", "L361", "(i) the linear torus")]),
    "stepW:w8:sc-dist": dict(H="", Q="none", C="||x - x^0||_E <= 162 sqrt(t_n) e", S="none",
        deps=[("stepW:w8:sc-tan", "L367", "tangential modes"), ("bpW:w8:torus-shape", "L368", "(i)"), ("bpW:w3:coords", "L369", "Z")]),
    "stepW:w8:sc-gamma": dict(H="", Q="none", C="||Gamma^R(x) - x||_E <= E_6 t_n^{3/2}", S="none",
        deps=[("bpW:w3:gamma-real", "L370", "(ii)"), ("bpW:w1:embed", "L370", "norm comparison"), ("bpW:w8:torus-shape", "L372", "(v)")]),
    "stepW:w8:sc-close": dict(H="", Q="none", C="the closeness bound", S="none",
        deps=[("stepW:w8:sc-dist", "L374", "distance"), ("stepW:w8:sc-gamma", "L374", "Birkhoff map"), ("bpW:w8:etor", "L375", "e")]),
    "stepW:w8:sc-size": dict(H="", Q="none", C="||K^(n)_xi(theta)|| < 2 rho_n", S="none",
        deps=[("bpW:w3:flow", "L376", "rho_1^2 = 1/(160 C_F)"), ("bpW:w3:gamma-real", "L376", "(ii)")]),
    "bpW:w8:shell-inv": dict(
        H="n >= 0", Q="(i) for xi in Gamma_n, theta in R^2, j in N_+",
        C="(i) with K = K^(n)_xi, nu = nu^(n)_*(xi): t -> coeff (K(theta + t nu)).1 j has derivative lambda_j coeff (K theta).2 j "
          "at 0 and t -> coeff (K(theta + t nu)).2 j has derivative -lambda_j coeff (K theta).1 j - cubicGrad m hm (K theta).1 j "
          "at 0 (clause (4)); (ii) (xi,theta) -> K^(n)_xi(theta) is continuous on Gamma_n x R^2", S="none",
        deps=[("bpW:w8:Kshell", "L386", "K^(n)_xi"), ("bpW:w8:shell-iter", "L386", "nu^(n)_*"),
              ("stepW:w8:si-weak", "L394", PS), ("stepW:w8:si-tr", "L398", PS), ("stepW:w8:si-frozen", "L400", PS),
              ("stepW:w8:si-cont", "L404", PS)]),
    "stepW:w8:si-weak": dict(H="", Q="real theta", C="Psi maps into B_{rho_1}, is differentiable into W, real, and D Psi nu = "
        "X_{H'}(Psi) in W_{a,p-1}", S="none",
        deps=[("bpW:w6:tori", "L394", "(i), (iii)"), ("bpW:w8:w6-general", "L394", "transfer"), ("bpW:w3:main", "L397", "H'")]),
    "stepW:w8:si-tr": dict(H="", Q="theta", C="the coefficient system along nu for (Q,P) = Z^{-1} Gamma o Psi", S="none",
        deps=[("bpW:w3:transport-tori-weak", "L398", "weak invariance is transported"), ("bpW:w0:eqmotion", "L398", "(bpW:w0:coeffsys)"),
              ("stepW:w8:si-weak", "L398", "its hypothesis")]),
    "stepW:w8:si-frozen": dict(H="", Q="theta, j", C="(i) in the frozen form", S="none",
        deps=[("bpW:w1:coordinatewise", "L402", "coordinates of the derivative"), ("bpW:w1:cubic-analytic", "L402", "(iv)"),
              ("stepW:w8:si-tr", "L400", "the coefficient system"), ("bpW:w8#data", "L400", "tau_E and coeff")]),
    "stepW:w8:si-cont": dict(H="", Q="none", C="(ii) continuity", S="none",
        deps=[("bpW:w6:tori", "L404", "(ii)"), ("bpW:w8:w6-general", "L404", "transfer"), ("bpW:w8:torus-shape", "L405", "(v)"),
              ("bpW:w3:gamma-real", "L406", "(i) Gamma^R analytic")]),
}

DELETE = []

COV = {
    "w8-assembly:prose-L5-L11": ("EXCLUDED", "introduction"),
    "w8-assembly:prose-L13-L34": ("EXCLUDED", "outline of what W8 adds (pointers to the lemmas that carry it)"),
    "w8-assembly:prose-L36-L53": ("NODE bpW:w8#data", "standing data and notation of W8"),
    "w8-assembly:prose-L57-L58": ("EXCLUDED", "layout"),
    "w8-assembly:prose-L93-L94": ("EXCLUDED", "layout"),
    "w8-assembly:prose-L98-L98": ("NODE bpW:w8:const", "all numbers are fixed after m and depend on m only (recorded in the "
                                  "CONSTANT_SCOPE of Definition bpW:w8:const)"),
}
