# Writer spec for slice W-w5a (blueprint-W/parts/w5-kamstep.tex L1-L449). Wave 2. Rendered by w_depgraph_fill.py.
F = "blueprint-W/parts/w5-kamstep.tex"
STEP_CONTEXT = True
SYMBOL_EDGES = True
# in W5-W8 a bare \lambda is P96-K's weighting parameter; only subscripted frequencies lambda_J count as frozen lam
SYMBOL_OVERRIDE = {"bpW:w0:basis#lam": r"\\lambda_(?:[1-9JjiIn]|\{[jJiI])"}
PS = "proof step"
EXT = dict(H="none (Mathlib-level external fact)", Q="as stated in the item", S="none", deps=[])
SD = "W5 standing data (L35-L39): a = p = 1, wave weights omega_{a,q}(j+2) (Convention bpW:w4:index)"
FR = "frequencies (omega, Omega) on Pi satisfying (bpW:w5:freq) with constants M_0, M_omega, M_Omega"

NODES = {
    "bpW:w5:ext-taylor": dict(EXT, C="if g is holomorphic on |t| < rho with values in a complex Banach space and ||g(t)|| <= "
        "B there, then g(t) = sum g_k t^k on |t| < rho with the Cauchy coefficients g_k, ||g_k|| <= B rho^{-k}, and for |t| "
        "<= 1 < rho: ||g(t) - sum_{k<=2} g_k t^k|| <= B rho^{-3}/(1 - rho^{-1})"),
    "bpW:w5:ext-ftc": dict(EXT, C="for C^1 c : [0,1] -> V (open in a Banach space) and G C^1 on V: G(c(1)) - G(c(0)) = int_0^1 "
        "DG(c(t)) c'(t) dt; differentiation under the integral (W3-E5); Neumann series (W3-E6); Gronwall (W1-E7)"),
    "bpW:w5#data": dict(
        new=True, kind="definition", title="W5 weights a = p = 1", stmt=f"{F}#bpW:w5@L35-L39", proof="-",
        H="none", Q="none",
        C="fixes a = p = 1 throughout W5 (Convention bpW:w0:weights); this satisfies the weight guard (G) of W4's bracket "
          "identity and p >= 1/2; normal quantities carry the wave weights omega_{a,q}(J), J = j+2", S="none",
        note="Unlabelled 'Weights' paragraph (SPEC hypothesis packages); its premise a = p = 1 is recorded in the "
             "SOURCE_HYPOTHESES of W5 results that use it (guard (G), pairings).",
        deps=[("bpW:w0:ellap#WaveSpace", "L35", "the headline weights a = p = 1 (Convention bpW:w0:weights)"),
              ("bpW:w4:lie-sec#guard", "L36", "the guard (G) holds for a = p = 1"),
              ("bpW:w4:index", "L37", "the wave weights")]),
    "bpW:w5:setting": dict(
        H=SD + "; typing data: q in R, r > 0", Q="q, r",
        C="defines P^q = C^2 x C^2 x l^N_{a,q} x l^N_{a,q} with points W = (Theta,Y,U,V) and |W|_{q,r} = |Theta| + |Y|/r^2 + "
          "(||U||_{a,q} + ||V||_{a,q})/r; P = P^p; D(s,r) subset P; real points and P^q_R; the bilinear form varpi(W,W') = "
          "2 pi(<Theta,Y'> - <Y,Theta'>) + <U,V'>_0 - <V,U'>_0; operator norms |L|_{q -> q',r}", S="none",
        deps=[("bpW:w1:kam-space", "L64", "the norm and the domain D(s,r)"), ("bpW:w4:index", "L65", "the normal spaces"),
              ("bpW:w5#data", "L63", "a = p = 1")]),
    "bpW:w5:omega": dict(
        H=SD + "; varpi on P", Q="for all W, W'; r > 0; q >= p, r' <= r",
        C="varpi is continuous, antisymmetric and nondegenerate on P, |varpi(W,W')| <= (4 pi r^2 + 2 r^2)|W|_{p,r} |W'|_{p,r}; "
          "|W|_{p,r} <= |W|_{q,r} and |W|_{q,r} <= |W|_{q,r'} <= (r/r')^2 |W|_{q,r}", S="none",
        deps=[("bpW:w5:setting", "L76", "varpi and the norms"),
              ("stepW:w5:ombd", "L81", PS), ("stepW:w5:omnd", "L83", PS), ("stepW:w5:omnorm", "L86", PS)]),
    "stepW:w5:ombd": dict(H="", Q="W, W'", C="the bound on varpi", S="none",
        deps=[("bpW:w4:index", "L82", "(bpW:w4:pairing)")]),
    "stepW:w5:omnd": dict(H="", Q="W", C="testing with unit vectors gives nondegeneracy", S="none", deps=[]),
    "stepW:w5:omnorm": dict(H="", Q="q, r, r'", C="the norm comparisons", S="none",
        deps=[("bpW:w1:embed", "L86", "weights increase with q")]),
    "bpW:w5:class": dict(
        H=SD + "; p_+ in [p+1/2, p+1], V subset P open, Pi subset R^2 (max norm); lambda >= 0, r > 0", Q="p_+, V, Pi, lambda, r",
        C="defines S_{p_+}(V): holomorphic P : V -> C with a holomorphic X_P : V -> P^{p_+}, DP(w)W = varpi(X_P(w),W) (unique "
          "by Lemma bpW:w5:omega; X_P = (P_y/(2pi), -P_theta/(2pi), P_v, -P_u)); real P; families P(.,xi); the norm "
          "|X_P|^lambda_{r,V} = sup |X_{P(xi)}|_{p_+,r} + lambda sup (Lipschitz quotient), read as the conjunction of two "
          "bounds", S="none",
        deps=[("bpW:w1:holomorphic", "L93", "holomorphic maps"), ("bpW:w5:setting", "L94", "varpi, P^{p_+}"),
              ("bpW:w5:omega", "L96", "uniqueness of X_P"), ("bpW:w4:taylor", "L97", "the field formula")]),
    "bpW:w5:lambda-product": dict(
        kind="claim",
        H="|a(xi)| <= A_0, |a(xi) - a(zeta)| <= A_1|xi - zeta| and likewise for b; a.b a product of norm <= 1", Q="lambda >= 0",
        C="A_0 B_0 + lambda(A_1 B_0 + A_0 B_1) <= (A_0 + lambda A_1)(B_0 + lambda B_1): the lambda-norm is submultiplicative",
        S="none", note="Remark kept as a node: \"used without comment below\"; consumers that bound lambda-norms of "
                       "products depend on it.", deps=[]),
    "bpW:w5:w4-general": dict(
        H=SD + "; p_+ in [p+1/2, p+1]; in W4 the exponent bar p = p+1 replaced by p_+ and (bpW:w4:freq) by (bpW:w5:freq)",
        Q="for every such p_+",
        C="Lemma bpW:w4:lie, Theorem bpW:w4:lemma1 and Corollary bpW:w4:lemma2 hold verbatim with the same constants C_1, "
          "B^W_sigma, 3C_1, except that Theorem bpW:w4:lemma1(iv) reads sup_j (j+2)^{p_+-p}|hat Omega_j| <= eps (likewise "
          "for differences); (bpW:w5:freq): Omega_j = j + 2 + tilde Omega_j, sup j^{1/2}|tilde Omega_j| <= M_0, Lipschitz "
          "bounds with sup j^{1/2}", S="C_1, B^W_sigma as in W4",
        deps=[("bpW:w4:lie", "L130", "restated"), ("bpW:w4:lemma1", "L130", "restated"), ("bpW:w4:lemma2", "L130", "restated"),
              ("bpW:w4:ops", "L124", "the exponent bar p replaced"), ("bpW:w4:taylor", "L125", "the exponent bar p replaced"),
              ("stepW:w5:g-pair", "L136", PS), ("stepW:w5:g-tail", "L139", PS), ("stepW:w5:g-div", "L141", PS),
              ("stepW:w5:g-diag", "L144", PS), ("stepW:w5:g-rest", "L147", PS)]),
    "stepW:w5:g-pair": dict(H="", Q="none", C="the pairings need q + q' >= 0; the pairs (p_+,p), (p,p), (p-1,p_+) qualify "
        "since p = 1", S="none", deps=[("bpW:w4:index", "L136", "(bpW:w4:pairing)"), ("bpW:w4:ops", "L136", "the pairs"),
                                       ("bpW:w4:lie", "L137", "(i)"), ("bpW:w5#data", "L138", "p = 1")]),
    "stepW:w5:g-tail": dict(H="", Q="none", C="the tails enter only Step stepW:w4:liebd via |Omega_j| <= (1+M_0)(j+2), which "
        "still holds", S="none", deps=[("stepW:w4:liebd", "L139", "the only use of the tails")]),
    "stepW:w5:g-div": dict(H="", Q="none", C="Step stepW:w4:divlip uses the Lipschitz bound only through the sum, which "
        "holds with j^{-1/2} <= 1", S="none", deps=[("stepW:w4:divlip", "L141", "its use of M_Omega")]),
    "stepW:w5:g-diag": dict(H="", Q="none", C="Lemma bpW:w4:schur(iii) with mu_i nu_i = (i+2)^{p_+-p}; used only in Step "
        "stepW:w4:Nhat", S="none", deps=[("bpW:w4:schur", "L144", "(iii)"), ("stepW:w4:Nhat", "L145", "its only use")]),
    "stepW:w5:g-rest": dict(H="", Q="none", C="the remaining W4 lemmas are stated for arbitrary Banach spaces or weights",
        S="none", deps=[("bpW:w4:fourier-ops", "L147", "general"), ("bpW:w4:lattice", "L148", "general"),
                        ("bpW:w4:schur", "L148", "(i)-(ii)"), ("bpW:w4:solve", "L148", "general"),
                        ("bpW:w4:extract", "L148", "general"), ("bpW:w4:components", "L148", "general")]),
    "bpW:w5:w4-modified": dict(
        H=SD + "; (bpW:w5:freq) with M = M_omega + M_Omega > 0; hat alpha > 0; beta in (0,1/2]; p_+ in [p+1/2, p+1] with "
          "beta <= p+1-p_+; every divisor of Definition bpW:w4:melnikov satisfies the bound of (H_{hat alpha}) except "
          "delta^Q_{k,ij}, i != j, for which only (bpW:w5:modified) |delta^Q| >= (hat alpha/A_k)|i-j|/(min(i,j)+2)^beta; R as "
          "in Theorem bpW:w4:lemma1 with bar p = p+1; F, hat N by the same formulas", Q="for all such data; (ii) moreover 2 beta "
          "<= p+1-p_+; (iii) 0 < sigma <= 1",
        C="(i) F(.,xi) in T_{s-sigma} with Q_F, Q_F^T bounded l^N_{a,p} -> l^N_{a,p_+}, all other components as in W4; the "
          "equation (ii) and bounds (iv) of Theorem bpW:w4:lemma1 hold and |X_F|_{p_+,r} <= C_1 B^W_sigma eps/hat alpha; (ii) "
          "the Lipschitz bound with B^natural_sigma = sum (1+|k|_1)^2 A_k^2 e^{-2 pi |k|_1 sigma} >= B^W_sigma, and the "
          "lambda-form with 3 C_1 B^natural_sigma/hat alpha for 0 <= lambda <= hat alpha/M; (iii) B^natural_sigma <= "
          "b^natural(tau) sigma^{-(2tau+4)}, b^natural(tau) = 4(C_0 + C_2 + C_{2tau} + C_{2tau+2})",
        S="C_1 absolute; b^natural depends only on tau",
        deps=[("bpW:w4:melnikov", "L158", "divisors and (H_{hat alpha})"), ("bpW:w4:lemma1", "L163", "R, F, hat N"),
              ("stepW:w5:m-sup", "L180", PS), ("stepW:w5:m-other", "L185", PS), ("stepW:w5:m-lip", "L187", PS),
              ("stepW:w5:m-act", "L191", PS), ("stepW:w5:m-ass", "L213", PS), ("stepW:w5:m-const", "L218", PS)]),
    "stepW:w5:m-sup": dict(H="I = i+2, J = j+2, c = p+1-p_+", Q="k", C="the Q-division gives an operator l^N_{a,p} -> "
        "l^N_{a,p_+} with kappa = K_S; likewise Q_F^T", S="none",
        deps=[("bpW:w4:schur", "L183", "Hadamard division")]),
    "stepW:w5:m-other": dict(H="", Q="none", C="the other components obey (H_{hat alpha}); W4's bounds hold in "
        "l^N_{a,p+1} subset l^N_{a,p_+}", S="none", deps=[("bpW:w4:lemma1", "L186", "its bounds")]),
    "stepW:w5:m-lip": dict(H="I = i+2, J = j+2, c = p+1-p_+", Q="xi, zeta", C="the Lipschitz bound of d_ij carries "
        "min(I,J)^{2beta}, compensated when 2 beta <= c; Lemma bpW:w4:solve(ii) applies", S="none",
        deps=[("stepW:w4:divlip", "L187", "the divisor difference"), ("bpW:w4:solve", "L190", "(ii)"),
              ("stepW:w4:lip", "L190", "as in this step")]),
    "stepW:w5:m-act": dict(H="", Q="i, xi, zeta", C="d_{theta_i} Q_F bounded as an operator l^N_{a,p} -> l^N_{a,p_+} by "
        "2 pi K_S B^W_sigma eps/hat alpha; the differences with B^natural_sigma", S="none",
        deps=[("bpW:w4:components", "L195", "(i): ||Q|| <= eps"), ("bpW:w4:w1-requests", "L196", "(F1), (F2)"),
              ("stepW:w5:m-sup", "L197", "the Q-division"), ("bpW:w1:ext-unifderiv", "L199", "termwise differentiation"),
              ("bpW:w4:index", "L202", "(bpW:w4:pairing)"), ("stepW:w5:m-lip", "L206", "the divisor differences"),
              ("bpW:w4:fourier-ops", "L209", "(iii)")]),
    "stepW:w5:m-ass": dict(H="", Q="none", C="W4's assembly with the Q_F contribution from Step stepW:w5:m-act; the "
        "lambda-form as in Corollary bpW:w4:lemma2", S="none",
        deps=[("stepW:w4:Fcomp", "L213", "W4's component bounds"), ("stepW:w4:assembly", "L213", "W4's assembly"),
              ("stepW:w4:Nhat", "L213", "W4's hat N step"), ("stepW:w5:m-act", "L214", "the Q_F contribution"),
              ("bpW:w4:lemma2", "L217", "the lambda-form")]),
    "stepW:w5:m-const": dict(H="", Q="sigma <= 1", C="B^natural_sigma <= 4(S_0 + S_2 + S_{2tau} + S_{2tau+2}) <= "
        "b^natural(tau) sigma^{-(2tau+4)}", S="b^natural depends only on tau",
        deps=[("bpW:w4:lattice", "L219", "(ii), (iii)")]),
    "bpW:w5:taylor": dict(
        H=SD + "; s, r > 0; p_+ in [p+1/2, p+1]; P(.,xi) in S_{p_+}(D(s,r)) real, 1-periodic in each theta_i, |X_P|^lambda_"
          "{r,D(s,r)} <= eps; S_t, T_t the scalings; a, b, g, H and R as displayed", Q="for all such P; eta in (0,1/8] for (iv)",
        C="(i) R(.,xi) in T_s (bar p = p_+) with the displayed components c^+-, P, Q, P' in z, zbar, holomorphic, periodic, "
          "bounded, P, P' symmetric; R real; R(w) = sum_{k<=2} (1/k!) d_t^k P(S_t w)|_{t=0}; (ii) X_R(w) = sum_{k<=2} (1/k!) "
          "d_t^k G(t,w)|_{t=0}, G(t,w) = T_t X_P(S_t w); (iii) |X_R|^lambda_{r,D(s,r)} <= 3 eps; (iv) |X_P - X_R|^lambda_{eta "
          "r,D(s,4 eta r)} <= 128 eta eps", S="constants 3 and 128 absolute",
        deps=[("bpW:w5:class", "L252", "the class S_{p_+} and the lambda-norm"), ("bpW:w4:taylor", "L260", "the class T_s"),
              ("bpW:w4:index", "L261", "the z, zbar coordinates"),
              ("stepW:w5:t-scale", "L273", PS), ("stepW:w5:t-disc", "L277", PS), ("stepW:w5:t-poly", "L280", PS),
              ("stepW:w5:t-comp", "L285", PS), ("stepW:w5:t-field", "L293", PS), ("stepW:w5:t-est", "L299", PS)]),
    "stepW:w5:t-scale": dict(H="", Q="t != 0", C="varpi(X, S_t W') = varpi(T_t X, W'); X_{P o S_t} = G(t,.), holomorphic in "
        "(t,w) including t = 0", S="none", deps=[("bpW:w5:setting", "L273", "varpi")]),
    "stepW:w5:t-disc": dict(H="", Q="r' <= r", C="S_t w in D(s,r) for |t| < r/r' and |T_t X|_{p_+,r'} <= rho^2 |X|_{p_+,r}",
        S="none", deps=[]),
    "stepW:w5:t-poly": dict(H="", Q="w", C="the Taylor coefficients of t -> P(S_t w) are a, <g,(u,v)>_0 and <b,y> + (1/2)"
        "<H(u,v),(u,v)>_0; last claim of (i)", S="none", deps=[("bpW:w5:class", "L283", "DP W = varpi(X_P,W)")]),
    "stepW:w5:t-comp": dict(H="", Q="theta", C="a, b, g holomorphic; H a Cauchy integral, holomorphic, bounded, symmetric; "
        "the z-blocks; reality and periodicity", S="none",
        deps=[("bpW:w1:deriv-continuous", "L287", "the derivative as a Cauchy integral"), ("bpW:w1:cauchy", "L288", "bound"),
              ("bpW:w4:index", "L291", "substitution u, v in z, zbar")]),
    "stepW:w5:t-field": dict(H="", Q="w, W'", C="DR(w)W' = varpi(sum g_k(w), W') so X_R = sum_{k<=2} g_k (ii)", S="none",
        deps=[("stepW:w5:t-scale", "L295", "X_{P o S_t} = G(t,.)"), ("bpW:w5:omega", "L297", "uniqueness")]),
    "stepW:w5:t-est": dict(H="", Q="w", C="(iii) |X_R| <= 3 eps; (iv) |X_P - X_R| <= 128 eta eps; Lipschitz parts by "
        "linearity", S="none",
        deps=[("stepW:w5:t-disc", "L300", "the disc of radius > 1"), ("bpW:w5:ext-taylor", "L301", "Taylor coefficients and "
              "remainder"), ("bpW:w5:omega", "L304", "norm comparison")]),
    "bpW:w5:data": dict(
        H=SD + "; p_+ in [p+1/2, p+1]; tau >= 0; 0 < s <= 1, 0 < sigma <= min(1/4, s/6), 0 < eta <= 1/8, r > 0; Pi subset R^2; "
          + FR + " with M > 0; alpha > 0 with (H_alpha) on Pi or (modified case) the hypotheses of Lemma bpW:w5:w4-modified with "
          "hat alpha = alpha; 0 <= lambda <= alpha/M; N = <omega(xi),y> + sum Omega_j z_j zbar_j; a real periodic family P in "
          "S_{p'}(D(s,r)) (p' = p+1 modified, p_+ otherwise) and eps > 0 with eps >= |X_P|^lambda_{r,D(s,r)}", Q="none",
        C="defines step data and t = 2 tau + 4, c_F = 9 C_1 b_W(tau), c_0 = 16 c_F, M_F = c_F eps/(alpha sigma^{t-1}); in the "
          "modified case t^natural = 2 tau + 5, c^natural_F = 9 C_1 b^natural(tau), c^natural_0 = 16 c^natural_F, C^natural_2 "
          "= 896 + 168 c^natural_F; the smallness condition (bpW:w5:small) eps <= alpha sigma^t eta^2/c_0 (equivalently M_F <= "
          "sigma eta^2/16)", S="c_F, c_0 depend only on tau",
        note="The pointer to Remark bpW:w7:choices (tau = 24 in W6) is a forward pointer; not an edge.",
        deps=[("bpW:w4:melnikov", "L317", "(H_alpha)"), ("bpW:w5:w4-modified", "L318", "the modified hypotheses and b^natural"),
              ("bpW:w5:class", "L320", "the class and the lambda-norm"), ("bpW:w4:lemma1", "L324", "C_1"),
              ("bpW:w4:lattice", "L324", "b_W(tau)"), ("bpW:w5:w4-general", "L316", "(bpW:w5:freq)")]),
    "bpW:w5:solve": dict(
        H="step data (Definition bpW:w5:data); R the Taylor polynomial of Lemma bpW:w5:taylor; F, hat N, hat a_0 of Theorem "
          "bpW:w4:lemma1 for R (through Lemma bpW:w5:w4-general, or bpW:w5:w4-modified)", Q="for all step data",
        C="F in T_{s-sigma} cap S_{p_+}(D(s-sigma,r)), hat N in S_{p_+}(P), both real; R + DN . X_F = hat N + hat a_0 on "
          "D(s-sigma,r); |X_F|^lambda_{r,D(s-sigma,r)} <= M_F, |X_{hat N}|^lambda_{r,D(s,r)} <= 6 eps, |hat omega| + lambda "
          "|hat omega|^L <= 6 pi eps, sup_j (j+2)^{p_+-p}(|hat Omega_j| + lambda|hat Omega_j|^L) <= 3 eps; in the modified case "
          "the Lipschitz parts require 2 beta <= p+1-p_+ and X_F is bounded with c^natural_F, t^natural", S="as in Definition bpW:w5:data",
        deps=[("bpW:w5:data", "L338", "step data"), ("bpW:w5:taylor", "L338", "R"), ("bpW:w4:lemma1", "L339", "F, hat N"),
              ("bpW:w5:w4-general", "L339", "W4 with p_+"), ("bpW:w5:w4-modified", "L340", "modified case"),
              ("stepW:w5:s-in", "L350", PS), ("stepW:w5:s-out", "L352", PS), ("stepW:w5:s-class", "L357", PS)]),
    "stepW:w5:s-in": dict(H="", Q="none", C="R in T_s and |X_R|^lambda <= 3 eps", S="none",
        deps=[("bpW:w5:taylor", "L350", "(i), (iii)")]),
    "stepW:w5:s-out": dict(H="", Q="none", C="|X_F|^lambda <= M_F, |X_{hat N}|^lambda <= 6 eps, the bracket identity",
        S="none", deps=[("bpW:w4:lemma2", "L352", "via Lemma bpW:w5:w4-general"), ("bpW:w5:w4-general", "L352", "W4 with p_+"),
                        ("bpW:w4:lattice", "L354", "(iv)"), ("bpW:w4:lemma1", "L355", "(ii), (iv)"),
                        ("bpW:w4:lie", "L356", "(ii)"), ("stepW:w5:s-in", "L353", "the input bound")]),
    "stepW:w5:s-class": dict(H="", Q="none", C="members of T are C^2 with holomorphic fields into P^{p_+} and DF W = "
        "varpi(X_F,W)", S="none",
        deps=[("bpW:w1:holo-analytic-fd", "L358", "holomorphic in finitely many variables is analytic"),
              ("bpW:w4:taylor", "L360", "the field from the gradients")]),
    "bpW:w5:flow": dict(
        H="step data and (bpW:w5:small); Lemma bpW:w1:flow in (P,|.|_{p,r}) with X = X_{F(xi)}, V = D(s-sigma,r), U = "
          "D(s-2sigma,r/2), delta = sigma/4, M = M_F <= sigma/256 < delta, L = M/delta <= 1/64", Q="for |t| <= 1, xi, zeta in Pi",
        C="the hypotheses of Lemma bpW:w1:flow hold, and (i) phi^t exists on U with values in V, phi^t - id is holomorphic U -> "
          "P^{p_+}, |phi^t - id|^lambda_{p_+,r,U} <= 2 M_F; (ii) on D(s-3sigma,r/4): |D phi^t - I|_{p->p_+,r} <= 8 M_F/sigma and "
          "|D phi^t - I|^lambda <= 16 M_F/sigma <= eta^2; (iii) phi^t(D(s-5sigma,eta r)) subset D(s-4sigma,2 eta r) subset "
          "D(s-3sigma,r/4); (iv) phi^t is real on real points and commutes with integer angle translations", S="none",
        deps=[("bpW:w5:data", "L365", "step data and (bpW:w5:small)"), ("bpW:w1:flow", "L365", "W1's holomorphic flow"),
              ("bpW:w5:solve", "L366", "X_F and M_F"),
              ("stepW:w5:f-margin", "L381", PS), ("stepW:w5:f-flow", "L384", PS), ("stepW:w5:f-par", "L388", PS),
              ("stepW:w5:f-der", "L394", PS), ("stepW:w5:f-image", "L398", PS), ("stepW:w5:f-real", "L400", PS)]),
    "stepW:w5:f-margin": dict(H="", Q="w in U", C="B(w,2 delta) subset V; |X_F|_{p,r} <= M_F on V; M_F <= sigma/1024",
        S="none", deps=[("bpW:w1:kam-domain", "L381", "domain margins"), ("bpW:w5:omega", "L383", "norm comparison"),
                        ("bpW:w5:solve", "L382", "|X_F| <= M_F")]),
    "stepW:w5:f-flow": dict(H="", Q="t", C="(i): the flow and phi^t - id holomorphic into P^{p_+} with norm <= |t| M_F",
        S="none", deps=[("bpW:w1:flow", "L384", "(i)-(iii)"), ("bpW:w1:cauchy", "L387", "uniform derivative bound"),
                        ("bpW:w3:ext-integral", "L387", "differentiation under the integral"), ("stepW:w5:f-margin", "L384", "hypotheses")]),
    "stepW:w5:f-par": dict(H="", Q="xi, zeta", C="|phi^t - id|^lambda <= 2 M_F", S="none",
        deps=[("bpW:w1:flow", "L389", "(iv)"), ("bpW:w1:cauchy", "L392", "|DX_F| <= M_F/delta on B(w,delta)"),
              ("stepW:w5:f-flow", "L390", "the integral identity")]),
    "stepW:w5:f-der": dict(H="", Q="w in D(s-3sigma,r/4)", C="(ii) via Cauchy estimates with margin sigma/8; 16 M_F/sigma "
        "<= eta^2", S="none",
        deps=[("bpW:w1:kam-domain", "L394", "margins"), ("bpW:w1:cauchy", "L396", "the Cauchy estimate"),
              ("stepW:w5:f-flow", "L396", "the bound M_F"), ("stepW:w5:f-par", "L397", "the bound 2 N_1"),
              ("bpW:w5:data", "L397", "(bpW:w5:small)")]),
    "stepW:w5:f-image": dict(H="", Q="w in D(s-5sigma,eta r)", C="(iii) the image inclusions", S="none",
        deps=[("stepW:w5:f-flow", "L398", "the increment bound")]),
    "stepW:w5:f-real": dict(H="", Q="k in Z^2", C="(iv) reality and equivariance", S="none",
        deps=[("bpW:w1:flow", "L400", "(i), (iii)"), ("bpW:w4:lemma1", "L401", "(i) X_F real"),
              ("bpW:w4:taylor", "L401", "1-periodic components")]),
    "bpW:w5:flow-calc": dict(
        H="the setting of Lemma bpW:w5:flow", Q="for |t| <= 1",
        C="(i) (t,w) -> phi^t(w), D phi^t(w) continuous on [-1,1] x U and D phi^t = I + int_0^t DX_F(phi^tau) D phi^tau dtau; "
          "(ii) varpi(D phi^t W, D phi^t W') = varpi(W,W'); (iii) on D(s-3sigma,r/4), D phi^t is invertible on P and maps "
          "P^{p_+} onto P^{p_+}; (iv) if G in S_{p_+}(V') and phi^t(O) subset V' then G o phi^t in S_{p_+}(O) with X_{G o "
          "phi^t} = (phi^t)^* X_G = D(phi^t)^{-1} X_G o phi^t; (v) d/dt G(phi^t w) = DG(phi^t w) X_F(phi^t w), and d/dt "
          "N(phi^t w) = (hat N + hat a_0 - R)(phi^t w)", S="none",
        deps=[("bpW:w5:flow", "L413", "the flow"), ("bpW:w5:class", "L419", "S_{p_+}"),
              ("stepW:w5:c-cont", "L427", PS), ("stepW:w5:c-var", "L431", PS), ("stepW:w5:c-skew", "L434", PS),
              ("stepW:w5:c-symp", "L437", PS), ("stepW:w5:c-inv", "L439", PS), ("stepW:w5:c-trans", "L441", PS),
              ("stepW:w5:c-time", "L445", PS)]),
    "stepW:w5:c-cont": dict(H="", Q="t, w", C="continuity of phi^t and D phi^t (Cauchy integral)", S="none",
        deps=[("bpW:w1:flow", "L428", "(ii)"), ("bpW:w1:ext-unifderiv", "L428", "mean value inequality")]),
    "stepW:w5:c-var": dict(H="", Q="t, w", C="the variational equation", S="none",
        deps=[("bpW:w3:ext-integral", "L432", "differentiation under the integral"), ("stepW:w5:c-cont", "L433", "continuity"),
              ("bpW:w1:deriv-continuous", "L433", "DX_F continuous")]),
    "stepW:w5:c-skew": dict(H="", Q="w, A, B", C="varpi(DX_F A, B) + varpi(A, DX_F B) = 0", S="none",
        deps=[("stepW:w5:s-class", "L434", "F is C^2"), ("bpW:w5:omega", "L436", "antisymmetry")]),
    "stepW:w5:c-symp": dict(H="", Q="t", C="(ii) symplecticity", S="none",
        deps=[("stepW:w5:c-var", "L438", "variational equation"), ("stepW:w5:c-skew", "L438", "skewness"),
              ("bpW:w3:ext-mvt", "L438", "zero derivative")]),
    "stepW:w5:c-inv": dict(H="", Q="w", C="(iii) invertibility by Neumann series", S="none",
        deps=[("bpW:w5:flow", "L439", "(ii) |D phi^t - I| <= 1/8"), ("bpW:w3:ext-neumann", "L440", "Neumann series")]),
    "stepW:w5:c-trans": dict(H="", Q="w, W", C="(iv) the transport formula and holomorphy of the field", S="none",
        deps=[("bpW:w3:symplectic", "L441", "the same argument"), ("stepW:w5:c-symp", "L442", "symplecticity"),
              ("stepW:w5:c-inv", "L442", "invertibility")]),
    "stepW:w5:c-time": dict(H="", Q="w", C="(v) chain rule; N is a continuous quadratic form for p = 1; DN X_F = hat N + "
        "hat a_0 - R", S="none",
        deps=[("bpW:w4:lie", "L447", "(ii)"), ("bpW:w4:lemma1", "L447", "(ii)"), ("bpW:w5#data", "L445", "p = 1")]),
}

DELETE = ["bpW:w5:prep-gap"]

COV = {
    "bpW:w5:prep-gap": ("EXCLUDED", "administrative remark (exponents adopted by W6-W7 after the sourcegap; their values "
                        "are fixed in Definition bpW:w7:constdef and Lemma bpW:w6:prep-step)"),
}

COV.update({
    "w5-kamstep:sourcegap-L226": ("NODE bpW:w5:w4-modified, stepW:w5:m-lip, stepW:w5:m-act", "P96-K p. 140's lambda-norm "
        "for the modified divisors needs 2 beta <= bar p - check p; the blueprint states (ii) under that hypothesis "
        "(Step stepW:w5:m-lip) and handles the action component separately (Step stepW:w5:m-act); W7 adopts beta = 1/4. "
        "Not an open gap of the blueprint", "blueprint-W/parts/w5-kamstep.tex#sourcegap@L226-L238"),
    "w5-kamstep:prose-L7-L11": ("EXCLUDED", "introduction"),
    "w5-kamstep:prose-L13-L25": ("EXCLUDED", "route paragraph (outline)"),
    "w5-kamstep:prose-L27-L33": ("EXCLUDED", "inputs paragraph (pointers; each use is an edge at its consumer)"),
    "w5-kamstep:prose-L35-L39": ("NODE bpW:w5#data", "fixes a = p = 1 for W5"),
    "w5-kamstep:prose-L43-L45": ("EXCLUDED", "introduction of the external list and layout"),
    "w5-kamstep:prose-L57-L58": ("EXCLUDED", "layout"),
    "w5-kamstep:prose-L118-L121": ("EXCLUDED", "motivation of Lemmas bpW:w5:w4-general and bpW:w5:w4-modified"),
})
