# Writer spec for slice W-w4 (blueprint-W/parts/w4-homological.tex, all lines). Wave 2. Rendered by w_depgraph_fill.py.
F = "blueprint-W/parts/w4-homological.tex"
STEP_CONTEXT = True
SYMBOL_EDGES = True
PS = "proof step"
EXT = dict(H="none (Mathlib-level external fact)", Q="as stated in the item", S="none", deps=[])
SD = "Convention bpW:w4:index (a >= 0, p >= 0, bar p = p+1, P96-K normal index j = J-2, wave weights omega_{a,q}(j+2))"
FR = "frequencies omega : Pi -> R^2, Omega : Pi -> R^{N_+} with (bpW:w4:freq) (constants M_0, M_omega, M_Omega; M = M_omega + M_Omega)"
NO_SYMBOL = {"bpW:w4:lemma2": ("bpW:w0:basis#lam",)}

NODES = {
    "bpW:w4:ext-roots": dict(EXT, C="for m in Z, sum_{u=0}^3 i^{um} = 4 if 4 | m and 0 otherwise (finite geometric sum)"),
    "bpW:w4:ext-parallelogram": dict(EXT, C="parallelogram law ||x+y||^2 + ||x-y||^2 = 2||x||^2 + 2||y||^2 in a complex "
        "inner product space"),
    "bpW:w4:ext-exp": dict(EXT, C="e^t >= 1 + t for real t; hence e^{t-1} >= t and x^q e^{-x} <= (q/e)^q for q > 0, x >= 0; "
        "sum_{N>=1} e^{-xN} = 1/(e^x - 1) for x > 0"),
    "bpW:w4:ext-intparts": dict(EXT, C="if g : R -> E (Banach) is C^1 and 1-periodic then int_0^1 g' = 0; continuous linear "
        "maps commute with Bochner integrals"),
    "bpW:w4:index": dict(
        H="typing data: a >= 0, p >= 0", Q="a, p",
        C="convention: bar p = p+1; tangential modes 1,2, normal modes J = j+2 indexed by the P96-K index j >= 1; the space "
          "l^N_{a,q} of (z_j)_{j>=1} with ||z||_{a,q}^2 = sum omega_{a,q}(j+2)^2 |z_j|^2 (wave weights; realized in lp with "
          "the entries J = 1,2 zero); max norm on C^2, |k|_1 on Z^2; the unweighted pairing <x,x'>_0 with (bpW:w4:pairing) "
          "|<x,x'>_0| <= ||x||_{a,q} ||x'||_{a,q'} for q + q' >= 0; z = (u+iv)/sqrt2, zbar = (u-iv)/sqrt2 with "
          "(bpW:w4:zu); period-one angle theta (x = 2 pi theta), strip T_s, domain D(s,r); symplectic form "
          "2 pi sum dtheta ^ dy + sum du ^ dv and Hamilton's equations (bpW:w4:hameq); angular frequencies omega, "
          "nu = omega/(2 pi)", S="none",
        note="The pointer to Lemma bpW:w4:lie(iv) (guard (G)) at L61-L62 and to Remark bpW:w4:weights are forward pointers; not edges.",
        deps=[("bpW:w1:transport", "L69", "weighted coordinates at weight (a,q)"),
              ("bpW:w1:tails", "L70", "the convention for normal-mode sequences (entries J = 1,2 zero)"),
              ("bpW:w0:z", "L86", "the W0 convention z = (q + ip)/sqrt2"),
              ("bpW:w1:kam-space", "L93", "the domain D(s,r) of Definition bpW:w1:kam-space")]),
    "bpW:w4:ops": dict(
        H=SD, Q="none",
        C="defines L (bounded linear maps l^N_{a,p} -> l^N_{a,bar p}, operator norm), matrices M_ij = <M e_j, e_i>_0, "
          "transpose and symmetry; the bilinear norm and the space B of bounded bilinear forms; Lambda : L -> B, Lambda M(z,z') "
          "= <Mz,z'>_0 with ||Lambda M||_bil <= ||M||; the dual norm ||c||_* and the space l^N_*", S="none",
        deps=[("bpW:w4:index", "L118", "the spaces l^N_{a,q}, the pairing and (bpW:w4:pairing)")]),
    "bpW:w4:taylor": dict(
        H=SD + "; s > 0; r > 0 for the field norm", Q="s, r",
        C="defines the class T_s of R = a + <b,y> + <c^+,z>_0 + <c^-,zbar>_0 + <Pz,z>_0 + <Qz,zbar>_0 + <P'zbar,zbar>_0 "
          "(bpW:w4:R) with components a, b, c^+-, P, P', Q, Q^T complex differentiable, 1-periodic and bounded on T_s, P, P' "
          "symmetric; the derivatives R_y, R_theta, R_z, R_zbar, R_u, R_v; the field X_R = (R_y/(2pi), -R_theta/(2pi), R_v, "
          "-R_u) and |X_R|_r; reality; the mean [g] = hat g_0", S="none",
        deps=[("bpW:w4:index", "L139", "the spaces and the coordinates z, zbar, u, v"),
              ("bpW:w4:ops", "L138", "the operator space L")]),
    "bpW:w4:melnikov": dict(
        H=SD + "; Pi subset R^2; " + FR + "; tau >= 0; alpha > 0", Q="Pi, omega, Omega, tau, alpha",
        C="defines (bpW:w4:freq) (Omega_j = j + 2 + tilde Omega_j, sup j|tilde Omega_j| <= M_0, Lipschitz bounds M_omega, "
          "M_Omega), M = M_omega + M_Omega, A_0 = 1, A_k = 1 + |k|_1^tau, |l|, <l> = max(1,|sum j l_j|), the set Z, the "
          "Melnikov conditions (H_alpha) |<k,omega(xi)> + <l,Omega(xi)>| >= alpha <l>/A_k for (k,l) in Z, the divisors "
          "delta^0, delta^+-, delta^P, delta^{P'}, delta^Q and their weights", S="none",
        deps=[("bpW:w4:index", "L158", "the P96-K normal index j")]),
    "bpW:w4:wave": dict(
        H="lambda_J = sqrt(J^2+m); b = (1/lambda_1, 1/lambda_2); omega(xi) = (lambda_1,lambda_2) + A xi, Omega_j(xi) = "
          "lambda_{j+2} + (3/(2 pi lambda_{j+2}))<b,xi> (j >= 1), A of Theorem bpW:w0n:AB", Q="for every Pi subset R^2",
        C="(i) (bpW:w4:freq) holds with M_omega = 9/(8 pi lambda_1^2) + 3/(2 pi lambda_1 lambda_2), M_Omega = (3/(2pi))"
          "(1/lambda_1 + 1/lambda_2), M_0 = m/2 + (3/(2pi)) sup_Pi |<b,xi>|; P96-K Assumption B holds with d = 1, delta = -1, "
          "bar Omega_j = j + 2; (ii) <l> <= <l>^w <= 3<l> for 1 <= |l| <= 2 unless sum l_j = 0 (then equal), so (H_alpha) "
          "with <l>^w implies (H_alpha), and (H_alpha) implies the <l>^w-conditions with alpha/3", S="none",
        deps=[("bpW:w0n:AB", "L187", "the matrix A"), ("bpW:w4:melnikov", "L189", "(bpW:w4:freq) and (H_alpha)"),
              ("stepW:w4:waveLip", "L201", PS), ("stepW:w4:waveTail", "L206", PS), ("stepW:w4:waveIdx", "L210", PS)]),
    "stepW:w4:waveLip": dict(H="", Q="xi, zeta", C="|A(xi - zeta)| <= max row sum |xi - zeta| (the first row); "
        "j|Omega_j(xi) - Omega_j(zeta)| <= (3/(2pi)) |b|_1 |xi - zeta|", S="none",
        deps=[("bpW:w0n:AB", "L203", "A_ii' > 0 and lambda_1 < lambda_2"),
              ("bpW:w0:basis#lambda-facts", "L205", "lambda_{j+2} > j; lambda increasing")]),
    "stepW:w4:waveTail": dict(H="", Q="xi", C="j|tilde Omega_j| <= m/2 + (3/(2pi))|<b,xi>|", S="none",
        deps=[("bpW:w0:basis#lambda-facts", "L208", "0 < lambda_J - J = m/(lambda_J + J) <= m/(2J)"),
              ("bpW:w1:tails", "L209", "the same bound in the wave index")]),
    "stepW:w4:waveIdx": dict(H="", Q="l", C="sum (j+2) l_j = sum j l_j + 2 sum l_j; the ratio lies in [1,3]", S="none", deps=[]),
    "bpW:w4:k0": dict(
        H="the setting of Lemma bpW:w4:wave; alpha_0(m) = 2/sqrt(9+m); xi in R^2 with |<b,xi>| <= 2 pi; 0 < alpha <= alpha_0(m)",
        Q="for all such xi, alpha; every l with 1 <= |l| <= 2",
        C="|<l,Omega(xi)>| >= alpha <l>; i.e. (H_alpha) with k = 0 holds on Pi subset {|<b,xi>| <= 2 pi}", S="alpha_0 depends only on m",
        deps=[("bpW:w4:wave", "L220", "the wave frequencies"), ("bpW:w4:melnikov", "L222", "(H_alpha) and <l>"),
              ("stepW:w4:k0one", "L228", PS), ("stepW:w4:k0diff", "L231", PS)]),
    "stepW:w4:k0one": dict(H="beta = (3/(2pi))<b,xi>, |beta| <= 3; J = j + 2 >= 3", Q="j, i",
        C="Omega_j >= J - 1 = j + 1 > alpha<e_j>; Omega_i + Omega_j >= i + j + 2 > alpha<e_i + e_j>", S="none",
        deps=[("bpW:w0:basis#lambda-facts", "L229", "lambda_J > J >= 3")]),
    "stepW:w4:k0diff": dict(H="beta as above; I = i + 2, J = j + 2", Q="i > j",
        C="Omega_i - Omega_j >= (2/3)(lambda_I - lambda_J) >= alpha_0(m)(i - j) = alpha_0(m)<e_i - e_j>", S="none",
        deps=[("bpW:w0:basis#lambda-facts", "L234", "lambda_K <= K sqrt(1 + m/9) for K >= 3; lambda_I lambda_J > 9")]),
    "bpW:w4:w1-requests": dict(
        H="E complex Banach, s > 0, f : T_s -> E complex differentiable, 1-periodic, ||f|| <= m on T_s; hat f_k", Q="f, k, c_k, s' < s",
        C="(F1) ||hat f_k|| <= m e^{-2 pi |k|_1 s}; (F2) for c_k with sum ||c_k|| e^{2 pi |k|_1 s'} < infinity, g = sum c_k "
          "e^{2 pi i <k,theta>} converges absolutely and uniformly on T_{s'}, is complex differentiable and 1-periodic, "
          "hat g_k = c_k, ||g|| <= sum ||c_k|| e^{2 pi |k|_1 s'}; (F3) (scalar) hat f_k = 0 for all k implies f = 0 on T_s; "
          "(F1) is Lemma bpW:w1:fourier-banach(i), (F2) its (iii), (F3) Lemma bpW:w1:fourier-l2(iii) with H = C", S="none",
        kind="claim",
        note="Remark kept as a node: its items (F1)-(F3) are cited by label (\\ref{bpW:w4:F1}..F3) in the proofs of W4.",
        deps=[("bpW:w1:fourier-banach", "L288", "(F1) is (i), (F2) is (iii)"),
              ("bpW:w1:fourier-l2", "L289", "(F3) is (iii) with H = C")]),
    "bpW:w4:fourier-ops": dict(
        H="f : T_s -> E as in Remark bpW:w4:w1-requests; (iii) f depending on xi in Pi with ||f(theta,xi) - f(theta,zeta)|| <= "
          "m^L |xi - zeta|", Q="for all such f; Lambda; i in {1,2}; xi, zeta",
        C="(i) (Lambda f)^_k = Lambda hat f_k for continuous linear Lambda; (ii) d_{theta_i} f is complex differentiable, "
          "1-periodic and (d_{theta_i} f)^_k = 2 pi i k_i hat f_k; (iii) ||hat f_k(xi) - hat f_k(zeta)|| <= m^L |xi - zeta| "
          "e^{-2 pi |k|_1 s}", S="none",
        deps=[("bpW:w4:w1-requests", "L296", "the setting of f"),
              ("stepW:w4:linimg", "L307", PS), ("stepW:w4:deriv", "L309", PS), ("stepW:w4:fpar", "L315", PS)]),
    "stepW:w4:linimg": dict(H="", Q="none", C="(i): Lambda commutes with the integral defining hat f_k", S="none",
        deps=[("bpW:w4:ext-intparts", "L308", "continuous linear maps commute with Bochner integrals")]),
    "stepW:w4:deriv": dict(H="", Q="i, k", C="(ii): d_{theta_i} f complex differentiable and periodic; (d_{theta_i} f)^_k = "
        "2 pi i k_i hat f_k by periodic integration by parts and Fubini", S="none",
        deps=[("bpW:w1:ext-onevar", "L310", "derivatives of holomorphic maps (in theta_i)"),
              ("bpW:w4:ext-intparts", "L313", "periodic integration by parts"),
              ("bpW:w1:ext-rect", "L314", "Fubini for continuous functions on [0,1]^2")]),
    "stepW:w4:fpar": dict(H="", Q="xi, zeta", C="(iii): (F1) applied to f(.,xi) - f(.,zeta)", S="none",
        deps=[("bpW:w4:w1-requests", "L316", "(F1)")]),
    "bpW:w4:lattice": dict(
        H="sigma > 0; S_q(sigma) = sum_{k in Z^2} |k|_1^q e^{-2 pi |k|_1 sigma} (q >= 0, 0^0 = 1); (iv) tau >= 0, A_k as in "
          "Definition bpW:w4:melnikov, B^W_sigma = sum (1 + |k|_1) A_k^2 e^{-2 pi |k|_1 sigma}", Q="for all sigma > 0, q, tau",
        C="(i) #{k : |k|_1 = N} = 4N; (ii) S_0 = coth(pi sigma)^2 <= (1 + 1/(pi sigma))^2; (iii) S_q <= (4/(pi sigma)) "
          "((q+1)/(e pi sigma))^{q+1} for q > 0; (iv) sum A_k e^{-2 pi|k|_1 sigma} <= B^W_sigma and for 0 < sigma <= 1, "
          "B^W_sigma <= b_W(tau)/sigma^{2tau+3}, b_W(tau) = 2(C_0 + C_1 + C_{2tau} + C_{2tau+1})",
        S="b_W depends only on tau",
        deps=[("bpW:w4:melnikov", "L326", "A_k"), ("stepW:w4:count", "L338", PS), ("stepW:w4:coth", "L341", PS),
              ("stepW:w4:wsum", "L344", PS), ("stepW:w4:bw", "L347", PS)]),
    "stepW:w4:count": dict(H="", Q="N >= 1", C="(i) #{|k|_1 = N} = 4N", S="none", deps=[]),
    "stepW:w4:coth": dict(H="", Q="sigma", C="(ii): the sum factorizes and sum_m e^{-x|m|} = coth(x/2); coth t <= 1 + 1/t",
        S="none", deps=[("bpW:w4:ext-exp", "L343", "geometric sum")]),
    "stepW:w4:wsum": dict(H="", Q="q > 0", C="(iii): S_q = 4 sum N^{q+1} e^{-xN} with the stated bound", S="none",
        deps=[("stepW:w4:count", "L345", "(i)"), ("bpW:w4:ext-exp", "L346", "x^q e^{-x} <= (q/e)^q and the geometric sum")]),
    "stepW:w4:bw": dict(H="", Q="tau, sigma <= 1", C="(iv): the bound on B^W_sigma via S_0, S_1, S_{2tau}, S_{2tau+1}",
        S="b_W depends only on tau",
        deps=[("stepW:w4:coth", "L352", "(ii)"), ("stepW:w4:wsum", "L352", "(iii)")]),
    "bpW:w4:divisors": dict(
        H=SD + "; " + FR + "; (H_alpha)", Q="for every divisor delta with weight w; all xi, zeta in Pi; k in Z^2",
        C="|delta(xi)| >= alpha w/A_k and |1/delta(xi) - 1/delta(zeta)| <= 2(1 + |k|_1) A_k^2 M |xi - zeta|/(alpha^2 w); "
          "w^Q_ij >= |i-j|, w^P_ij >= |i-j| for i != j, all weights >= 1", S="none",
        deps=[("bpW:w4:melnikov", "L362", "(bpW:w4:freq), (H_alpha), divisors and weights"),
              ("stepW:w4:member", "L370", PS), ("stepW:w4:divlip", "L375", PS)]),
    "stepW:w4:member": dict(H="", Q="divisors", C="each divisor is <k,omega> + <l,Omega> with (k,l) in Z and <l> = w; "
        "(H_alpha) gives the lower bound", S="none", deps=[]),
    "stepW:w4:divlip": dict(H="", Q="xi, zeta", C="|delta(xi) - delta(zeta)| <= (|k|_1 + 2) M |xi - zeta|; dividing by "
        "|delta(xi) delta(zeta)| gives the Lipschitz bound", S="none",
        deps=[("stepW:w4:member", "L378", "the lower bound alpha w/A_k")]),
    "bpW:w4:schur": dict(
        H=SD + "; K_S = 1 + pi/sqrt3; d_ij with |d_ij| <= c/|i-j| (i != j), |d_ii| <= c; positive mu, nu; A with weighted "
          "matrix (mu_i A_ij nu_j) bounded on l^2 with norm N_A", Q="for all such d, c, mu, nu, A",
        C="(mu_i d_ij A_ij nu_j) is bounded with norm <= c K_S N_A; (i) H_d : M -> (d_ij M_ij) is bounded L -> L with norm <= "
          "c K_S and H_d(M)^T = H_{d^T}(M^T); (ii) the same on bilinear forms B -> B, Lambda o H_d = H_d o Lambda; (iii) for "
          "diagonal d the bound is c, in particular (i+2)|M_ii| <= ||M|| for M in L", S="none",
        deps=[("bpW:w4:ops", "L394", "L, B, Lambda"),
              ("stepW:w4:schurtr", "L405", PS), ("stepW:w4:schurrep", "L408", PS), ("stepW:w4:schurdiag", "L414", PS)]),
    "stepW:w4:schurtr": dict(H="", Q="none", C="the weighted matrices satisfy the hypotheses of Lemma bpW:w1:schur(iii)",
        S="none", deps=[("bpW:w1:schur", "L406", "(iii)")]),
    "stepW:w4:schurrep": dict(H="", Q="none", C="the weighted matrix of M in L is that of its representative; bounded "
        "weighted matrices are exactly elements of L; the bilinear case via Riesz on l^2", S="none",
        deps=[("bpW:w1:transport", "L410", "the representative tau o M o kappa")]),
    "stepW:w4:schurdiag": dict(H="", Q="none", C="(iii): diagonal multipliers; mu_i nu_i = i + 2", S="none",
        deps=[("bpW:w1:schur", "L415", "(ii)"), ("bpW:w1:multiplier", "L415", "diagonal multipliers")]),
    "bpW:w4:solve": dict(
        H="E, E' complex Banach; 0 < sigma < s; alpha > 0, kappa >= 1, M >= 0; T_k(xi) in L(E,E') with ||T_k(xi)|| <= kappa "
          "A_k/alpha and ||T_k(xi) - T_k(zeta)|| <= 2 kappa (1+|k|_1) A_k^2 M |xi - zeta|/alpha^2; f(.,xi) : T_s -> E complex "
          "differentiable, 1-periodic, ||f|| <= m, ||f(theta,xi) - f(theta,zeta)|| <= m^L |xi - zeta|; S f = sum T_k hat f_k "
          "e^{2 pi i <k,theta>}", Q="for all such data",
        C="(i) the series converges absolutely and uniformly on T_{s-sigma}; S f is complex differentiable, 1-periodic, with "
          "coefficients T_k hat f_k and ||S f|| <= kappa B^W_sigma m/alpha; (ii) ||S f(xi) - S f(zeta)|| <= (kappa B^W_sigma/"
          "alpha)(m^L + 2Mm/alpha)|xi - zeta|; (iii) if d_{theta_i} f is bounded then d_{theta_i} S f = S(d_{theta_i} f); "
          "(iv) S commutes with continuous linear images (Lambda S f, Lambda_1 S f = S'(Lambda_0 f))", S="none",
        deps=[("bpW:w4:lattice", "L431", "B^W_sigma"),
              ("stepW:w4:solvecoef", "L442", PS), ("stepW:w4:solvediff", "L446", PS),
              ("stepW:w4:solvecomm", "L452", PS), ("stepW:w4:solvelin", "L458", PS)]),
    "stepW:w4:solvecoef": dict(H="", Q="k", C="(i): sum ||T_k hat f_k|| e^{2 pi |k|_1 (s-sigma)} <= kappa m B^W_sigma/alpha "
        "and (F2) with s' = s - sigma", S="none",
        deps=[("bpW:w4:w1-requests", "L443", "(F1), (F2)"), ("bpW:w4:lattice", "L445", "(iv)")]),
    "stepW:w4:solvediff": dict(H="", Q="xi, zeta", C="(ii): the coefficient differences are bounded and summed", S="none",
        deps=[("bpW:w4:fourier-ops", "L448", "(iii)"), ("bpW:w4:w1-requests", "L448", "(F1), (F2)"),
              ("bpW:w4:lattice", "L450", "B^W_sigma")]),
    "stepW:w4:solvecomm": dict(H="", Q="i", C="(iii): termwise differentiation gives d_{theta_i} S f = S(d_{theta_i} f)",
        S="none", deps=[("bpW:w4:fourier-ops", "L453", "(ii)"), ("stepW:w4:solvecoef", "L454", "summability"),
                        ("bpW:w1:ext-unifderiv", "L456", "termwise differentiation")]),
    "stepW:w4:solvelin": dict(H="", Q="none", C="(iv): Lambda commutes with absolutely convergent sums", S="none",
        deps=[("bpW:w4:fourier-ops", "L460", "(i)")]),
    "bpW:w4:lie-sec#guard": dict(
        new=True, kind="definition", title="The guard (G) and the weak-bracket setting", stmt=f"{F}#bpW:w4:lie-sec@L469-L478",
        proof=f"{F}#bpW:w4:lie-sec@L469-L478",
        H=SD + "; " + FR, Q="a, p",
        C="defines the formal normal form N = <omega(xi),y> + sum Omega_j z_j zbar_j and the guard (G) gamma_{a,p} = sup_j "
          "(j+2)/omega_{a,p}(j+2)^2 < infinity (bpW:w4:guard); records that the series of N need not converge for a = p = 0, "
          "that (G) holds iff a > 0 or p >= 1/2, and gamma_{1,1} = e^{-6}/3", S="none",
        note="Unlabelled prose L469-L478 with the display label bpW:w4:guard (SPEC section-data rule); consumed by Lemma "
             "bpW:w4:lie(iv) and Theorem bpW:w4:lemma1(ii).",
        deps=[("bpW:w4:index", "L474", "the wave weights omega_{a,p}(j+2)"), ("bpW:w4:melnikov", "L469", "omega, Omega")]),
    "bpW:w4:lie": dict(
        H=SD + "; " + FR + "; F in T_{s'} with components a_F, b_F, c^+-_F, P_F, Q_F, P'_F; L_N F and the weak bracket "
          "<<N,F>> as displayed; (iv) the guard (G)", Q="for (theta,y,z,zbar) in T_{s'} x C^2 x (l^N_{a,p})^2",
        C="(i) Omega z in l^N_{a,p-1} with ||Omega z||_{a,p-1} <= (1+M_0)||z||; L_N F and <<N,F>> are continuous in (z,zbar) "
          "and polynomials of degree <= 2; (ii) <<N,F>> = -L_N F; (iii) on finitely supported z, zbar, L_N F replaces the "
          "k-th coefficient of each component by i delta times it (delta = <k,omega>, delta^+-, delta^P, delta^Q with "
          "delta^Q_{0,jj} = 0, delta^{P'}); (iv) under (G), N_Omega is a continuous bilinear form with |N_Omega| <= "
          "(1+M_0) gamma_{a,p} ||z|| ||zbar||, N is a continuous polynomial, Frechet differentiable, and DN(w) . X_F(w) = "
          "<<N,F>>(w) = -L_N F(w)", S="none",
        deps=[("bpW:w4:taylor", "L481", "the class T_{s'}, components and gradients"),
              ("bpW:w4:lie-sec#guard", "L500", "the guard (G) and N"),
              ("bpW:w4:melnikov", "L481", "(bpW:w4:freq) and the divisors"),
              ("stepW:w4:liebd", "L511", PS), ("stepW:w4:liebr", "L516", PS), ("stepW:w4:liecoef", "L520", PS),
              ("stepW:w4:lieder", "L528", PS)]),
    "stepW:w4:liebd": dict(H="", Q="none", C="|Omega_j| <= (1+M_0)(j+2); the pairings are bounded by (bpW:w4:pairing) with "
        "q = p-1, q' = p+1; continuity in (z,zbar)", S="none",
        deps=[("bpW:w4:index", "L513", "(bpW:w4:pairing)")]),
    "stepW:w4:liebr": dict(H="", Q="none", C="(ii): substitution gives <<N,F>> = -L_N F, an identity of expressions",
        S="none", deps=[]),
    "stepW:w4:liecoef": dict(H="", Q="k", C="(iii): coefficient collection; the k-th coefficient of (1/(2pi))<omega, d_theta "
        "g> is i<k,omega> hat g_k", S="none",
        deps=[("bpW:w4:taylor", "L522", "F_z, F_zbar"), ("bpW:w4:fourier-ops", "L526", "(i), (ii)")]),
    "stepW:w4:lieder": dict(H="", Q="none", C="(iv): under (G) N_Omega is bounded bilinear, N a continuous polynomial with the "
        "displayed derivative; DN . X_F = <<N,F>>", S="none",
        deps=[("bpW:w4:lie-sec#guard", "L529", "(G)"), ("bpW:w1:embed", "L533", "l^N_{a,bar p} subset l^N_{a,p}"),
              ("bpW:w4:index", "L532", "(bpW:w4:hameq): the components of X_F"),
              ("stepW:w4:liebr", "L536", "(ii)")]),
    "bpW:w4:extract": dict(
        H="E complex Banach, rho_1, rho_2 > 0, g(zeta,eta) = sum_{p+q<=2} g_pq zeta^p eta^q with g_pq in E, ||g|| <= K on "
          "|zeta| < rho_1, |eta| < rho_2", Q="for all such data",
        C="||g_pq|| <= K rho_1^{-p} rho_2^{-q} for p + q <= 2; likewise in one variable", S="none",
        deps=[("bpW:w4:ext-roots", "L557", "averages over fourth roots of unity")]),
    "bpW:w4:components": dict(
        H=SD + "; s, r > 0; R in T_s with |X_R(theta,y,z,zbar)|_r <= eps on D(s,r)", Q="for all theta in T_s, i in {1,2}",
        C="(i) |b| <= 2 pi eps, ||c^+-||_{bar p} <= r eps/sqrt2, ||2P||, ||Q||, ||Q^T||, ||2P'|| <= eps; (ii) |d_{theta_i} a| "
          "<= 2 pi r^2 eps, |d_{theta_i} b|_1 <= 2 pi eps, ||d_{theta_i} c^+-||_* <= 2 sqrt2 pi r eps, ||Lambda d_{theta_i} "
          "P||_bil, ||Lambda d_{theta_i} P'||_bil <= 4 pi eps, ||Lambda d_{theta_i} Q||_bil <= 16 pi eps", S="none",
        deps=[("bpW:w4:taylor", "L564", "T_s and |X_R|_r"), ("bpW:w4:ops", "L568", "norms on L, B, l^N_*"),
              ("stepW:w4:testpts", "L576", PS), ("stepW:w4:first", "L582", PS), ("stepW:w4:angle", "L587", PS),
              ("stepW:w4:polar", "L596", PS)]),
    "stepW:w4:testpts": dict(H="", Q="none", C="the test points lie in D(s,r); there |R_y| <= 2 pi eps, |R_theta| <= 2 pi r^2 "
        "eps, ||R_z||, ||R_zbar|| <= r eps/sqrt2", S="none", deps=[("bpW:w4:index", "L577", "(bpW:w4:zu)")]),
    "stepW:w4:first": dict(H="", Q="theta", C="(i) via the polynomial structure and coefficient extraction", S="none",
        deps=[("stepW:w4:testpts", "L584", "bounds at the test points"), ("bpW:w4:extract", "L585", "coefficient extraction")]),
    "stepW:w4:angle": dict(H="", Q="theta, i", C="(ii) for a, b, c^+-, P, Q, P' by coefficient extraction in zeta, eta",
        S="none", deps=[("stepW:w4:testpts", "L589", "bounds at the test points"), ("bpW:w4:extract", "L589", "coefficient extraction")]),
    "stepW:w4:polar": dict(H="", Q="unit z, z'", C="polarization: |beta(z,z')| <= 4 pi eps for symmetric beta = Lambda "
        "d_{theta_i} P", S="none",
        deps=[("stepW:w4:angle", "L599", "the diagonal bound"), ("bpW:w4:ext-parallelogram", "L600", "parallelogram law")]),
    "bpW:w4:lemma1": dict(
        H=SD + "; " + FR + " on Pi subset R^2; tau >= 0; (H_alpha) for some alpha > 0; 0 < sigma < s, r > 0, eps, eps^L >= 0; "
          "for each xi in Pi, R(.,xi) in T_s with |X_{R(xi)}|_r <= eps and |X_{R(xi)} - X_{R(zeta)}|_r <= eps^L |xi - zeta| on "
          "D(s,r); F defined componentwise by division by i delta; hat N = <hat omega,y> + sum hat Omega_j z_j zbar_j, hat "
          "omega = [b], hat Omega_j = ([Q])_jj; C_1 = 7 + 10 K_S, B = B^W_sigma", Q="for every xi in Pi",
        C="(i) F in T_{s-sigma} with hat a_{F,0} = 0, hat b_{F,0} = 0, (hat Q_{F,0})_jj = 0; real if R is real (hat omega in "
          "R^2, hat Omega_j in R); (ii) L_N F + hat N = R - hat a_0, equivalently R + <<N,F>> = hat N + hat a_0, and under (G) "
          "(in particular a = p = 1) R + DN . X_F = hat N + hat a_0; (iii) |X_F|_r <= C_1 B eps/alpha and |X_{F(xi)} - "
          "X_{F(zeta)}|_r <= (C_1 B/alpha)(eps^L + 2M eps/alpha)|xi - zeta| on D(s-sigma,r); (iv) |hat omega| <= 2 pi eps, "
          "sup (j+2)|hat Omega_j| <= eps (likewise for differences), |X_{hat N}|_r <= 2 eps and the Lipschitz analogue on D(s,r)",
        S="C_1 = 7 + 10 K_S < 36 absolute; B = B^W_sigma depends on tau, sigma",
        deps=[("bpW:w4:taylor", "L611", "the class T_s"), ("bpW:w4:melnikov", "L614", "divisors and (H_alpha)"),
              ("bpW:w4:lie", "L624", "L_N and the weak bracket"), ("bpW:w4:lie-sec#guard", "L626", "the guard (G)"),
              ("bpW:w4:lattice", "L620", "B^W_sigma"), ("bpW:w4:schur", "L620", "K_S"),
              ("stepW:w4:divops", "L636", PS), ("stepW:w4:class", "L645", PS), ("stepW:w4:equation", "L650", PS),
              ("stepW:w4:Fcomp", "L660", PS), ("stepW:w4:assembly", "L674", PS), ("stepW:w4:lip", "L687", PS),
              ("stepW:w4:Nhat", "L693", PS), ("stepW:w4:real", "L700", PS)]),
    "stepW:w4:divops": dict(H="", Q="k, xi", C="the division operators T_k satisfy the hypotheses of Lemma bpW:w4:solve with "
        "kappa = 1 (a, b, c^+-) and kappa = K_S (P, Q, Q^T, P')", S="none",
        deps=[("bpW:w4:divisors", "L640", "divisor bounds"), ("bpW:w4:schur", "L642", "Hadamard maps"),
              ("bpW:w1:multiplier", "L643", "diagonal multipliers"), ("bpW:w4:solve", "L643", "its hypotheses")]),
    "stepW:w4:class": dict(H="", Q="none", C="each component of F is S g (in T_{s-sigma}); Q_F^T via H_d(M)^T = H_{d^T}(M^T); "
        "P_F, P'_F symmetric; vanishing coefficients", S="none",
        deps=[("bpW:w4:solve", "L646", "(i)"), ("bpW:w4:schur", "L647", "(i) transpose identity"),
              ("stepW:w4:divops", "L646", "the division operators")]),
    "stepW:w4:equation": dict(H="", Q="y, finitely supported z, zbar", C="(ii): the coefficients of L_N F + hat N - R + hat "
        "a_0 vanish, so it vanishes; extended by continuity and density; second and third forms", S="none",
        deps=[("bpW:w4:solve", "L653", "(iii)"), ("bpW:w4:components", "L653", "(ii)"),
              ("bpW:w4:lie", "L653", "(i)-(iv)"), ("bpW:w4:w1-requests", "L656", "(F3)"),
              ("bpW:w1:space", "L658", "(iii) density of finitely supported sequences"),
              ("stepW:w4:class", "L654", "the components of F"), ("stepW:w4:Nhat", "L657", "hat N continuous")]),
    "stepW:w4:Fcomp": dict(H="", Q="theta in T_{s-sigma}", C="the component bounds of F (values and theta-derivatives)",
        S="C_1 absolute", deps=[("bpW:w4:components", "L661", "the component bounds of R"),
                                ("stepW:w4:divops", "L661", "kappa"), ("bpW:w4:solve", "L661", "(i), (iii), (iv)"),
                                ("bpW:w4:schur", "L669", "(ii) Hadamard maps on B"),
                                ("bpW:w4:index", "L672", "(bpW:w4:pairing): ||c||_* <= ||c||_{bar p}")]),
    "stepW:w4:assembly": dict(H="", Q="(theta,y,z,zbar) in D(s-sigma,r)", C="|X_F|_r <= C_1 B eps/alpha", S="C_1 absolute",
        deps=[("bpW:w4:index", "L675", "(bpW:w4:zu)"), ("stepW:w4:Fcomp", "L676", "the component bounds")]),
    "stepW:w4:lip": dict(H="", Q="xi, zeta", C="(iii) Lipschitz part via R(xi) - R(zeta)", S="none",
        deps=[("bpW:w4:components", "L689", "applied to R(xi) - R(zeta)"), ("bpW:w4:solve", "L690", "(ii)"),
              ("stepW:w4:assembly", "L691", "linear assembly"), ("stepW:w4:Fcomp", "L689", "the inputs")]),
    "stepW:w4:Nhat": dict(H="", Q="none", C="(iv): bounds on hat omega, hat Omega and X_{hat N}", S="none",
        deps=[("bpW:w4:components", "L694", "|b| <= 2 pi eps, ||Q|| <= eps"), ("bpW:w4:schur", "L695", "(iii)")]),
    "stepW:w4:real": dict(H="", Q="real xi", C="the reality relations pass to F and hat N", S="none",
        deps=[("bpW:w4:taylor", "L701", "reality of R"), ("stepW:w4:class", "L705", "the coefficients of F")]),
    "bpW:w4:lemma2": dict(
        H="the setting of Theorem bpW:w4:lemma1 with M > 0; 0 <= lambda <= alpha/M; |X|^lambda = eps_X + lambda eps_X^L",
        Q="for all such lambda",
        C="|X_{hat N}|^lambda_{r,D(s,r)} <= 2 |X_R|^lambda_{r,D(s,r)}, |X_F|^lambda_{r,D(s-sigma,r)} <= (3 C_1 B^W_sigma/alpha)"
          " |X_R|^lambda_{r,D(s,r)}, and for 0 < sigma <= 1, B^W_sigma <= b_W(tau) sigma^{-(2tau+3)} (P96-K (4), b = b_W(tau)); "
          "3 C_1 < 108 replaces P96-K's absolute a", S="3 C_1 absolute; b_W depends only on tau",
        note="lambda here is the P96-K weighting parameter, not the frequency lambda_j (no lam edge).",
        deps=[("bpW:w4:lemma1", "L733", "(iii), (iv)"), ("bpW:w4:lattice", "L734", "(iv)")]),
    "bpW:w4:from-w3": dict(
        kind="claim",
        H="the Birkhoff coordinates of Theorem bpW:w3:main; " + SD, Q="none",
        C="z_j = w_{j+2}, zbar_j = w_{-(j+2)}, on real points u_j = q_{j+2}, v_j = p_{j+2}; ||hat w||^2 = ||z||^2 + ||zbar||^2 "
          "= ||u||^2 + ||v||^2 with the wave weights; (b) ||hat w|| <= ||u|| + ||v|| <= sqrt2 ||hat w||; (c) the smoothing "
          "class of W3 gives normal gradients in l^N_{a,bar p}; (d) Omega restricted to the normal part is sum du ^ dv and "
          "dz = -i H_zbar agrees with X_P(w)_l = -i sgn(l) DP(w) e_{-l}; ownership ruling: W5 owns the action-angle "
          "substitution, the domain check and the norm comparisons",
        S="none",
        note="Remark kept as a node: its identifications are consumed by W5 (action-angle substitution); the ownership "
             "ruling and the pointer to Remark bpW:w3:interface are administrative.",
        deps=[("bpW:w3:main", "L775", "the Birkhoff map"), ("bpW:w3:space", "L776", "the coordinates w_l"),
              ("bpW:w3:coords", "L777", "u_j = q_{j+2}, v_j = p_{j+2}"), ("bpW:w4:index", "L779", "the wave weights"),
              ("bpW:w3:omega", "L782", "the symplectic form"), ("bpW:w3:hamfield-def", "L783", "X_P")]),
}

DELETE = ["bpW:w4:weights", "bpW:w4:melnikov-check", "bpW:w4:counterexample", "bpW:w4:compare", "bpW:w4:to-w5"]

COV = {
    "bpW:w4:weights": ("EXCLUDED", "administrative remark (why the wave weights are kept)"),
    "bpW:w4:melnikov-check": ("EXCLUDED", "administrative remark (summary of what is checked about the Melnikov conditions)"),
    "bpW:w4:counterexample": ("EXCLUDED", "administrative remark (counterexample to P96-K p. 127's operator-valued "
                              "square-sum bound; errata); no proof consumes it"),
    "bpW:w4:compare": ("EXCLUDED", "administrative remark (comparison of constants with P96-K)"),
    "bpW:w4:to-w5": ("EXCLUDED", "administrative remark (what W5 receives and must supply); pointer"),
    "w4-homological:sourcegap-L716": ("NODE stepW:w4:Fcomp, stepW:w4:assembly", "P96-K p. 128 omits the bookkeeping of "
                                      "the other components and of the y-component; the blueprint supplies it",
                                      "blueprint-W/parts/w4-homological.tex#sourcegap@L716-L719"),
    "w4-homological:prose-L3-L7": ("EXCLUDED", "introduction"),
    "w4-homological:prose-L9-L21": ("EXCLUDED", "route paragraph (outline)"),
    "w4-homological:prose-L23-L30": ("EXCLUDED", "inputs paragraph (pointers; each use is an edge at its consumer)"),
    "w4-homological:prose-L32-L36": ("EXCLUDED", "regularity remark (outline)"),
    "w4-homological:prose-L40-L42": ("EXCLUDED", "introduction of the external list"),
    "w4-homological:prose-L53-L55": ("EXCLUDED", "derivation note for an external item (W4-E3); layout"),
    "w4-homological:prose-L469-L478": ("NODE bpW:w4:lie-sec#guard", "the formal N and the guard (G)"),
    "w4-homological:prose-L813-L819": ("EXCLUDED", "ledger (administrative)"),
    "w4-homological:prose-L821-L824": ("EXCLUDED", "ledger (administrative)"),
    "w4-homological:prose-L826-L831": ("EXCLUDED", "ledger of suspected P96-K errata (administrative)"),
}
