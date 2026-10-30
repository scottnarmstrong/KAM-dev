# Writer spec for slice W-w2 (blueprint-W/parts/w2-reconstruction.tex, all lines). Rendered by w_depgraph_fill.py.
F = "blueprint-W/parts/w2-reconstruction.tex"
STEP_CONTEXT = True
SYMBOL_EDGES = True

EXT = dict(H="none (Mathlib-level external fact)", Q="as stated in the item", S="none", deps=[])

NODES = {
    "bpW:w2:ext-deriv": dict(EXT, C="a continuous linear map composed with a curve differentiable at t is "
        "differentiable at t with the image derivative; d/ds <Psi(s),y> = <Psi'(s),y>; derivatives are unique; "
        "translation: if F has derivative d at 0 then s -> F(s-t) has derivative d at t; a two-sided derivative is a "
        "derivative within any set; on [0,pi] (pi > 0) derivatives within are unique, so derivWithin f (Icc 0 pi) x "
        "equals any f' with HasDerivWithinAt f f' (Icc 0 pi) x"),
    "bpW:w2:ext-an": dict(EXT, C="the projections of R x R and the affine maps t -> theta_0 + t nu are analytic; sums, "
        "products and powers of real analytic functions are analytic; analytic maps are differentiable and continuous; "
        "continuity at every point of a set gives ContinuousOn"),
    "bpW:w2:ext-sums": dict(EXT, C="tsum_congr (termwise equal series have equal tsum, no summability needed); "
        "Summable.tsum_sub, Summable.tsum_add, tsum_mul_left for summable series; tsum_zero; comparison; summability of "
        "j e^{-j}, e^{-j} (geometric); Cauchy-Schwarz ¦<Psi,y>¦ <= ||Psi|| ||y||; on a product norm_fst_le, norm_snd_le"),
    "bpW:w2:ext-trig": dict(EXT, C="sin 0 = 0, sin(n pi) = 0 for n in N; ¦sin¦, ¦cos¦ <= 1; d/dx sin(jx) = j cos(jx), "
        "d/dx cos(jx) = -j sin(jx); sqrt(lambda) sqrt(lambda) = lambda and lambda/sqrt(lambda) = sqrt(lambda) for "
        "lambda > 0; lambda_j^2 = j^2 + m"),
    "bpW:w2:derived": dict(
        H="typing data: y in l^2_R, x in R (standing data a = p = 1, kappa = kappa_{1,1})", Q="y, x",
        C="defines D^0 y(x) = U_m(y)(x) (frozen reconU m hm y x), D^1 y(x) = sum_j kappa(y)_j/sqrt(lambda_j) sqrt(2/pi) "
          "j cos(jx), D^2 y(x) = -sum_j kappa(y)_j/sqrt(lambda_j) sqrt(2/pi) j^2 sin(jx) as tsums over N_+ (non-frozen "
          "helpers)", S="none",
        deps=[("bpW:w0:ellap#coeff", "L72", "kappa(y)_j = coeff y j")]),
    "bpW:w2:functionals": dict(
        H="standing data (m > 0, a = p = 1); c_0 = sqrt(2/pi) (e^2-1)^{-1/2}", Q="there exist Psi^0, Psi^1, Psi^2, Psi^V; "
        "then for all y in l^2_R and x in R",
        C="there are real analytic Psi^0, Psi^1, Psi^2, Psi^V : R -> l^2_R (AnalyticOnNhd R Psi univ) such that (i) "
          "D^k y(x) = <Psi^k(x),y> (k = 0,1,2) and V_m(y)(x) = <Psi^V(x),y>, the four series absolutely convergent; (ii) "
          "||Psi^0(x)||, ||Psi^1(x)|| <= c_0, ||Psi^V(x)|| <= (1+m)^{1/4} c_0, hence ¦D^0y(x)¦, ¦D^1y(x)¦ <= c_0 ||y|| "
          "and ¦V_m(y)(x)¦ <= (1+m)^{1/4} c_0 ||y||; (iii) D^k y has derivative D^{k+1} y(x) at x (k = 0,1); (iv) "
          "D^0 y(0) = D^0 y(pi) = 0", S="c_0 absolute; Psi^k independent of y and x",
        deps=[("bpW:w2:derived", "L85", "D^k y"),
              ("stepW:w2:features", "L95", "proof step"), ("stepW:w2:pairing", "L103", "proof step"),
              ("stepW:w2:norms", "L108", "proof step"), ("stepW:w2:xder", "L114", "proof step"),
              ("stepW:w2:bdry", "L120", "proof step")]),
    "stepW:w2:features": dict(
        H="", Q="none", C="Lemma bpW:w1:sine-feature with a = p = 1 applies to beta_j = lambda_j^{-1/2} (B = 1, nu = 0) "
        "and beta_j = lambda_j^{1/2} (B = (1+m)^{1/4}, nu = 1/2); the real restrictions Psi^k, Psi^V are real analytic "
        "with coordinates Psi^k(x)_j = lambda_j^{-1/2} phi_j^(k)(x)/omega(j), Psi^V(x)_j = lambda_j^{1/2} phi_j(x)/omega(j)",
        S="none",
        deps=[("bpW:w1:sine-feature", "L96", "with a = p = 1 and the two choices of beta; (ii) real analyticity"),
              ("bpW:w0:basis#lambda-facts", "L97", "lambda_j > j >= 1"),
              ("bpW:w0:mass", "L98", "lambda_j^2 = j^2 + m <= (1+m) j^2")]),
    "stepW:w2:pairing": dict(
        H="", Q="y, x", C="<Psi^k(x),y> and <Psi^V(x),y> equal termwise the summands of reconU, of D^1, D^2 and of "
        "reconV, so the tsums agree; this is (i)", S="none",
        deps=[("bpW:w1:sine-feature", "L104", "(iii): the pairings as absolutely convergent series"),
              ("stepW:w2:features", "L104", "the feature maps Psi^k, Psi^V"),
              ("bpW:w2:derived", "L106", "the summands of D^1, D^2"),
              ("bpW:w2:ext-sums", "L107", "tsum_congr")]),
    "stepW:w2:norms": dict(
        H="", Q="x", C="||Psi^k(x)||^2 <= (2/pi) sum_j lambda_j^{-1} j^{2k-2} e^{-2j} <= c_0^2 for k = 0,1, and "
        "||Psi^V(x)||^2 <= (1+m)^{1/2} c_0^2; with Cauchy-Schwarz this gives (ii)", S="c_0 absolute",
        deps=[("stepW:w2:features", "L109", "the coordinates of Psi^k, Psi^V"),
              ("bpW:w0:basis#lambda-facts", "L110", "lambda_j^{-1} < 1 and lambda_j j^{-2} <= (1+m)^{1/2} j^{-1}"),
              ("bpW:w1:ext-lp", "L113", "norm bounds from finite partial sums"),
              ("bpW:w2:ext-sums", "L113", "Cauchy-Schwarz"),
              ("stepW:w2:pairing", "L113", "(i) for the pointwise bounds")]),
    "stepW:w2:xder": dict(
        H="", Q="x, y", C="(Psi^k)'(x) = Psi^{k+1}(x) for k = 0,1, and x -> <Psi^k(x),y> has derivative <Psi^{k+1}(x),y>; "
        "with (i) this is (iii)", S="none",
        deps=[("stepW:w1:recder", "L115", "the derivative of the analytic feature map has the coordinatewise derivatives"),
              ("bpW:w2:ext-trig", "L116", "derivatives of sin(jx), cos(jx)"),
              ("bpW:w2:ext-deriv", "L119", "derivative of the pairing with fixed y"),
              ("stepW:w2:pairing", "L119", "(i)")]),
    "stepW:w2:bdry": dict(
        H="", Q="y", C="phi_j(0) = phi_j(pi) = 0 for j in N_+, so every summand of reconU m hm y 0 and reconU m hm y pi "
        "vanishes and the tsum is 0; this is (iv)", S="none",
        deps=[("bpW:w2:ext-trig", "L121", "sin 0 = 0, sin(j pi) = 0"),
              ("bpW:w2:ext-sums", "L123", "tsum_zero")]),
    "bpW:w2:force": dict(
        H="standing data; y in l^2_R; Sigma_lin(x) = sum_j sqrt(lambda_j) lambda_j kappa(y)_j phi_j(x), Sigma_cub(x) = "
          "sum_j sqrt(lambda_j) G(y)_j phi_j(x) with G(y)_j = cubicGrad m hm y j",
        Q="for all y; for every x in R (convergence, (i)); for every x in [0,pi] ((ii))",
        C="both series converge absolutely; (i) Sigma_lin(x) = -D^2 y(x) + m D^0 y(x) for every x in R; (ii) "
          "Sigma_cub(x) = U_m(y)(x)^3 for every x in [0,pi]", S="none",
        deps=[("bpW:w2:derived", "L134", "D^0 y and D^2 y"),
              ("stepW:w2:fsum", "L140", "proof step"), ("stepW:w2:flin", "L148", "proof step"),
              ("stepW:w2:fcub", "L154", "proof step")]),
    "stepW:w2:fsum": dict(
        H="", Q="y, x", C="the summands of Sigma_lin are at most sqrt(2/pi)(1+m)^{3/4} ||y|| j e^{-j}, those of Sigma_cub "
        "at most sqrt(2/pi)(1+m)^{1/4} ||G^w(y)|| e^{-j}; both majorants are summable; D^0 y(x), D^2 y(x) converge "
        "absolutely", S="none",
        deps=[("bpW:w1:ext-lp", "L141", "¦kappa(y)_j¦ <= ||y||/(j e^j)"),
              ("bpW:w0:basis#lambda-facts", "L141", "sqrt(lambda_j) lambda_j <= (1+m)^{3/4} j^{3/2}"),
              ("bpW:w1:cubic-analytic", "L143", "(iv): G(y)_j = G^w(y)_j/omega_{1,2}(j), G^w(y) in l^2_R"),
              ("bpW:w2:ext-sums", "L146", "comparison and summability of the majorants"),
              ("bpW:w2:functionals", "L147", "(i): absolute convergence of D^0 y(x), D^2 y(x)")]),
    "stepW:w2:flin": dict(
        H="", Q="y, x", C="termwise sqrt(lambda_j) lambda_j = (j^2+m)/sqrt(lambda_j), so the j-th summand of Sigma_lin is "
        "minus that of D^2 y plus m times that of D^0 y; summing gives (i)", S="none",
        deps=[("bpW:w2:ext-trig", "L149", "lambda/sqrt(lambda) identities and lambda_j^2 = j^2 + m"),
              ("bpW:w2:derived", "L151", "the summands of D^0, D^2"),
              ("stepW:w2:fsum", "L151", "absolute convergence of both series"),
              ("bpW:w2:ext-sums", "L152", "Summable.tsum_add, tsum_mul_left")]),
    "stepW:w2:fcub": dict(
        H="", Q="y, x in [0,pi]", C="U_m(y) = U_m(q) and G(y) = G_q(q) for q = kappa(y) in l^{1,1}; the first identity of "
        "(bpW:w0n:force) gives U_m(q)^3 = sum_l sqrt(lambda_l) G_q(q)_l phi_l on [0,pi], which is (ii)", S="none",
        deps=[("stepW:w1:trifrozen", "L155", "the frozen reconU and cubicGrad are U_m and G_q of q = kappa(y)"),
              ("stepW:w0n:force", "L157", "the force identity U_m(q)^3 = sum sqrt(lambda_l) G_q(q)_l phi_l")]),
    "bpW:w2:coeffsol": dict(
        H="typing data: Y : R -> WaveSpace (standing data)", Q="Y",
        C="defines: Y is an analytic coefficient solution iff (C1) Y is real analytic at every t (forall t, AnalyticAt R "
          "Y t) and (C2) for all t and j in N_+, s -> coeff (Y s).1 j has derivative lambda_j coeff (Y t).2 j at t and "
          "s -> coeff (Y s).2 j has derivative -lambda_j coeff (Y t).1 j - cubicGrad m hm (Y t).1 j at t (HasDerivAt)",
        S="none",
        deps=[("bpW:w0:eqmotion", "L176", "(C2) is the coefficient system (bpW:w0:coeffsys) read coordinatewise")]),
    "bpW:w2:orbit": dict(
        H="K : (Fin 2 -> R) -> WaveSpace with AnalyticOnNhd R K univ; nu : Fin 2 -> R such that for all theta and j in "
          "N_+ the invariance (bpW:w2:inv) holds, each as a HasDerivAt at 0 of t -> coeff (K(theta + t nu)).i j (the "
          "frozen conclusion (4) of nlw2 for one I)", Q="for all K, nu as stated; for every theta_0",
        C="Y(t) = K(theta_0 + t nu) is an analytic coefficient solution", S="none",
        deps=[("bpW:w2:coeffsol", "L189", "the notion of analytic coefficient solution"),
              ("stepW:w2:oan", "L193", "proof step"), ("stepW:w2:oshift", "L196", "proof step")]),
    "stepW:w2:oan": dict(
        H="", Q="t", C="t -> theta_0 + t nu is analytic and K is analytic at its value, so Y is analytic at t ((C1))",
        S="none", deps=[("bpW:w2:ext-an", "L195", "affine maps are analytic; AnalyticAt.comp")]),
    "stepW:w2:oshift": dict(
        H="", Q="t, j", C="applying (bpW:w2:inv) at theta = theta_0 + t nu and translating, s -> coeff (Y s).i j has the "
        "derivative required by (C2) at t", S="none",
        deps=[("bpW:w2:ext-deriv", "L198", "the translation rule for derivatives")]),
    "bpW:w2:curve-deriv": dict(
        H="Y an analytic coefficient solution; t in R", Q="for all Y, t; j in N_+",
        C="Y_1 = (Y .).1 and Y_2 = (Y .).2 are differentiable at t as maps R -> l^2_R and, with Y_i'(t) their "
          "derivatives, kappa(Y_1'(t))_j = lambda_j kappa(Y_2(t))_j and kappa(Y_2'(t))_j = -lambda_j kappa(Y_1(t))_j - "
          "G(Y_1(t))_j", S="none",
        deps=[("bpW:w2:coeffsol", "L207", "analytic coefficient solution"),
              ("stepW:w2:cdiff", "L213", "proof step"), ("stepW:w2:ccoord", "L216", "proof step")]),
    "stepW:w2:cdiff": dict(
        H="", Q="t", C="Y_i is analytic at t (composite with the continuous linear projection), hence differentiable",
        S="none", deps=[("bpW:w2:ext-an", "L215", "analytic maps are differentiable")]),
    "stepW:w2:ccoord": dict(
        H="", Q="t, j", C="s -> kappa(Y_i(s))_j has derivative kappa(Y_i'(t))_j and, by (C2), the derivative stated "
        "there; uniqueness gives the identities", S="none",
        deps=[("bpW:w1:coordinatewise", "L217", "with (a,p) = (a',p') = (1,1), hat iota = id, v = Y_i'(t)"),
              ("stepW:w2:cdiff", "L217", "Y_i differentiable at t"),
              ("bpW:w2:ext-deriv", "L219", "uniqueness of derivatives")]),
    "bpW:w2:curve": dict(
        H="Y an analytic coefficient solution; u(t,x) = U_m(Y_1(t))(x), u_t(t,x) = V_m(Y_2(t))(x), u_x = D^1 Y_1(t)(x), "
          "u_xx = D^2 Y_1(t)(x), u_tt = u_xx - m u - u^3; M_m = c_0(2 + (1+m)^{1/4})",
        Q="for all Y; (ii), (iv) for all t, x in R; (iii), (vi) for all t in R, x in [0,pi]",
        C="(i) each of the five functions, uncurried, is real analytic at every point of R x R; (ii) s -> u(s,x) has "
          "derivative u_t(t,x) at t; (iii) for x in [0,pi], s -> u_t(s,x) has derivative u_tt(t,x) at t; (iv) u(t,.) has "
          "derivative u_x(t,x) and u_x(t,.) has derivative u_xx(t,x) at x; (v) IsClassicalSolution m hm u with witnesses "
          "(u_t,u_x,u_tt,u_xx); (vi) for x in [0,pi], derivWithin (u t) (Icc 0 pi) x = u_x(t,x) and ¦u(t,x)¦ + "
          "¦derivWithin (u t) (Icc 0 pi) x¦ + ¦V_m(Y_2(t))(x)¦ <= M_m ||Y(t)||", S="M_m depends only on m",
        deps=[("bpW:w2:coeffsol", "L234", "analytic coefficient solution"),
              ("bpW:w2:derived", "L236", "u_x = D^1 Y_1(t), u_xx = D^2 Y_1(t)"),
              ("bpW:w2:functionals", "L238", "c_0"),
              ("stepW:w2:joint", "L252", "proof step"), ("stepW:w2:t1", "L263", "proof step"),
              ("stepW:w2:t2", "L271", "proof step"), ("stepW:w2:x", "L279", "proof step"),
              ("stepW:w2:frozen", "L281", "proof step"), ("stepW:w2:bound", "L290", "proof step")]),
    "stepW:w2:joint": dict(
        H="", Q="(s_0,x_0) in R^2", C="(s,x) -> <Psi(x),Y_i(s)> are real analytic at every point; by (i) of Lemma "
        "bpW:w2:functionals these are u, u_x, u_xx, u_t; u_tt is a polynomial in u, u_xx; this is (i)", S="none",
        deps=[("stepW:w2:cdiff", "L253", "Y_1, Y_2 analytic at every t"),
              ("bpW:w1:recon-analytic", "L253", "(iii) with parameter domain R"),
              ("bpW:w2:ext-an", "L257", "pairs, projections and polynomials of analytic maps"),
              ("bpW:w1:ext-analytic", "L259", "the continuous bilinear inner product is analytic"),
              ("bpW:w2:functionals", "L259", "(i): the functions are the pairings")]),
    "stepW:w2:t1": dict(
        H="", Q="t, x", C="s -> u(s,x) has derivative <Psi^0(x),Y_1'(t)> = U_m(Y_1'(t))(x) = V_m(Y_2(t))(x) = u_t(t,x); "
        "this is (ii)", S="none",
        deps=[("bpW:w2:functionals", "L265", "(i): D^0 y(x) = <Psi^0(x),y> continuous linear in y"),
              ("bpW:w2:ext-deriv", "L266", "derivative of a continuous linear image of a curve"),
              ("bpW:w2:curve-deriv", "L267", "kappa(Y_1'(t))_j = lambda_j kappa(Y_2(t))_j"),
              ("bpW:w2:ext-trig", "L267", "lambda/sqrt(lambda) = sqrt(lambda)"),
              ("bpW:w2:ext-sums", "L270", "tsum_congr")]),
    "stepW:w2:t2": dict(
        H="", Q="t, x in [0,pi]", C="s -> u_t(s,x) has derivative V_m(Y_2'(t))(x) = -Sigma_lin(x) - Sigma_cub(x) = "
        "u_tt(t,x) for x in [0,pi]; this is (iii)", S="none",
        deps=[("bpW:w2:functionals", "L272", "(i): V_m(y)(x) = <Psi^V(x),y>"),
              ("bpW:w2:ext-deriv", "L272", "derivative of a continuous linear image of a curve"),
              ("bpW:w2:curve-deriv", "L273", "the coordinates of Y_2'(t)"),
              ("stepW:w2:fsum", "L275", "absolute convergence of Sigma_lin, Sigma_cub with y = Y_1(t)"),
              ("bpW:w2:ext-sums", "L276", "Summable.tsum_sub"),
              ("bpW:w2:force", "L277", "(i), (ii) on [0,pi]")]),
    "stepW:w2:x": dict(
        H="", Q="t, x", C="(iv) is (iii) of Lemma bpW:w2:functionals with y = Y_1(t)", S="none",
        deps=[("bpW:w2:functionals", "L280", "(iii)")]),
    "stepW:w2:frozen": dict(
        H="", Q="t, x in [0,pi]", C="unfolding IsClassicalSolution m hm u with witnesses (u_t,u_x,u_tt,u_xx): continuity on "
        "univ x Icc 0 pi from (i), the two time derivatives from (ii), (iii), the two x-derivatives within [0,pi] from "
        "(iv), the equation by definition of u_tt, the boundary values from (iv) of Lemma bpW:w2:functionals; this is (v)",
        S="none",
        deps=[("stepW:w2:joint", "L283", "(i): analyticity, hence continuity"),
              ("bpW:w2:ext-an", "L283", "analytic implies continuous; ContinuousOn"),
              ("stepW:w2:t1", "L286", "(ii)"), ("stepW:w2:t2", "L286", "(iii)"),
              ("stepW:w2:x", "L287", "(iv)"),
              ("bpW:w2:ext-deriv", "L287", "HasDerivAt.hasDerivWithinAt"),
              ("bpW:w2:functionals", "L289", "(iv): boundary values")]),
    "stepW:w2:bound": dict(
        H="", Q="t, x in [0,pi]", C="derivWithin (u t) (Icc 0 pi) x = u_x(t,x) (endpoints included) and ¦u¦ + ¦u_x¦ + "
        "¦V_m(Y_2(t))(x)¦ <= M_m ||Y(t)||; this is (vi)", S="M_m depends only on m",
        deps=[("stepW:w2:frozen", "L291", "the derivative within [0,pi]"),
              ("bpW:w2:ext-deriv", "L292", "uniqueness of derivatives within [0,pi]"),
              ("bpW:w2:functionals", "L293", "(ii): the pointwise bounds"),
              ("bpW:w2:ext-sums", "L295", "norm_fst_le, norm_snd_le")]),
    "bpW:w2:main": dict(
        H="m > 0; M_m as in Theorem bpW:w2:curve; K : (Fin 2 -> R) -> WaveSpace, nu : Fin 2 -> R, B in R with (H1) "
          "IsAnalyticTorusEmbedding K, (H2) the invariance (bpW:w2:inv) for every theta and j in N_+, (H3) ||K(theta)|| "
          "<= B for every theta",
        Q="for all m > 0, K, nu, B as stated; for every theta_0; (a) for every z in univ x Icc 0 pi; (c), (d) for all t "
          "in R, x in [0,pi]",
        C="with u(t,x) = reconU m hm (K(theta_0 + t nu)).1 x: (a) AnalyticAt R (z -> reconU m hm (K(theta_0 + z.1 nu)).1 "
          "z.2) z; (b) IsClassicalSolution m hm u; (c) HasDerivAt (s -> reconU m hm (K(theta_0 + s nu)).1 x) (reconV m hm "
          "(K(theta_0 + t nu)).2 x) t; (d) ¦u(t,x)¦ + ¦derivWithin (u t) (Icc 0 pi) x¦ + ¦V_m(K(theta_0 + t nu).2)(x)¦ "
          "<= M_m B", S="M_m depends only on m",
        deps=[("bpW:w2:curve", "L304", "M_m"),
              ("bpW:w2:orbit", "L308", "(H2) is its invariance hypothesis (bpW:w2:inv)"),
              ("stepW:w2:mred", "L324", "proof step"), ("stepW:w2:mconc", "L328", "proof step")]),
    "stepW:w2:mred": dict(
        H="", Q="theta_0", C="from the analyticity conjunct of (H1) and (H2), Y(t) = K(theta_0 + t nu) is an analytic "
        "coefficient solution, and the u of the two theorems coincide", S="none",
        deps=[("bpW:w2:orbit", "L326", "torus orbits are analytic coefficient solutions")]),
    "stepW:w2:mconc": dict(
        H="", Q="theta_0", C="(a) is (i) of Theorem bpW:w2:curve restricted to R x [0,pi]; (b) is (v); (c) is (ii) "
        "restricted to [0,pi]; (d) is (vi) with ||Y(t)|| <= B by (H3) and M_m > 0", S="M_m depends only on m",
        deps=[("bpW:w2:curve", "L329", "(i), (ii), (v), (vi)"),
              ("stepW:w2:mred", "L329", "Y is an analytic coefficient solution")]),
    "bpW:w2:clause5": dict(
        H="m > 0, C_3 > 0, Gamma subset Fin 2 -> R, nu : (Fin 2 -> R) -> Fin 2 -> R, K : (Fin 2 -> R) -> (Fin 2 -> R) -> "
          "WaveSpace; for every I in Gamma: K_I satisfies IsAnalyticTorusEmbedding, ||K_I(theta)|| <= C_3 sqrt(I_0+I_1) "
          "for all theta, and the invariance (4) of nlw2 holds; C = max(1,M_m) C_3",
        Q="for all such m, C_3, Gamma, nu, K",
        C="C > 0, C >= C_3, ||K_I(theta)|| <= C sqrt(I_0+I_1), and conclusion (5) of nlw2 holds verbatim with this C",
        S="C depends only on m and C_3 (C = max(1,M_m) C_3)",
        note="Consumer: the W8 assembly (later wave) for the root bpW:wh:nlw2. The statement speaks of the form of "
             "conclusions (4)-(5) of nlw2; that is not a use of the root.",
        deps=[("bpW:w2:main", "L358", "applied with K = K_I, nu = nu(I), B = C_3 sqrt(I_0+I_1)"),
              ("bpW:w2:curve", "L351", "the constant M_m"),
              ("bpW:w0:basis#lam", "L351", "(4) of nlw2 involves lambda_j"),
              ("bpW:w0:Gq#cubicGrad", "L351", "(4) of nlw2 involves cubicGrad"),
              ("bpW:w0:ellap#coeff", "L351", "(4) of nlw2 involves coeff"),
              ("bpW:w0:reconstruction#reconU", "L352", "(5) of nlw2 involves reconU"),
              ("bpW:w0:reconstruction#reconV", "L352", "(5) of nlw2 involves reconV"),
              ("bpW:w0:nlw#IsClassicalSolution", "L352", "(5) of nlw2 involves IsClassicalSolution")]),
}

DELETE = ["bpW:w2:hidden", "bpW:w2:hyp", "bpW:w2:constants"]

COV = {
    "bpW:w2:hidden": ("EXCLUDED", "administrative remark (regularity hidden in the hypotheses; the proofs use only the "
                      "coordinate form); no proof consumes it"),
    "bpW:w2:hyp": ("EXCLUDED", "administrative remark (how W8 supplies (H1)-(H3); Lean statement may weaken (H1)); "
                   "re-examine when W8 is added"),
    "bpW:w2:constants": ("EXCLUDED", "administrative remark (order of constants; the value of M_m); the constant "
                         "choice is Corollary bpW:w2:clause5"),
}

COV.update({
    "w2-reconstruction:prose-L3-L12": ("EXCLUDED", "introduction and outline (what W2 delivers; pointer to Corollary "
                                       "bpW:w2:clause5)"),
    "w2-reconstruction:prose-L14-L23": ("EXCLUDED", "route paragraph (outline of the proof)"),
    "w2-reconstruction:prose-L25-L33": ("NODE bpW:w2:functionals, bpW:w2:force, bpW:w2:coeffsol, bpW:w2:curve, "
                                        "bpW:w2:main", "standing data: notation identifying lambda, phi, U_m, V_m, G, "
                                        "kappa with the frozen lam, sineMode, reconU, reconV, cubicGrad, coeff (each "
                                        "consumer has the anchor edge where it uses the symbol); max norm on WaveSpace "
                                        "is ext-sums (norm_fst_le, norm_snd_le)"),
    "w2-reconstruction:prose-L37-L39": ("EXCLUDED", "introduction of the external list (pointer to W1's externals)"),
    "w2-reconstruction:prose-L65-L66": ("EXCLUDED", "layout"),
    "w2-reconstruction:prose-L375-L381": ("EXCLUDED", "Lean totality notes (administrative; the summability facts "
                                          "they recall are proved in Lemmas bpW:w2:functionals, bpW:w2:force)"),
    "w2-reconstruction:prose-L383-L392": ("EXCLUDED", "comparison with the source (provenance; errata N-4 already in W0)"),
    "w2-reconstruction:prose-L394-L403": ("EXCLUDED", "summary of results and inputs (administrative)"),
})
