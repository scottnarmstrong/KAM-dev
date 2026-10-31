# Writer spec for slice W-w0n (blueprint-W/parts/w0-normalization.tex, all lines). Rendered by w_depgraph_fill.py.
F = "blueprint-W/parts/w0-normalization.tex"
W1 = "blueprint-W/parts/w1-sequences.tex"

NODES = {
    "bpW:w0n:recon-bounded": dict(
        H="a > 0, p in R, k in N; c in l^{a,p}_C (also the standing m > 0 for the U_m, V_m clause)",
        Q="for all a > 0, p, k; for all c",
        C="sum_j |c_j| j^k <= M_{a,p,k} ||c||_{a,p} with M_{a,p,k}^2 = sum_j j^{2k-2p} e^{-2aj} < infinity; the series "
          "sum c_j phi_j and its termwise x-derivatives of order <= k converge absolutely and uniformly on [0,pi]; "
          "c -> sum c_j phi_j is bounded linear l^{a,p} -> C^k([0,pi]) with norm <= sqrt(2/pi) M_{a,p,k}, vanishes at "
          "x = 0, pi, and int_0^pi (sum c_j phi_j) phi_l = c_l; U_m, V_m and q -> U_m(lambda q) are bounded linear "
          "l^{a,p} -> C^k([0,pi]) for every p, since lambda_j^{+-1/2} <= (1+m)^{1/4} j^{1/2} and multiplication by "
          "lambda^r maps l^{a,p} into l^{a,p-|r|} (0 <= r <= 2) with norm <= (1+m)^{r/2}",
        S="M_{a,p,k} depends only on a, p, k; the multiplier norms on m",
        deps=[("bpW:w0:ellap#ellWeight", "L30", "the norm ||c||_{a,p} with weight j^p e^{aj} in Cauchy-Schwarz"),
              ("bpW:w0:basis#sineMode", "L31", "|d_x^r phi_j| <= sqrt(2/pi) j^r; phi_j(0) = phi_j(pi) = 0; orthonormality"),
              ("bpW:w1:ext-unifderiv", "L32", "Weierstrass M-test and termwise differentiation of uniformly convergent "
               "derivative series", F),
              ("bpW:w0:reconstruction#reconU", "L24", "U_m is a series of this form with c_j = q_j/sqrt(lambda_j)"),
              ("bpW:w0:reconstruction#reconV", "L24", "V_m is a series of this form with c_j = sqrt(lambda_j) p_j"),
              ("bpW:w0:basis#lam", "L25", "the multiplier lambda^r and the bound lambda_j^{+-1/2} <= (1+m)^{1/4} j^{1/2}"),
              ("bpW:w0:mass", "L34", "j^2 + m <= (1+m) j^2 uses m >= 0")]),
    "bpW:w0n:quartic-coeff": dict(
        H="i, j, k, l >= 1; g_ijkl = int_0^pi phi_i phi_j phi_k phi_l dx", Q="for all i, j, k, l >= 1",
        C="g_ijkl = (1/(2pi)) ([i+l=j+k] + [i+k=j+l] + [i+j=k+l] - [i=j+k+l] - [j=i+k+l] - [k=i+j+l] - [l=i+j+k]); "
          "g is symmetric; g_ijkl = 0 unless +-i+-j+-k+-l = 0; g_iiii = 3/(2pi); g_iijj = 1/pi (i != j); equivalently "
          "(bpW:w0n:g-signed) g_ijkl = (1/(2pi)) sum_{eps in {+-1}^3} s(eps) [l = eps_1 i + eps_2 j + eps_3 k], "
          "s(eps) = (-1)^{1+#{t: eps_t = -1}}, so |g_ijkl| <= (1/(2pi)) sum_eps [l = eps_1 i + eps_2 j + eps_3 k]",
        S="none",
        deps=[("bpW:w0:basis#sineMode", "L41", "g is the integral of a product of four modes phi"),
              ("stepW:w0n:prod", "L54", "proof step"), ("stepW:w0n:cos", "L57", "proof step"),
              ("stepW:w0n:signed", "L65", "proof step")]),
    "stepW:w0n:prod": dict(
        H="i, j, k, l >= 1", Q="for all x",
        C="phi_i phi_j phi_k phi_l = (1/pi^2)(cos(i-j)x - cos(i+j)x)(cos(k-l)x - cos(k+l)x)", S="none",
        deps=[("bpW:w0:basis#sineMode", "L56", "phi_j = sqrt(2/pi) sin(jx) and the product-to-sum formula")]),
    "stepW:w0n:cos": dict(
        H="integers A, B; the expansion of Step stepW:w0n:prod", Q="for all A, B in Z",
        C="int_0^pi cos Ax cos Bx dx = (pi/2)([A=B] + [A=-B]); hence the eight-bracket formula for g_ijkl, which reduces "
          "to the stated closed form, with g_iiii = 3/(2pi) and g_iijj = 1/pi (i != j)",
        S="none",
        deps=[("stepW:w0n:prod", "L60", "integrates the product-to-sum expansion termwise")]),
    "stepW:w0n:signed": dict(
        H="the closed form of Step stepW:w0n:cos; l >= 1", Q="for all i, j, k, l >= 1",
        C="the seven bracket relations solved for l give the signed form (bpW:w0n:g-signed) (the eighth pattern "
          "l = -i-j-k is impossible for l >= 1)", S="none",
        deps=[("stepW:w0n:cos", "L66", "rewrites the seven relations of the closed form")]),
    "bpW:w0n:gradient": dict(
        H="a > 0, p >= 0, q in l^{a,p}; hat q_j = q_j/sqrt(lambda_j)", Q="for all a > 0, p >= 0, q",
        C="G(q) = (1/4) sum_{i,j,k,l} g_ijkl hat q_i hat q_j hat q_k hat q_l and G_q(q)_l = (1/sqrt(lambda_l)) "
          "sum_{i,j,k} g_ijkl hat q_i hat q_j hat q_k, both absolutely convergent; G is Gateaux differentiable along "
          "every coordinate with dG/dq_l = G_q(q)_l; int_0^pi U_m(q)^3 phi_l dx = sqrt(lambda_l) G_q(q)_l",
        S="none",
        deps=[("bpW:w0n:recon-bounded", "L85", "k = 0: sum |hat q_j| < infinity and U_m(q) = sum hat q_j phi_j uniformly"),
              ("bpW:w0:reconstruction#reconU", "L85", "U_m(q) = sum hat q_j phi_j"),
              ("bpW:w0:H", "L88", "G(q) = (1/4) int U_m(q)^4"),
              ("bpW:w0n:quartic-coeff", "L86", "the coefficients g_ijkl of the termwise-integrated quadruple series"),
              ("bpW:w1:ext-integral", "L87", "termwise integration (dominated convergence for series) and "
               "differentiation under the integral", F),
              ("bpW:w0:Gq#cubicGrad", "L90", "identifies int U_m(q)^3 phi_l / sqrt(lambda_l) with G_q(q)_l")]),
    "bpW:w0n:algebra": dict(
        H="a >= 0, s >= 1; c, d in l^{a,s}_b", Q="for all a >= 0, s >= 1, c, d",
        C="||c*d||_{a,s} <= K_s ||c||_{a,s} ||d||_{a,s} with K_s = 2^s (1+2 zeta(2s))^{1/2}; K_{3/2}^2 = 8(1+2 zeta(3)); "
          "each convolution sum converges absolutely",
        S="K_s depends only on s",
        deps=[("bpW:w0:twosided", "L95", "the two-sided spaces and the convolution"),
              ("stepW:w0n:weight", "L102", "proof step"), ("stepW:w0n:young", "L107", "proof step")]),
    "stepW:w0n:weight": dict(
        H="a >= 0, s >= 1; w_l = <l>^s e^{a|l|}", Q="for all i, l in Z",
        C="e^{a|l|} <= e^{a|i|} e^{a|l-i|}, <l> <= <i> + <l-i>, and w_l <= 2^{s-1}(w_i w_{l-i}/<l-i>^s + w_i w_{l-i}/<i>^s)",
        S="none",
        deps=[("bpW:w0:twosided", "L103", "the weight <l> = max(1,¦l¦) of l^{a,s}_b")]),
    "stepW:w0n:young": dict(
        H="the weight inequality of Step stepW:w0n:weight; C_l = w_l ¦c_l¦, D_l = w_l ¦d_l¦", Q="for all l",
        C="w_l ¦(c*d)_l¦ <= 2^{s-1}((C*D')_l + (C'*D)_l); with Young ||X*Y||_2 <= ||X||_2 ||Y||_1 and "
          "||D'||_1 <= ||D||_2 (1+2 zeta(2s))^{1/2} this gives the bound with K_s and the absolute convergence",
        S="K_s depends only on s",
        deps=[("stepW:w0n:weight", "L108", "inserts the weight inequality"),
              ("bpW:w1:young", "L109", "Young's inequality (i) and the l^1 control with 1+2 zeta(2s) (ii)")]),
    "bpW:w0n:cubic-bound": dict(
        H="a >= 0, p >= 1/2; T(q,q',q'')_l = (1/sqrt(lambda_l)) sum_{i,j,k} g_ijkl hat q_i hat q'_j hat q''_k on "
          "(l^{a,p}_C)^3, hat q_j = q_j/sqrt(lambda_j)",
        Q="for all a >= 0, p >= 1/2; for all q, q', q''",
        C="the sums converge absolutely; T is a bounded trilinear map into l^{a,p+1}_C, real on real arguments, with "
          "||T(q,q',q'')||_{a,p+1} <= C_* ||q|| ||q'|| ||q''||, C_* = K_{p+1/2}^2/pi; for a > 0, G_q(q) = T(q,q,q); for "
          "a = p = 1, G_q : l^{1,1} -> l^{1,2} is real analytic (a continuous cubic polynomial) with "
          "||G_q(q)||_{1,2} <= C_m ||q||_{1,1}^3, C_m = 8(1+2 zeta(3))/pi (about 8.67)",
        S="C_* depends only on p; C_m is independent of m > 0 (only lambda_j >= j is used)",
        deps=[("bpW:w0n:quartic-coeff", "L120", "the coefficients g_ijkl of T"),
              ("bpW:w0:basis#lam", "L120", "the weights 1/sqrt(lambda)"),
              ("bpW:w0:Gq#cubicGrad", "L125", "the identification G_q(q) = T(q,q,q)"),
              ("stepW:w0n:majorant", "L132", "proof step"), ("stepW:w0n:selection", "L136", "proof step"),
              ("stepW:w0n:smoothing", "L142", "proof step"), ("stepW:w0n:analytic", "L149", "proof step")]),
    "stepW:w0n:majorant": dict(
        H="q in l^{a,p}_C; x_i = ¦q_¦i¦¦/sqrt(lambda_¦i¦) (i != 0), x_0 = 0", Q="for q, q', q''",
        C="x is even and ||x||_{a,p+1/2}^2 = 2 sum_i (i/lambda_i) i^{2p} e^{2ai} ¦q_i¦^2 <= 2 ||q||_{a,p}^2 (the "
          "corrected constant sqrt 2, errata N-1)",
        S="none",
        deps=[("bpW:w0:twosided", "L135", "the two-sided norm of the majorant"),
              ("bpW:w0:basis#lambda-facts", "L134", "lambda_i >= i (i/lambda_i < 1)")]),
    "stepW:w0n:selection": dict(
        H="the majorants x, x', x'' of Step stepW:w0n:majorant; l >= 1", Q="for all l >= 1",
        C="sum_{i,j,k} ¦g_ijkl¦ ¦hat q_i hat q'_j hat q''_k¦ <= (1/(2pi)) (x*x'*x'')_l, so the sum defining T converges "
          "absolutely", S="none",
        deps=[("bpW:w0n:quartic-coeff", "L137", "the signed form (bpW:w0n:g-signed) and its bound"),
              ("stepW:w0n:majorant", "L139", "the even majorants x, x', x''")]),
    "stepW:w0n:smoothing": dict(
        H="X = x*x'*x'' from Step stepW:w0n:selection; s = p + 1/2 >= 1", Q="for q, q', q''",
        C="||T||_{a,p+1}^2 <= (1/(8 pi^2)) ||X||_{a,p+1/2}^2 and ||X|| <= K_s^2 2^{3/2} prod ||q||, hence "
          "||T||_{a,p+1} <= (K_s^2/pi) prod ||q||", S="K_s depends only on s = p + 1/2",
        deps=[("stepW:w0n:selection", "L143", "the pointwise bound by X_l/(2pi)"),
              ("bpW:w0:basis#lambda-facts", "L143", "l/lambda_l <= 1"),
              ("bpW:w0n:algebra", "L146", "the algebra bound with s = p + 1/2 >= 1, applied twice"),
              ("stepW:w0n:majorant", "L147", "||x|| <= sqrt 2 ||q||")]),
    "stepW:w0n:analytic": dict(
        H="T bounded symmetric trilinear (Steps above)", Q="none",
        C="T is trilinear and symmetric; q -> T(q,q,q) is a continuous homogeneous cubic polynomial, analytic on the "
          "whole space, real on real sequences; for a > 0 it is G_q (Lemma bpW:w0n:gradient)", S="none",
        deps=[("bpW:w0n:quartic-coeff", "L150", "symmetry of g"),
              ("bpW:w1:ext-analytic", "L152", "a continuous multilinear map (its diagonal) is analytic", F),
              ("bpW:w0n:gradient", "L154", "identification with G_q for a > 0")]),
    "bpW:w0n:pde-equiv": dict(
        H="I subset R open interval; q, p : I -> l^{1,1}; (i): q, p continuous into l^{1,1}, continuously "
          "differentiable into l^{1,0}, satisfying (bpW:w0:coeffsys) in l^{1,0}; (ii): u(t,x) = U_m(q(t))(x) is a "
          "classical solution of (bpW:w0:eq) on I and u_t(t,.) = V_m(p(t)) for every t",
        Q="for every open I and q, p as stated; (force identity) for every q in l^{1,1}",
        C="(i) u = U_m(q(t)) is a classical solution of (bpW:w0:eq) on I with u_t = V_m(p(t)); (ii) every q_j, p_j is "
          "C^1 on I and (bpW:w0:coeffsys) holds coordinatewise; and (bpW:w0n:force): U_m(q)^3 = sum_l sqrt(lambda_l) "
          "G_q(q)_l phi_l uniformly on [0,pi] and -d_x^2 U_m(q) + m U_m(q) = U_m(lambda^2 q)",
        S="none",
        deps=[("bpW:w0:eqmotion", "L169", "the coefficient system (bpW:w0:coeffsys)"),
              ("bpW:w0:nlw#IsClassicalSolution", "L170", "classical solution of (bpW:w0:eq)"),
              ("bpW:w0:reconstruction#reconU", "L170", "u = U_m(q(t))"),
              ("bpW:w0:reconstruction#reconV", "L171", "u_t = V_m(p(t))"),
              ("stepW:w0n:force", "L186", "proof step"), ("stepW:w0n:time", "L193", "proof step"),
              ("stepW:w0n:ident", "L199", "proof step"), ("stepW:w0n:converse", "L202", "proof step")]),
    "stepW:w0n:force": dict(
        H="q in l^{1,1}; f = U_m(q)^3 in C([0,pi])", Q="for q",
        C="(bpW:w0n:force): U_m(q)^3 = sum_l sqrt(lambda_l) G_q(q)_l phi_l uniformly on [0,pi], and "
          "-d_x^2 U_m(q) + m U_m(q) = U_m(lambda^2 q)", S="none",
        deps=[("bpW:w0n:gradient", "L187", "int f phi_l = sqrt(lambda_l) G_q(q)_l"),
              ("bpW:w0n:cubic-bound", "L188", "(sqrt(lambda_l) G_q(q)_l) lies in l^{1,1}"),
              ("bpW:w0n:recon-bounded", "L188", "uniform convergence of S (k = 0) and termwise differentiation (k = 2)"),
              ("bpW:w1:sine-completeness", "L190", "(phi_l) is a complete orthonormal system of L^2(0,pi)", F),
              ("bpW:w0:basis#sineMode", "L192", "-phi_j'' + m phi_j = lambda_j^2 phi_j"),
              ("bpW:w0:basis#lam", "L192", "the eigenvalue lambda_j^2 = j^2 + m")]),
    "stepW:w0n:time": dict(
        H="the hypotheses of (i)", Q="t in I",
        C="q is C^1 into l^{1,-1} with ddot q = -lambda^2 q - lambda G_q(q); t -> u(t,.) is C^2 into C^2([0,pi]); "
          "u, u_t, u_tt, u_x, u_xx exist and are jointly continuous; u_t = U_m(lambda p) = V_m(p); u_tt = U_m(ddot q)",
        S="none",
        deps=[("bpW:w0:eqmotion", "L194", "dot q = lambda p and dot p = -lambda q - G_q(q)"),
              ("bpW:w0n:recon-bounded", "L196", "lambda bounded l^{1,0} -> l^{1,-1}; U_m : l^{1,-1} -> C^2([0,pi]) bounded linear"),
              ("bpW:w0:reconstruction#reconV", "L198", "U_m(lambda p) = V_m(p)")]),
    "stepW:w0n:ident": dict(
        H="the conclusions of Steps stepW:w0n:force and stepW:w0n:time", Q="t in I",
        C="u_tt = u_xx - m u - u^3 and u(t,0) = u(t,pi) = 0, so u is a classical solution with u_t = V_m(p)", S="none",
        deps=[("stepW:w0n:force", "L200", "U_m(lambda^2 q) = -u_xx + m u and U_m(lambda G_q(q)) = u^3"),
              ("stepW:w0n:time", "L200", "u_tt = U_m(ddot q)"),
              ("bpW:w0n:recon-bounded", "L201", "boundary values vanish"),
              ("bpW:w0:nlw#IsClassicalSolution", "L201", "the definition of classical solution being verified")]),
    "stepW:w0n:converse": dict(
        H="the hypotheses of (ii)", Q="t in I, l >= 1",
        C="int u phi_l = q_l/sqrt(lambda_l), int u_t phi_l = sqrt(lambda_l) p_l; dot q_l = lambda_l p_l and "
          "sqrt(lambda_l) dot p_l = int u_tt phi_l = -lambda_l^2 q_l/sqrt(lambda_l) - sqrt(lambda_l) G_q(q)_l, i.e. "
          "(bpW:w0:coeffsys) coordinatewise with q_l, p_l in C^1", S="none",
        deps=[("bpW:w0:nlw#IsClassicalSolution", "L204", "u_t, u_tt continuous; the equation and boundary values"),
              ("bpW:w0n:recon-bounded", "L203", "the coefficient formula int (sum c_j phi_j) phi_l = c_l"),
              ("bpW:w1:ext-integral", "L204", "differentiation under the integral sign", F),
              ("bpW:w0:basis#sineMode", "L206", "phi_l(0) = phi_l(pi) = 0 and phi_l'' = -l^2 phi_l (integration by parts)"),
              ("bpW:w0n:gradient", "L207", "int u^3 phi_l = sqrt(lambda_l) G_q(q)_l")]),
    "bpW:w0n:nonres": dict(
        H="m > 0; a, b, c, d >= 1 with g_abcd != 0; sigma in {+-1}^4 with sigma_1 lambda_a + sigma_2 lambda_b + "
          "sigma_3 lambda_c + sigma_4 lambda_d = 0",
        Q="for all m > 0, a, b, c, d, sigma", C="the indices with sigma = +1 and those with sigma = -1 form equal "
        "multisets (two of each)", S="none",
        deps=[("bpW:w0:basis#lam", "L222", "the frequencies lambda"),
              ("bpW:w0n:quartic-coeff", "L227", "g_abcd != 0 implies a signed relation +-a+-b+-c+-d = 0"),
              ("stepW:w0n:31", "L229", "proof step"), ("stepW:w0n:22", "L233", "proof step")]),
    "stepW:w0n:31": dict(
        H="the signed relation among a, b, c, d (each index at most the sum of the other three)", Q="x, y >= 1",
        C="all four signs equal is impossible; three equal signs are impossible since lambda_x + lambda_y > "
          "lambda_{x+y} and lambda_d <= lambda_{a+b+c} < lambda_a + lambda_b + lambda_c", S="none",
        deps=[("bpW:w0:basis#lambda-facts", "L231", "lambda > 0 and j -> lambda_j increasing"),
              ("bpW:w0:mass", "L232", "squaring: 2 sqrt((x^2+m)(y^2+m)) > 2xy - m uses m > 0")]),
    "stepW:w0n:22": dict(
        H="lambda_a + lambda_b = lambda_c + lambda_d with {a,b} != {c,d}; f(s) = sqrt(s^2+m)",
        Q="the three cases of the signed relation",
        C="case (1) a+b = c+d, case (2) a+c = b+d, case (3) a = b+c+d each lead to a contradiction; the cases are "
          "exhaustive", S="none",
        deps=[("bpW:w0:basis#lambda-facts", "L236", "strict convexity of f, f' > 0 increasing")]),
    "bpW:w0n:birkhoff#data": dict(
        new=True, kind="definition", title="Quartic part in complex coordinates; resonance; tangential/normal split",
        stmt=f"{F}#bpW:w0n:birkhoff@L258-L268", proof="-",
        H="J = {1,2}, N = {j >= 3}; complex coordinates z of Definition bpW:w0:z", Q="none",
        C="defines (with the identity (bpW:w0n:Gz)) G = (1/16) sum g_ijkl (lambda_i lambda_j lambda_k lambda_l)^{-1/2} "
          "prod (z + zbar) as a sum of monomials z^alpha zbar^beta, ¦alpha¦+¦beta¦ = 4, evolving by "
          "e^{-i<alpha-beta,hat lambda>t} along the linear flow; resonant iff <alpha-beta,hat lambda> = 0; the split "
          "G = G^tan + G^nor, G^nor the monomials with all indices in N",
        S="none",
        note="Unlabelled prose L258-L268 (with the display bpW:w0n:Gz) that fixes data consumed by Qdef, AB and "
             "formal-birkhoff (SPEC section-data rule).",
        deps=[("bpW:w0:z", "L259", "q_j = (z_j + zbar_j)/sqrt 2 and the linear flow dz_j = -i lambda_j z_j"),
              ("bpW:w0n:gradient", "L261", "G = (1/4) sum g_ijkl q-hat^4 (quartic series)"),
              ("bpW:w0:basis#lam", "L261", "the weights (lambda_i lambda_j lambda_k lambda_l)^{-1/2}")]),
    "bpW:w0n:Qdef": dict(
        H="G^tan, G^nor and resonance as in bpW:w0n:birkhoff#data", Q="none",
        C="defines bar G = the sum of the resonant monomials of G^tan (with coefficients) and the partial quartic "
          "normal form Lambda + bar G + G^nor", S="none",
        deps=[("bpW:w0n:birkhoff#data", "L271", "resonant monomials of G^tan; G^nor"),
              ("bpW:w0:H", "L272", "Lambda, the quadratic part of H")]),
    "bpW:w0n:AB": dict(
        H="J = {1,2}; m > 0; I = (I_1,I_2), Z = (I_j)_{j>=3}, I_j = ¦z_j¦^2", Q="for every m > 0",
        C="bar G = (1/2)<AI,I> + <BI,Z> with A_ii = 9/(8 pi lambda_i^2), A_12 = A_21 = 3/(2 pi lambda_1 lambda_2), "
          "B_ji = 3/(2 pi lambda_j lambda_i) (j >= 3, i in J); equivalently A = (3/(8pi)) D(4 11^T - Id)D, "
          "D = diag(1/lambda_1, 1/lambda_2), (BI)_j = (3/(2 pi lambda_j))(I_1/lambda_1 + I_2/lambda_2); and "
          "(bpW:w0n:avgG) <G> = (3/(16 pi))(4 (sum_j I_j/lambda_j)^2 - sum_j I_j^2/lambda_j^2)",
        S="none",
        deps=[("bpW:w0n:Qdef", "L277", "bar G is the resonant tangential part"),
              ("bpW:w0:actions", "L276", "I_j = ¦z_j¦^2, tangential I, normal Z"),
              ("bpW:w0:basis#lam", "L278", "lambda in A and B"),
              ("stepW:w0n:resavg", "L289", "proof step"), ("stepW:w0n:moments", "L295", "proof step"),
              ("stepW:w0n:sum", "L299", "proof step")]),
    "stepW:w0n:resavg": dict(
        H="the monomials of (bpW:w0n:Gz) with nonzero coefficient", Q="monomials z^alpha zbar^beta",
        C="a monomial is resonant iff alpha = beta (it is I_a I_b); the angle average of z^alpha zbar^beta is "
          "delta_{alpha beta} I^alpha; hence bar G is the part of <G> (extended from finitely supported q by the "
          "absolutely convergent formula) with at least one tangential action", S="none",
        deps=[("bpW:w0n:nonres", "L290", "resonance with nonzero coefficient forces alpha = beta"),
              ("bpW:w0n:birkhoff#data", "L290", "the monomials of (bpW:w0n:Gz)"),
              ("bpW:w0:actions", "L291", "z_j = sqrt(I_j) e^{-i phi_j}"),
              ("bpW:w0n:Qdef", "L292", "bar G as the resonant tangential monomials")]),
    "stepW:w0n:moments": dict(
        H="q_j = sqrt(2 I_j) cos phi_j, independent angles", Q="indices i, j, k, l",
        C="<q_i q_j q_k q_l> = 0 unless the indices pair up; <q_i^4> = (3/2) I_i^2; <q_i^2 q_j^2> = I_i I_j (i != j); "
          "(i,i,i,i) occurs once and {i,i,j,j} six times among ordered quadruples", S="none",
        deps=[("bpW:w0:actions", "L296", "q_j = sqrt(2 I_j) cos phi_j")]),
    "stepW:w0n:sum": dict(
        H="y_j = I_j/lambda_j; Steps stepW:w0n:resavg and stepW:w0n:moments", Q="none",
        C="<G> = (9/(16pi)) sum y_i^2 + (3/(2pi)) sum_{i<j} y_i y_j, which is (bpW:w0n:avgG); matching gives A and B",
        S="none",
        deps=[("bpW:w0n:gradient", "L300", "G = (1/4) sum g_ijkl hat q^4 with hat q = q/sqrt(lambda)"),
              ("bpW:w0n:quartic-coeff", "L300", "g_iiii = 3/(2pi), g_iijj = 1/pi"),
              ("stepW:w0n:moments", "L301", "the moments 3/2 I^2, I_i I_j and the multiplicities"),
              ("stepW:w0n:resavg", "L303", "bar G = the part of <G> with a tangential action")]),
    "bpW:w0n:formal-birkhoff": dict(
        H="F the quartic polynomial with coefficient c_ab/(-i<alpha-beta,hat lambda>) on each nonresonant monomial "
          "z^alpha zbar^beta of G^tan (coefficient c_ab) and zero otherwise",
        Q="none",
        C="F is real; X_Lambda F = G^tan - bar G (X_Lambda F = dF/dt along the linear flow); formally "
          "H o Phi^1_F = Lambda + bar G + G^nor + (terms of degree >= 6); the quartic part of the normal form is "
          "independent of the choice of F among solutions of X_Lambda F = G^tan - bar G",
        S="none",
        deps=[("bpW:w0n:birkhoff#data", "L308", "monomials of G^tan, resonance, divisors <alpha-beta,hat lambda>"),
              ("bpW:w0n:Qdef", "L310", "bar G and the normal form"),
              ("bpW:w0n:nonres", "L318", "the divisors of nonresonant monomials are nonzero"),
              ("bpW:w0:z", "L318", "X_Lambda (z^alpha zbar^beta) = -i<alpha-beta,hat lambda> z^alpha zbar^beta along "
               "dz = -i lambda z"),
              ("bpW:w0:H", "L321", "H = Lambda + G in the Lie series")]),
    "bpW:w0n:nondeg-sec#data": dict(
        new=True, kind="definition", title="Nondegeneracy conditions (A1)-(A3) of the Cantor Manifold Theorem",
        stmt=f"{F}#bpW:w0n:nondeg-sec@L341-L344", proof="-",
        H="A, B of Theorem bpW:w0n:AB", Q="(k,l) in Z^2 x Z^N with 1 <= ¦l¦ <= 2",
        C="defines omega(I) = lambda_J + A I, Omega(I) = lambda_N + B I and the conditions (A1) det A != 0, (A2) "
          "<l,lambda_N> != 0, (A3) <k,omega(I)> + <l,Omega(I)> not identically 0 as an affine function of I, for all "
          "(k,l) with 1 <= ¦l¦ <= 2 (¦l¦ = sum ¦l_j¦)", S="none",
        note="Unlabelled prose L341-L344 defining the conditions stated in Theorem bpW:w0n:nondeg (SPEC section-data rule).",
        deps=[("bpW:w0n:AB", "L341", "omega(I) = lambda_J + A I and Omega(I) = lambda_N + B I")]),
    "bpW:w0n:nondeg": dict(
        H="J = {1,2}; m > 0; A, B of Theorem bpW:w0n:AB; (A1)-(A3) as in bpW:w0n:nondeg-sec#data",
        Q="for every m > 0",
        C="(i) det A = -63/(64 pi^2 lambda_1^2 lambda_2^2) = -63/(64 pi^2 (1+m)(4+m)) != 0; (ii) <l,lambda_N> != 0 for "
          "1 <= ¦l¦ <= 2; (iii) (A3) holds", S="none",
        deps=[("bpW:w0n:nondeg-sec#data", "L351", "the conditions (A2), (A3)"),
              ("bpW:w0n:AB", "L349", "the matrix A"),
              ("stepW:w0n:det", "L356", "proof step"), ("stepW:w0n:A2", "L360", "proof step"),
              ("stepW:w0n:A3red", "L363", "proof step"), ("stepW:w0n:l1", "L369", "proof step"),
              ("stepW:w0n:l2", "L373", "proof step")]),
    "stepW:w0n:det": dict(
        H="A of Theorem bpW:w0n:AB", Q="none", C="det A = (3/(8pi))^2 lambda_1^{-2} lambda_2^{-2} det((3,4),(4,3)) = "
        "-63/(64 pi^2) lambda_1^{-2} lambda_2^{-2}", S="none",
        deps=[("bpW:w0n:AB", "L357", "A = (3/(8pi)) D(4 11^T - Id) D")]),
    "stepW:w0n:A2": dict(
        H="l in Z^N, 1 <= ¦l¦ <= 2", Q="l", C="<l,lambda_N> is +-lambda_a, +-2 lambda_a, +-(lambda_a+lambda_b) or "
        "+-(lambda_a-lambda_b), a != b in N, all nonzero", S="none",
        deps=[("bpW:w0:basis#lambda-facts", "L362", "lambda > 0 strictly increasing")]),
    "stepW:w0n:A3red": dict(
        H="b = (1/lambda_1, 1/lambda_2), s = sum_{j>=3} l_j/lambda_j", Q="(k,l)",
        C="A = (3/(8pi))(4bb^T - D^2), B^T l = (3/(2pi)) s b; the linear part (3/(8pi))(4(<b,k>+s)b - D^2 k) vanishes "
          "iff k_i/lambda_i = c (i = 1,2) with c = 4(<b,k>+s), then <b,k> = 2c, s = -(7/4)c; the constant part is "
          "c(lambda_1^2+lambda_2^2) + <l,lambda_N>", S="none",
        deps=[("bpW:w0n:AB", "L365", "A and B"),
              ("bpW:w0n:nondeg-sec#data", "L366", "the affine map of (A3)")]),
    "stepW:w0n:l1": dict(
        H="¦l¦ = 1, l = sigma e_nu, nu >= 3; the reduction of Step stepW:w0n:A3red", Q="sigma, nu",
        C="the constant part vanishes iff 7 lambda_nu^2 = 4(lambda_1^2+lambda_2^2), and then k_i^2 in (0,4/7) is not "
          "the square of an integer; so (A3) holds", S="none",
        deps=[("stepW:w0n:A3red", "L370", "the vanishing conditions of the reduction")]),
    "stepW:w0n:l2": dict(
        H="¦l¦ = 2; the reduction of Step stepW:w0n:A3red", Q="l",
        C="¦s¦ <= 2/lambda_3 < 2/3, ¦c¦ < 8/21, k_2 - k_1 = c(lambda_2 - lambda_1) with 0 < lambda_2 - lambda_1 < 1 "
          "forces k_1 = k_2, c = 0, s = 0, impossible for ¦l¦ = 2; so the linear part does not vanish", S="none",
        deps=[("stepW:w0n:A3red", "L374", "the vanishing conditions of the reduction"),
              ("bpW:w0:basis#lambda-facts", "L375", "lambda_3 > 3, 0 < lambda_2 - lambda_1 < 1, lambda injective")]),
    "bpW:w0n:duffing": dict(
        H="restriction of (bpW:w0:eq) to u = x(t) phi_j(x), only mode j excited, forcing of other modes dropped",
        Q="j >= 1; amplitude a",
        C="the coefficient equation is the Duffing equation ddot x + lambda_j^2 x + eps x^3 = 0, eps = g_jjjj = 3/(2pi); "
          "with q_j = sqrt(lambda_j) x and I_j = lambda_j a^2/2 its Lindstedt-Poincare frequency is "
          "lambda_j + (9/(8 pi lambda_j^2)) I_j + O(a^4) = lambda_j + A_jj I_j, the normal-form frequency", S="none",
        note="Consistency check (f) of W0; no later proof consumes it so far (decide at W8, SPEC Reachability).",
        deps=[("bpW:w0:nlw#IsClassicalSolution", "L392", "restriction of the equation (bpW:w0:eq)"),
              ("bpW:w0n:quartic-coeff", "L403", "int (x phi_j)^3 phi_j = x^3 g_jjjj, g_jjjj = 3/(2pi)"),
              ("bpW:w0n:ledger#ext-lindstedt", "L403", "the classical Lindstedt shift 3 eps a^2/(8 omega_0)"),
              ("bpW:w0:actions", "L406", "I_j = (q_j^2+p_j^2)/2 = lambda_j a^2/2 to leading order"),
              ("bpW:w0n:AB", "L397", "A_jj = 9/(8 pi lambda_j^2)")]),
    "bpW:w0n:ledger#ext-lindstedt": dict(
        new=True, kind="external", title="Classical Lindstedt frequency shift (unlabelled W0 external)",
        stmt=f"{F}#bpW:w0n:ledger@L422-L423", proof="-",
        H="the Duffing equation ddot x + omega_0^2 x + eps x^3 = 0", Q="amplitude a -> 0",
        C="its Lindstedt-Poincare frequency at amplitude a is omega_0 + 3 eps a^2/(8 omega_0) + O(a^4) (\"the classical "
          "Lindstedt shift\", W0 ledger \"External standard facts\")", S="none",
        note="Unlabelled external of the W0 ledger (SPEC External inputs); used only by bpW:w0n:duffing.",
        deps=[]),
}

DELETE = ["bpW:w0n:nonres-remark", "bpW:w0n:compare", "bpW:w0n:kappa"]

COV = {
    "bpW:w0n:nonres-remark": ("EXCLUDED", "administrative remark (qualitative versus quantitative nonresonance; "
                              "pointer to W3's bpW:w3:divisor); no proof consumes it"),
    "bpW:w0n:compare": ("EXCLUDED", "administrative remark (comparison with the printed P96-W coefficients, "
                        "E-PDE-W-1); no proof consumes it"),
    "bpW:w0n:kappa": ("EXCLUDED", "administrative remark (P96-W's exponent kappa = 2 is unchanged by the correction); "
                      "the spectral asymptotics used later are proved in bpW:w1:tails; no proof consumes it"),
    "w0-normalization:sourcegap-L159": ("NODE stepW:w0n:majorant", "the printed P96-W p. 280 bound (constant 1) is "
                                        "wrong; the blueprint proves the corrected constant sqrt 2 in the majorant "
                                        "step (errata N-1); constants only, no open gap"),
    "w0-normalization:prose-L3-L14": ("EXCLUDED", "introduction and outline (standing assumption bpW:w0:mass "
                                      "pointer, list of results)"),
    "w0-normalization:prose-L211-L216": ("EXCLUDED", "provenance note (expansion of P96-W Lemma 1, errata N-4); the "
                                         "completeness of (phi_l) it mentions is the edge stepW:w0n:force -> "
                                         "bpW:w1:sine-completeness"),
    "w0-normalization:prose-L258-L268": ("NODE bpW:w0n:birkhoff#data", "fixes the quartic part in z-coordinates "
                                         "(bpW:w0n:Gz), resonance and the split G^tan + G^nor"),
    "w0-normalization:prose-L341-L344": ("NODE bpW:w0n:nondeg-sec#data", "defines (A1)-(A3)"),
    "w0-normalization:prose-L408-L413": ("EXCLUDED", "remark on a numerical check (scripts/wave/w0_checks.py); "
                                         "not a mathematical input"),
    "w0-normalization:prose-L417-L429": ("NODE bpW:w0n:ledger#ext-lindstedt", "ledger: its only unlabelled external "
                                         "not provided elsewhere is the Lindstedt shift; the other external facts map "
                                         "to bpW:w1:sine-completeness, bpW:w1:ext-analytic, bpW:w1:young, "
                                         "bpW:w1:ext-series (SPEC); the rest is administrative"),
}
