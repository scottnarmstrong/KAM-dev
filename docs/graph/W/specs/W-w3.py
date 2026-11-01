# Writer spec for slice W-w3 (blueprint-W/parts/w3-birkhoff.tex, all lines). Rendered by w_depgraph_fill.py.
F = "blueprint-W/parts/w3-birkhoff.tex"
STEP_CONTEXT = True
SYMBOL_EDGES = True
SD = "W3 standing data (L23-L27): m > 0, a >= 0 and p >= 1/2 fixed, J = {1,2}"
EXT = dict(H="none (Mathlib-level external fact)", Q="as stated in the item", S="none", deps=[])
PS = "proof step"

NODES = {
    "bpW:w3:ext-multilinear": dict(EXT, C="continuous multilinear maps between Banach spaces form a Banach space under "
        "the operator norm; inserting a continuous multilinear map into a slot of another, or composing with continuous "
        "linear maps, gives a continuous multilinear map of norm at most the product; the diagonal P(w) = M(w,...,w) of "
        "a continuous d-linear M is C^infinity with DP(w)v = sum_i M(w,..,v (slot i),..,w)"),
    "bpW:w3:ext-series": dict(EXT, C="if (M_n) are continuous n-linear with sum ||M_n|| r^n < infinity then f(w) = sum "
        "M_n(w,..,w) has this power series on the open ball of radius r, is analytic there, derivative termwise; finite "
        "sums, compositions and continuous multilinear images of analytic maps are analytic; A -> A^{-1} is analytic on "
        "the units of a Banach algebra; the derivative of an analytic map is analytic; C-analytic implies R-analytic; "
        "a FormalMultilinearSeries carries explicit zero coefficients"),
    "bpW:w3:ext-tsum": dict(EXT, C="termwise differentiation of sum f_k on an open convex set under sum sup ||Df_k|| < "
        "infinity and convergence at a point; absolutely summable families may be regrouped along any partition; for a "
        "continuous multilinear B and absolutely summable families, B(sum a^1,..,sum a^r) = sum B(a^1_{i_1},..,a^r_{i_r}) "
        "absolutely (Cauchy products)"),
    "bpW:w3:ext-mvt": dict(EXT, C="mean value inequality ||f(y) - f(x)|| <= M ||y - x|| on a convex set with ||Df|| <= M; "
        "a differentiable function on an interval with vanishing derivative is constant"),
    "bpW:w3:ext-integral": dict(EXT, C="for Y : [0,1] x U -> V continuous, differentiable in w with D_w Y continuous and "
        "bounded, w -> int_0^1 Y(t,w) dt is differentiable with derivative int D_w Y (complex differentiable over C); "
        "the fundamental theorem of calculus for C^1 maps [0,1] -> V; continuous linear maps commute with the Bochner "
        "integral; ||int Y|| <= int ||Y||; termwise integration of sum g_j with sup ||g_j|| <= c_j, sum c_j < infinity"),
    "bpW:w3:ext-neumann": dict(EXT, C="if A is a bounded operator on a Banach space with ||A - I|| <= 1/2 then A is "
        "invertible, ||A^{-1}|| <= 2, ||A^{-1} - I|| <= 2||A - I||, and A^{-1} = sum_{n>=0} (I - A)^n absolutely"),
    "bpW:w3#data": dict(
        new=True, kind="definition", title="W3 standing data (a, p, J)", stmt=f"{F}#bpW:w3@L23-L27", proof="-",
        H="none", Q="none", C="fixes, throughout Part W3, a >= 0 and p >= 1/2 (headline a = p = 1), the tangential modes "
        "J = {1,2} and normal modes j >= 3; constants depend on m, a, p as listed in section bpW:w3:constants",
        S="none", note="Unlabelled 'Standing data' paragraph (SPEC hypothesis packages): its premise p >= 1/2 is used by "
                       "Lemma bpW:w3:Lambda and every bound through C_* = K_{p+1/2}^2/pi; it is recorded in the "
                       "SOURCE_HYPOTHESES of each W3 result.",
        deps=[("bpW:w0:mass", "L23", "Standing assumption m > 0 in force")]),
    "bpW:w3:space": dict(
        H=SD + "; typing data a >= 0, r in R", Q="a, r",
        C="defines W_{a,r} = complex families (w_l)_{l in Z\\0} with ||w||_{a,r}^2 = sum_{l != 0} ¦l¦^{2r} e^{2a¦l¦} "
          "¦w_l¦^2 < infinity; W = W_{a,p}, W+ = W_{a,p+1} (norms ||.||, ||.||_+); tilde w (¦l¦ <= 2) and hat w "
          "(¦l¦ >= 3); lambda'_l = sgn(l) lambda_¦l¦; Lean carrier lp (Bool x PNat -> C) 2 in weighted coordinates",
        S="none", deps=[("bpW:w3#data", "L111", "W = W_{a,p} with the standing a, p")]),
    "bpW:w3:coords": dict(
        H=SD + "; E^C = l^{a,p}_C x l^{a,p}_C with the max norm; Z : E^C -> W, (Zx)_j = (q_j + i p_j)/sqrt2, "
          "(Zx)_{-j} = (q_j - i p_j)/sqrt2", Q="for all x in E^C, w in W",
        C="Z is a C-linear bijection with ||x||_E <= ||Zx|| <= sqrt2 ||x||_E, mapping E^C_{a,p+1} onto W+ with the same "
          "bounds; rho(w)_l = conj(w_{-l}) is a conjugate-linear isometric involution of W and W+; Z maps the real "
          "E_{a,p} bijectively onto W_R = {rho w = w}; on real points w_j = z_j, w_{-j} = zbar_j, w_j w_{-j} = ¦z_j¦^2 = "
          "I_j", S="none",
        deps=[("bpW:w3:space", "L121", "the space W"),
              ("bpW:w0:z", "L127", "the complex coordinates z_j"),
              ("bpW:w0:actions", "L127", "I_j = ¦z_j¦^2")]),
    "bpW:w3:omega": dict(
        H=SD, Q="for all w, w' in W; x, x' real in E",
        C="Omega(w,w') = i sum_{l != 0} sgn(l) w_l w'_{-l} is continuous antisymmetric bilinear on W, ¦Omega(w,w')¦ <= "
          "||w|| ||w'||, nondegenerate (Omega(zeta,e_{-l}) = i sgn(l) zeta_l); Omega(Zx,Zx') = sum (q_j p'_j - p_j q'_j) "
          "(the form sum dq ^ dp); Omega(rho w, rho w') = conj Omega(w,w')", S="none",
        deps=[("bpW:w3:space", "L140", "the space W and its norm"),
              ("bpW:w3:coords", "L149", "the inverse formulas of Z"),
              ("bpW:w0:eqmotion", "L144", "the symplectic form sum dq_j ^ dp_j")]),
    "bpW:w3:hamfield-def": dict(
        H=SD + "; U subset W open, P : U -> C complex differentiable", Q="U, P",
        C="defines X_P as the map with DP(w)v = Omega(X_P(w),v) for all w in U, v in W (unique, X_P(w)_l = -i sgn(l) "
          "DP(w) e_{-l}); P real iff P(rho w) = conj P(w) on U = rho U (then X_P o rho = rho o X_P); the class A(U) of "
          "real P analytic on U whose Hamiltonian field exists, takes values in W+, and is analytic U -> W+; analytic "
          "maps are holomorphic (Definition bpW:w1:holomorphic)", S="none",
        deps=[("bpW:w3:omega", "L157", "uniqueness by nondegeneracy; the formula for X_P"),
              ("bpW:w3:coords", "L158", "the involution rho"),
              ("bpW:w1:holomorphic", "L161", "holomorphic maps")]),
    "bpW:w3:hamfield-def#hamilton": dict(
        new=True, kind="claim", title="Hamilton's equations and reality of X_P",
        stmt=f"{F}#bpW:w3:hamfield-def@L164-L167", proof=f"{F}#bpW:w3:hamfield-def@L164-L167",
        H=SD + "; P as in Definition bpW:w3:hamfield-def", Q="real points; w, v",
        C="on real points Z^{-1} X_P = (d_p P, -d_q P), the convention of Definition bpW:w0:eqmotion; if P is real then "
          "X_P o rho = rho o X_P", S="none",
        note="Unlabelled paragraph after Definition bpW:w3:hamfield-def, cited as \"paragraph after Definition "
             "bpW:w3:hamfield-def\" in Steps stepW:w3:XG and stepW:w3:XKconcl.",
        deps=[("bpW:w3:hamfield-def", "L164", "the Hamiltonian field X_P"),
              ("bpW:w3:omega", "L165", "Omega(Zx,Zx') = sum (q p' - p q') and Omega(rho w, rho w') = conj Omega"),
              ("bpW:w0:eqmotion", "L165", "the sign convention of Hamilton's equations")]),
    "bpW:w3:real-restrict": dict(
        H=SD + "; U subset W open with rho U = U; V in {W, W+} with real form E_V in {E_{a,p}, E_{a,p+1}}; f : U -> V "
          "analytic with f o rho = rho o f; (second claim) P : U -> C analytic and real",
        Q="for all such U, V, f, P",
        C="f^R(x) = Z^{-1} f(Zx), x in Z^{-1}(U) cap E_{a,p}, takes values in E_V and is real analytic; x -> P(Zx) is real "
          "valued and real analytic", S="none",
        deps=[("bpW:w3:coords", "L182", "Z and the projection Pi are continuous R-linear"),
              ("bpW:w3:ext-series", "L180", "C-analytic is R-analytic; compositions")]),
    "bpW:w3:forms": dict(
        H=SD + "; d >= 2; P a continuous symmetric d-linear form on W", Q="P, c",
        C="defines: P is smoothing with constant c if there is a continuous (d-1)-linear nabla P : W^{d-1} -> W+ with "
          "P(w^1,..,w^{d-1},v) = Omega(nabla P(w^1,..),v) and ||nabla P(..)||_+ <= c prod ||w^i||; and records that then "
          "X_P(w) = d nabla P(w,..,w), ¦P(w)¦ <= c||w||^d, ||X_P(w)||_+ <= dc||w||^{d-1}, ||X_P(y) - X_P(w)||_+ <= "
          "d(d-1)c max(||y||,||w||)^{d-2} ||y - w||", S="none",
        deps=[("bpW:w3:omega", "L192", "the symplectic form"),
              ("bpW:w3:hamfield-def", "L194", "the Hamiltonian field X_P"),
              ("bpW:w3:ext-multilinear", "L194", "derivative of the diagonal of a multilinear map")]),
    "bpW:w3:Lambda": dict(
        H=SD, Q="for all w, v in W; w in W+ for the field; real x",
        C="Lambda(w) = sum_{j>=1} lambda_j w_j w_{-j} is a continuous quadratic form on W with ¦Lambda(w)¦ <= sqrt(1+m) "
          "||w||^2, Lambda(Zx) = (1/2) sum lambda_j (q_j^2 + p_j^2) for real x; DLambda(w)v = sum_{l != 0} lambda_¦l¦ "
          "w_{-l} v_l; for w in W+ its Hamiltonian field is X_Lambda(w)_l = -i lambda'_l w_l, bounded linear W+ -> W "
          "of norm <= sqrt(1+m); X_Lambda does not map W into itself", S="none",
        deps=[("bpW:w3:space", "L201", "W, W+ and lambda'"),
              ("bpW:w0:H", "L203", "the quadratic part of H"),
              ("bpW:w3:coords", "L202", "Z on real points"),
              ("bpW:w0:basis#lambda-facts", "L209", "lambda_j <= sqrt(1+m) j"),
              ("bpW:w3:hamfield-def", "L210", "the field from Definition bpW:w3:hamfield-def"),
              ("bpW:w1:diag", "L211", "(i) with r = 1: the operator bound")]),
    "bpW:w3:quartic-sec#data": dict(
        new=True, kind="definition", title="Two-sided quartic coefficients, divisors, pairing, tangential set",
        stmt=f"{F}#bpW:w3:quartic-sec@L224-L230", proof="-",
        H=SD + "; x in (Z\\0)^4", Q="x",
        C="defines ¦x¦, w_x = w_{x_1} w_{x_2} w_{x_3} w_{x_4}, frak g_x = g_¦x¦/sqrt(lambda_¦x_1¦ .. lambda_¦x_4¦), "
          "delta_x = lambda'_{x_1} + .. + lambda'_{x_4}; x paired iff a permutation of (r,-r,s,-s) (then delta_x = 0); "
          "T = {x : min_t ¦x_t¦ <= 2} (at least one tangential index)", S="none",
        note="Unlabelled prose L224-L230 fixing notation consumed throughout W3 (SPEC section-data rule).",
        deps=[("bpW:w0n:quartic-coeff", "L228", "g from Lemma bpW:w0n:quartic-coeff"),
              ("bpW:w3:space", "L227", "lambda'_l = sgn(l) lambda_¦l¦")]),
    "bpW:w3:majorant": dict(
        H=SD + "; nonnegative u, u', u'' in l^{a,p}; M(u,u',u'')_l = lambda_l^{-1/2} sum_{i,j,k} ¦g_ijkl¦ u_i u'_j u''_k/"
          "sqrt(lambda_i lambda_j lambda_k)", Q="for all such u, u', u''",
        C="the sums converge and ||M(u,u',u'')||_{a,p+1} <= C_* ||u|| ||u'|| ||u''||, C_* = K_{p+1/2}^2/pi; C_* does not "
          "depend on m; for a = p = 1, C_* = 8(1+2 zeta(3))/pi",
        S="C_* depends only on p (not on m, not on a)",
        deps=[("bpW:w0n:quartic-coeff", "L234", "the coefficients g_ijkl"),
              ("bpW:w0n:algebra", "L237", "K_s"),
              ("stepW:w0n:majorant", "L242", "the W0 majorant step applied to q = u"),
              ("stepW:w0n:selection", "L242", "the W0 selection step"),
              ("stepW:w0n:smoothing", "L242", "the W0 smoothing step")]),
    "bpW:w3:quartic": dict(
        H=SD + "; S subset (Z\\0)^4 invariant under permutations and x -> -x; c_x with c_x = c_{sigma x} = conj(c_{-x}) and "
          "¦c_x¦ <= ¦frak g_x¦; P(w^1..w^4) = (1/16) sum_{x in S} c_x w^1_{x_1} w^2_{x_2} w^3_{x_3} w^4_{x_4}",
        Q="for all such S, c",
        C="P converges absolutely, is continuous, symmetric, smoothing with constant C_*/4, with nabla P(w^1,w^2,w^3)_l = "
          "-(i sgn(l)/16) sum_{y : (y,-l) in S} c_{(y,-l)} w^1_{y_1} w^2_{y_2} w^3_{y_3}; its diagonal P is real; with "
          "c = frak g on (Z\\0)^4, T, T cap paired, T^c one obtains frak G, frak G^tan, bar frak G, frak G^nor and "
          "G, G^tan, bar G, G^nor; G = G^tan + G^nor; ||X_P(w)||_+ <= C_* ||w||^3, ¦P(w)¦ <= (C_*/4)||w||^4 for these P",
        S="C_* depends only on p",
        deps=[("bpW:w3:quartic-sec#data", "L250", "frak g, pairing and T"),
              ("bpW:w3:forms", "L252", "smoothing forms"),
              ("stepW:w3:maj", "L262", PS), ("stepW:w3:gradbound", "L266", PS), ("stepW:w3:identify", "L270", PS)]),
    "stepW:w3:maj": dict(H="", Q="w^1, w^2, w^3", C="with u^t_i = ¦w^t_i¦ + ¦w^t_{-i}¦, ||u^t||_{a,p} <= sqrt2 ||w^t|| and "
        "sum_y ¦frak g_{(y,-l)}¦ ¦w^1_{y_1} w^2_{y_2} w^3_{y_3}¦ <= M(u^1,u^2,u^3)_¦l¦", S="none",
        deps=[("bpW:w3:majorant", "L265", "the majorant M"), ("bpW:w3:quartic-sec#data", "L265", "frak g")]),
    "stepW:w3:gradbound": dict(H="", Q="w^1, w^2, w^3", C="||nabla P||_+ <= (C_*/4) prod ||w^t||", S="C_* depends only on p",
        deps=[("bpW:w3:majorant", "L267", "the bound C_*"), ("stepW:w3:maj", "L268", "the majorization")]),
    "stepW:w3:identify": dict(H="", Q="w^1, w^2, w^3, v", C="Omega(nabla P(w^1,w^2,w^3),v) = P(w^1,w^2,w^3,v); symmetry; "
        "reality P(rho w) = conj P(w); the bounds by Definition bpW:w3:forms with d = 4, c = C_*/4; frak g and the four "
        "sets are invariant; (Z\\0)^4 = T disjoint union T^c", S="none",
        deps=[("bpW:w3:omega", "L271", "the form Omega"), ("stepW:w3:maj", "L274", "absolute convergence"),
              ("bpW:w3:forms", "L276", "the bounds for d = 4"), ("stepW:w3:gradbound", "L276", "c = C_*/4"),
              ("bpW:w3:coords", "L275", "the involution rho")]),
    "bpW:w3:quartic-ident": dict(
        H=SD + "; real x = (q,p) in E_{a,p}", Q="for all real x; for all w in W; for x in T",
        C="G(Zx) = G(q) of Definition bpW:w0:H for a > 0 (definition of G on E_{0,p} for a = 0); Z^{-1} X_G(Zx) = "
          "(0,-T(q,q,q)), which is (0,-G_q(q)) for a > 0; G^nor(w) = G^nor(hat w), X_{G^nor} has vanishing tangential "
          "components, ¦G^nor(w)¦ <= (C_*/4)||hat w||^4, ||X_{G^nor}(w)||_+ <= C_*||hat w||^3; with I_j := w_j w_{-j}, "
          "bar G(w) = (1/2) sum_{i,j in J} A_ij I_i I_j + sum_{j>=3, i in J} B_ji I_i I_j (corrected A, B); x in T with "
          "frak g_x != 0 has delta_x = 0 iff x is paired", S="C_* depends only on p",
        deps=[("bpW:w3:quartic", "L283", "the forms G, G^nor, bar G"),
              ("bpW:w0:H", "L283", "G(q) of Definition bpW:w0:H"),
              ("bpW:w0n:cubic-bound", "L284", "the trilinear T"),
              ("bpW:w0n:AB", "L289", "the corrected A, B"),
              ("stepW:w3:Gz", "L294", PS), ("stepW:w3:XG", "L298", PS), ("stepW:w3:Gnor", "L302", PS),
              ("stepW:w3:count", "L304", PS), ("stepW:w3:res", "L309", PS)]),
    "stepW:w3:Gz": dict(H="", Q="real x", C="expanding prod (z + zbar) in (bpW:w0n:Gz) gives G(Zx) = (1/16) sum frak g_x "
        "w_x, absolutely convergent, and G(q) agrees with (bpW:w0n:Gz)", S="none",
        deps=[("bpW:w0n:birkhoff#data", "L295", "the identity (bpW:w0n:Gz)"),
              ("bpW:w3:quartic", "L296", "absolute convergence"),
              ("bpW:w0n:gradient", "L297", "G(q) as the quartic sum")]),
    "stepW:w3:XG": dict(H="", Q="real points", C="Z^{-1} X_G = (d_p G, -d_q G) with d_p G = 0 and d_{q_l} G = T(q,q,q)_l",
        S="none",
        deps=[("bpW:w3:hamfield-def#hamilton", "L299", "on real points Z^{-1} X_P = (d_p P, -d_q P)"),
              ("bpW:w0n:gradient", "L301", "d_{q_l} G = G_q(q)_l = T(q,q,q)_l"),
              ("bpW:w0n:cubic-bound", "L301", "the trilinear T")]),
    "stepW:w3:Gnor": dict(H="", Q="x in T^c", C="every x in T^c has all ¦x_t¦ >= 3, whence the normal-part claims",
        S="none", deps=[("bpW:w3:quartic-sec#data", "L303", "the set T")]),
    "stepW:w3:count": dict(H="", Q="1 <= r <= s, r in J", C="the paired terms contribute (3/(2 pi lambda_r lambda_s)) "
        "I_r I_s (r < s, 24 orderings) and (1/2) A_rr I_r^2 (r = s, 6 orderings): the coefficients of Theorem bpW:w0n:AB",
        S="none",
        deps=[("bpW:w0n:quartic-coeff", "L305", "g_rrss = 1/pi, g_rrrr = 3/(2pi)"),
              ("bpW:w0n:AB", "L308", "A and B")]),
    "stepW:w3:res": dict(H="", Q="x", C="frak g_x != 0 and delta_x = 0 force pairing", S="none",
        deps=[("bpW:w0n:nonres", "L310", "applied to the indices ¦x¦ with signs sgn x_t")]),
    "bpW:w3:divisor": dict(
        H=SD + "; n general in this lemma; x in (Z\\0)^4 satisfying the selection rule eps_1¦x_1¦ + .. + eps_4¦x_4¦ = 0 "
          "for some eps in {+-1}^4, x not paired; n = min_t ¦x_t¦", Q="for all such x",
        C="¦delta_x¦ >= m/(27 (n^2+m)^{3/2}); consequently, if x in T, frak g_x != 0 and x is not paired, ¦delta_x¦ >= "
          "delta_*(m) := m/(27 (4+m)^{3/2})", S="delta_* depends only on m",
        deps=[("bpW:w3:quartic-sec#data", "L318", "delta_x, pairing, T"),
              ("bpW:w0:basis#lambda-facts", "L327", "f'(s) = s/f(s) increasing, f'' = m/f^3 > 0 decreasing"),
              ("stepW:w3:sel", "L329", PS), ("stepW:w3:signs", "L333", PS), ("stepW:w3:s0", "L337", PS),
              ("stepW:w3:s1", "L339", PS), ("stepW:w3:s23", "L344", PS), ("stepW:w3:s1inner", "L349", PS),
              ("stepW:w3:divconcl", "L360", PS)]),
    "stepW:w3:sel": dict(H="", Q="a <= b <= c <= d sorted ¦x_t¦", C="d = a+b+c or d = b+c-a", S="none", deps=[]),
    "stepW:w3:signs": dict(H="", Q="sign patterns", C="WLOG at most two x_t negative; it suffices to bound the divisor of "
        "each sign pattern on (a,b,c,d)", S="none", deps=[]),
    "stepW:w3:s0": dict(H="", Q="none", C="with no minus sign delta >= 4 > beta", S="none",
        deps=[("bpW:w0:basis#lambda-facts", "L338", "lambda_k > k >= 1")]),
    "stepW:w3:s1": dict(H="", Q="none", C="with one minus sign the divisor is >= m/(2 lambda_a) >= beta", S="none",
        deps=[("stepW:w3:sel", "L343", "a + b + c >= d"),
              ("bpW:w0:basis#lambda-facts", "L340", "f(k) - k = m/(f(k)+k); lambda_c + c <= lambda_d + d")]),
    "stepW:w3:s23": dict(H="", Q="none", C="delta_3 = lambda_c + lambda_d - lambda_a - lambda_b and delta_2 = (lambda_b - "
        "lambda_a) + (lambda_d - lambda_c) vanish identically iff paired, and otherwise are >= a/lambda_a >= beta",
        S="none", deps=[("bpW:w0:basis#lambda-facts", "L346", "lambda_{k+1} - lambda_k >= f'(k) >= f'(a)")]),
    "stepW:w3:s1inner": dict(H="", Q="cases (i), (ii)", C="delta_1 = lambda_a + lambda_d - lambda_b - lambda_c is paired iff "
        "a = b, c = d, and otherwise >= beta: (i) d = b+c-a via f'' >= m/(27 lambda_a^3); (ii) d = a+b+c via "
        "2a f'(b) >= 2/sqrt(1+m) >= beta", S="none",
        deps=[("stepW:w3:sel", "L352", "the two cases d = b+c-a, d = a+b+c"),
              ("bpW:w0:basis#lambda-facts", "L353", "f' increasing, f'' = m/f^3")]),
    "stepW:w3:divconcl": dict(H="", Q="none", C="two-minus patterns are +-delta_1, +-delta_2, +-delta_3 and pairing "
        "coincides with identical vanishing; the corollary follows since frak g_x != 0 implies the selection rule, n <= 2 "
        "on T, and n -> m/(n^2+m)^{3/2} is decreasing", S="delta_* depends only on m",
        deps=[("stepW:w3:s0", "L361", "no minus sign"), ("stepW:w3:s1", "L361", "one minus sign"),
              ("stepW:w3:s23", "L361", "delta_2, delta_3"), ("stepW:w3:s1inner", "L361", "delta_1"),
              ("bpW:w0n:quartic-coeff", "L363", "frak g_x != 0 implies the selection rule")]),
    "bpW:w3:Fdef": dict(
        H=SD, Q="x; w^1..w^4",
        C="defines f_x = frak g_x/delta_x for x in T not paired, f_x = 0 otherwise (Lean: division by 0 is 0; Lemma "
          "bpW:w3:divisor guarantees delta_x != 0 where frak g_x != 0); frak F(w^1..w^4) = (i/16) sum_x f_x w^1_{x_1} .. "
          "w^4_{x_4}, F(w) = frak F(w,w,w,w), S = 4 nabla frak F : W^3 -> W+, X_F(w) = S(w,w,w)", S="none",
        deps=[("bpW:w3:quartic-sec#data", "L386", "frak g, delta, pairing, T"),
              ("bpW:w3:forms", "L390", "nabla of a form")]),
    "bpW:w3:F": dict(
        H=SD + "; frak F, F, S of Definition bpW:w3:Fdef", Q="for all w, w^i, v",
        C="frak F is a continuous symmetric 4-linear form, smoothing with constant C_*/(4 delta_*), F real; S is a "
          "continuous symmetric trilinear W^3 -> W+ with ||S(w^1,w^2,w^3)||_+ <= C_F prod ||w^i||, C_F = C_*/delta_*(m) = "
          "27 C_* (4+m)^{3/2}/m; Omega(S(w^1,w^2,w^3),v) = 4 frak F(w^1,w^2,w^3,v) symmetric in all four; S commutes with "
          "rho; ¦F(w)¦ <= (C_F/4)||w||^4; X_F is a cubic polynomial, analytic W -> W+", S="C_F depends on m and p",
        deps=[("bpW:w3:Fdef", "L397", "frak F, F, S"),
              ("stepW:w3:fcoef", "L406", PS), ("stepW:w3:Fconcl", "L410", PS)]),
    "stepW:w3:fcoef": dict(H="", Q="x", C="f is permutation invariant, f_{-x} = -f_x, ¦f_x¦ <= ¦frak g_x¦/delta_*; "
        "c_x := i delta_* f_x satisfies the hypotheses of Lemma bpW:w3:quartic and frak F = delta_*^{-1} P_c", S="none",
        deps=[("bpW:w3:divisor", "L408", "¦delta_x¦ >= delta_*"), ("bpW:w3:quartic", "L408", "its coefficient hypotheses")]),
    "stepW:w3:Fconcl": dict(H="", Q="none", C="smoothing with constant C_*/(4 delta_*) and reality; S = 4 nabla frak F "
        "gives C_F; reality of S; analyticity of X_F", S="C_F depends on m and p",
        deps=[("bpW:w3:quartic", "L411", "smoothing and reality of P_c"), ("stepW:w3:fcoef", "L411", "frak F = P_c/delta_*"),
              ("bpW:w3:hamfield-def", "L413", "reality of the field from reality of the form"),
              ("bpW:w3:ext-series", "L413", "polynomials are analytic")]),
    "bpW:w3:homological": dict(
        H=SD + "; Z' = bar G - G^tan, the diagonal of frak z = bar frak G - frak G^tan", Q="for every w in W",
        C="frak z is a form as in Lemma bpW:w3:quartic, smoothing with constant C_*/4, ||X_{Z'}(w)||_+ <= C_*||w||^3; "
          "DLambda(w) X_F(w) = Z'(w), equivalently G + DLambda . X_F = bar G + G^nor", S="C_* depends only on p",
        deps=[("bpW:w3:quartic", "L418", "the forms bar frak G, frak G^tan and their bounds"),
              ("stepW:w3:Xfcoord", "L425", PS), ("stepW:w3:euler", "L428", PS), ("stepW:w3:divide", "L434", PS)]),
    "stepW:w3:Xfcoord": dict(H="", Q="w, l", C="X_F(w)_l = 4 nabla frak F(w,w,w)_l = (sgn(l)/4) sum_y f_{(y,-l)} w_y",
        S="none", deps=[("bpW:w3:Fdef", "L426", "S = 4 nabla frak F"), ("bpW:w3:quartic", "L426", "the formula for nabla")]),
    "stepW:w3:euler": dict(H="", Q="w", C="DLambda(w) X_F(w) = -(1/16) sum_x delta_x f_x w_x, all series absolutely "
        "convergent", S="none",
        deps=[("bpW:w3:Lambda", "L429", "DLambda(w)v"), ("stepW:w3:Xfcoord", "L429", "the coordinates of X_F"),
              ("bpW:w3:F", "L433", "||X_F(w)||_+ < infinity"),
              ("bpW:w0:basis#lambda-facts", "L432", "lambda_¦l¦ <= sqrt(1+m) ¦l¦^{p+1} e^{a¦l¦}")]),
    "stepW:w3:divide": dict(H="", Q="w", C="delta_x f_x = frak g_x on T \\ paired and 0 else, so the sum is bar G - G^tan; "
        "with G = G^tan + G^nor the second form", S="none",
        deps=[("stepW:w3:euler", "L436", "the sum"), ("bpW:w3:divisor", "L436", "delta_x != 0 where frak g_x != 0"),
              ("bpW:w3:quartic", "L437", "the forms and G = G^tan + G^nor")]),
    "bpW:w3:lie-coeff": dict(
        H=SD + "; S of Definition bpW:w3:Fdef", Q="k >= 0",
        C="defines the continuous (2k+1)-linear Phi_k : W^{2k+1} -> W by Phi_0(w) = w and the recursion Phi_{k+1}(w^1.."
          "w^{2k+3}) = (1/(k+1)) sum_{i=1}^{2k+1} Phi_k(w^1,..,w^{i-1},S(w^i,w^{i+1},w^{i+2}),w^{i+3},..), phi_k(w) = "
          "Phi_k(w,..,w), and (LQ)(w) = DQ(w) X_F(w) for C^1 maps Q", S="none",
        deps=[("bpW:w3:Fdef", "L453", "S and X_F")]),
    "bpW:w3:leibniz": dict(
        H=SD + "; Phi_k, phi_k, L of Definition bpW:w3:lie-coeff", Q="for all k >= 0",
        C="(i) phi_{k+1} = L phi_k/(k+1), phi_k = L^k(id)/k!; (ii) ||Phi_k|| <= (2C_F)^k and for k >= 1 Phi_k takes values "
          "in W+ with ||Phi_k||_{W^{2k+1} -> W+} <= (2C_F)^k; (iii) Phi_k commutes with rho; (iv) (k+1) phi_{k+1} = "
          "sum_{a+b+c=k} S(phi_a,phi_b,phi_c) and (k+1) D phi_{k+1}(w)v = sum_{a+b+c=k} 3 S(D phi_a(w)v, phi_b(w), "
          "phi_c(w))", S="C_F depends on m and p",
        deps=[("bpW:w3:lie-coeff", "L463", "Phi_k, phi_k, L"),
              ("stepW:w3:rec", "L473", PS), ("stepW:w3:norms", "L476", PS), ("stepW:w3:Phireal", "L481", PS),
              ("stepW:w3:leib", "L483", PS), ("stepW:w3:leibid", "L487", PS)]),
    "stepW:w3:rec": dict(H="", Q="k", C="(i): D phi_k(w)v = sum_i Phi_k(w,..,v,..,w) with v = S(w,w,w)", S="none",
        deps=[("bpW:w3:ext-multilinear", "L474", "derivative of the diagonal"), ("bpW:w3:lie-coeff", "L475", "the recursion")]),
    "stepW:w3:norms": dict(H="", Q="k", C="(ii): ||Phi_{k+1}|| <= 2 C_F ||Phi_k|| in W and in W+", S="C_F depends on m and p",
        deps=[("bpW:w3:ext-multilinear", "L477", "norms of inserted multilinear maps"),
              ("bpW:w3:F", "L477", "||S|| <= C_F"), ("bpW:w3:lie-coeff", "L479", "Phi_1 = S and the recursion")]),
    "stepW:w3:Phireal": dict(H="", Q="k", C="(iii) by induction", S="none",
        deps=[("bpW:w3:F", "L482", "S commutes with rho")]),
    "stepW:w3:leib": dict(H="", Q="n", C="for continuous multilinear B and C^infinity Q_i, L B(Q_1..Q_r) = sum_i B(..,LQ_i,..) "
        "and the multinomial formula for L^n B(Q_1..Q_r)", S="none",
        deps=[("bpW:w3:ext-multilinear", "L484", "product and chain rules for multilinear maps")]),
    "stepW:w3:leibid": dict(H="", Q="k", C="(iv): (k+1)! phi_{k+1} = L^k(S(id,id,id)) = sum_{a+b+c=k} (k!/(a!b!c!)) "
        "S(a! phi_a, b! phi_b, c! phi_c), and the derivative identity by symmetry of S", S="none",
        deps=[("stepW:w3:rec", "L489", "(i)"), ("stepW:w3:leib", "L489", "the Leibniz rule"),
              ("bpW:w3:F", "L490", "symmetry of S")]),
    "bpW:w3:flow": dict(
        H=SD + "; rho_0 = rho_0(m) = (40 C_F)^{-1/2}, B_rho = {w : ||w|| < rho}; Gamma_t(w) = sum_k t^k phi_k(w) for real "
          "¦t¦ < 2, w in B_{rho_0}; r = 2¦t¦ C_F ||w||^2 <= 1/10; (vi) rho_1 = rho_0/2",
        Q="for real ¦t¦ < 2 and w in B_{rho_0} ((vi): ¦t¦ <= 1, w in B_{rho_1})",
        C="(i) the series converges absolutely, w -> Gamma_t(w) has the power series (t^k Phi_k) on B_{rho_0} and is "
          "analytic, Gamma_t - id is analytic B_{rho_0} -> W+, (t,w) -> Gamma_t(w) is C^1; (ii) Gamma_0 = id, d_t Gamma_t = "
          "X_F(Gamma_t) and d_t Gamma_t = D Gamma_t X_F; (iii) ||Gamma_t(w)|| <= (10/9)||w||, ||Gamma_t(w) - w||_+ <= "
          "3¦t¦C_F||w||^3, ||D Gamma_t(w) - I||_{W -> W+} <= 10¦t¦C_F||w||^2 <= 1/2, D Gamma_t(w) maps W+ into itself, is "
          "invertible on W and W+ with inverses of norm <= 2 and ||D Gamma_t^{-1} - I||_{W -> W+} <= 20¦t¦C_F||w||^2; (iv) "
          "Gamma_t(rho w) = rho Gamma_t(w); (v) d_t D Gamma_t(w)v = DX_F(Gamma_t(w)) D Gamma_t(w)v, DX_F(y)xi = 3S(y,y,xi); "
          "(vi) Gamma_{-t}(Gamma_t(w)) = w, Gamma = Gamma_1 is injective on B_{rho_1}, Gamma(B_{rho_1}) subset "
          "B_{10 rho_1/9} and Gamma(B_{rho_1}) contains B_{9 rho_1/10}", S="rho_0, rho_1 depend on m and p",
        deps=[("bpW:w3:lie-coeff", "L497", "phi_k"), ("bpW:w3:F", "L495", "C_F"),
              ("stepW:w3:conv", "L520", PS), ("stepW:w3:floweq", "L528", PS), ("stepW:w3:transport", "L532", PS),
              ("stepW:w3:est", "L535", PS), ("stepW:w3:Greal", "L542", PS), ("stepW:w3:var", "L544", PS),
              ("stepW:w3:inv", "L548", PS)]),
    "stepW:w3:conv": dict(H="", Q="t, w", C="¦t¦^k ||phi_k(w)|| <= r^k ||w||, r <= 1/10; the formal series with "
        "coefficients t^k Phi_k gives analyticity in W and (k >= 1) in W+; termwise derivatives in (t,w) are summable, "
        "giving joint C^1", S="none",
        deps=[("bpW:w3:leibniz", "L521", "(ii) the coefficient bounds"),
              ("bpW:w3:ext-series", "L524", "power series give analyticity"),
              ("bpW:w3:ext-tsum", "L527", "termwise differentiation")]),
    "stepW:w3:floweq": dict(H="", Q="t, w", C="d_t Gamma_t = S(Gamma_t,Gamma_t,Gamma_t) = X_F(Gamma_t)", S="none",
        deps=[("bpW:w3:leibniz", "L530", "(iv)"), ("bpW:w3:ext-tsum", "L531", "Cauchy product"),
              ("stepW:w3:conv", "L529", "termwise derivative")]),
    "stepW:w3:transport": dict(H="", Q="t, w", C="d_t Gamma_t = D Gamma_t X_F", S="none",
        deps=[("bpW:w3:leibniz", "L534", "(i)"), ("stepW:w3:conv", "L534", "termwise derivatives")]),
    "stepW:w3:est": dict(H="", Q="t, w", C="the bounds of (iii) and the inverses", S="none",
        deps=[("bpW:w3:leibniz", "L537", "(ii)"), ("bpW:w3:ext-neumann", "L540", "Neumann series"),
              ("stepW:w3:conv", "L536", "r <= 1/10")]),
    "stepW:w3:Greal": dict(H="", Q="t real", C="(iv) termwise", S="none", deps=[("bpW:w3:leibniz", "L543", "(iii)")]),
    "stepW:w3:var": dict(H="", Q="t, w, v", C="d_t D Gamma_t v = 3S(D Gamma_t v, Gamma_t, Gamma_t)", S="none",
        deps=[("bpW:w3:leibniz", "L545", "(iv)"), ("bpW:w3:ext-tsum", "L545", "Cauchy product"),
              ("stepW:w3:conv", "L546", "termwise derivative")]),
    "stepW:w3:inv": dict(H="", Q="¦t¦ <= 1, w in B_{rho_1}", C="psi(s) = Gamma_{-s}(Gamma_s(w)) is C^1 with derivative 0, "
        "so Gamma_{-t}(Gamma_t(w)) = w; injectivity and the image inclusions", S="none",
        deps=[("stepW:w3:est", "L549", "||Gamma_s(w)|| <= (10/9)||w||"), ("stepW:w3:conv", "L550", "C^1"),
              ("stepW:w3:transport", "L552", "transport equation"), ("stepW:w3:floweq", "L552", "flow equation"),
              ("bpW:w3:ext-mvt", "L553", "zero derivative implies constant")]),
    "bpW:w3:symplectic": dict(
        H=SD + "; ¦t¦ < 2, w in B_{rho_0}, xi, eta in W; (consequence) P complex differentiable near Gamma_t(B_rho), "
          "rho <= rho_0, with Hamiltonian field X_P", Q="for all such t, w, xi, eta; P; w in B_rho",
        C="Omega(D Gamma_t(w) xi, D Gamma_t(w) eta) = Omega(xi,eta); P o Gamma_t has Hamiltonian field X_{P o Gamma_t}(w) = "
          "D Gamma_t(w)^{-1} X_P(Gamma_t(w)), with values in W+ when X_P has", S="none",
        deps=[("bpW:w3:flow", "L570", "Gamma_t and rho_0"), ("bpW:w3:hamfield-def", "L573", "Hamiltonian fields"),
              ("stepW:w3:skew", "L579", PS), ("stepW:w3:constform", "L583", PS), ("stepW:w3:gradtrans", "L588", PS)]),
    "stepW:w3:skew": dict(H="", Q="y, xi, eta", C="Omega(DX_F(y)xi,eta) + Omega(xi,DX_F(y)eta) = 0", S="none",
        deps=[("bpW:w3:F", "L581", "Omega(S(.),v) = 4 frak F symmetric"), ("bpW:w3:omega", "L582", "antisymmetry"),
              ("bpW:w3:flow", "L580", "(v): DX_F(y) xi = 3 S(y,y,xi)")]),
    "stepW:w3:constform": dict(H="", Q="t", C="g(t) = Omega(D Gamma_t xi, D Gamma_t eta) has g' = 0 and g(0) = Omega(xi,eta)",
        S="none", deps=[("bpW:w3:flow", "L586", "(v) variational equation; D Gamma_0 = I"),
                        ("stepW:w3:skew", "L586", "skewness"), ("bpW:w3:ext-mvt", "L587", "zero derivative")]),
    "stepW:w3:gradtrans": dict(H="", Q="w, v", C="D(P o Gamma_t)(w)v = Omega(D Gamma_t^{-1} X_P(Gamma_t w), v); values in W+ "
        "by invertibility on W+", S="none",
        deps=[("bpW:w3:flow", "L591", "(iii) invertibility on W and W+"), ("stepW:w3:constform", "L592", "constant form")]),
    "bpW:w3:main-sec#data": dict(
        new=True, kind="definition", title="H = Lambda + G on W and the integrand Y(t,w)",
        stmt=f"{F}#bpW:w3:main-sec@L598-L609", proof="-",
        H=SD, Q="0 <= t <= 1, w in B_{rho_1}",
        C="defines H = Lambda + G on W (on real points the Hamiltonian of Definition bpW:w0:H), X_H = X_Lambda + X_G on W+ "
          "with values in W, and (bpW:w3:Ydef) Y(t,w) = D Gamma_t(w)^{-1} X_{Z'}(Gamma_t w) - X_{Z'}(w) in W+, Z' = bar G - "
          "G^tan, rho_1 = (1/2)(40 C_F)^{-1/2}, D Gamma_t(w)^{-1} the inverse on W+", S="none",
        note="Unlabelled prose L598-L609 (with the display bpW:w3:Ydef) fixing H, X_H and Y used by Lemma bpW:w3:Yseries "
             "and Theorem bpW:w3:main (SPEC section-data rule).",
        deps=[("bpW:w3:Lambda", "L598", "Lambda finite, X_Lambda on W+"), ("bpW:w3:quartic", "L598", "G finite, X_G"),
              ("bpW:w0:H", "L599", "the Hamiltonian on real points"),
              ("bpW:w3:homological", "L605", "Z' = bar G - G^tan and X_{Z'}"),
              ("bpW:w3:flow", "L607", "(iii) the inverse of D Gamma_t on W+")]),
    "bpW:w3:Yseries": dict(
        H=SD + "; Y(t,w) of (bpW:w3:Ydef), rho_1 = (1/2)(40 C_F)^{-1/2}",
        Q="there exist Y_j (j >= 0); then for 0 <= t <= 1 and w in B_{rho_1}",
        C="there are continuous (2j+3)-linear Y_j : W^{2j+3} -> W+ with sum ||Y_j|| rho_1^{2j+3} <= 4 C_* rho_1^3 and "
          "Y(t,w) = sum t^j Y_j(w,..,w) absolutely; int_0^1 Y(t,w) dt = sum Y_j(w,..,w)/(j+1); w -> int_0^1 Y dt has the "
          "formal power series q (q_{2j+3} = Y_j/(j+1), else 0) on B_{rho_1} and is analytic B_{rho_1} -> W+; "
          "int_0^1 Y(t,rho w) dt = rho int_0^1 Y(t,w) dt", S="C_* depends only on p; rho_1 on m, p",
        deps=[("bpW:w3:main-sec#data", "L613", "the integrand Y"),
              ("stepW:w3:majcalc", "L623", PS), ("stepW:w3:majflow", "L635", PS), ("stepW:w3:majA", "L638", PS),
              ("stepW:w3:majN", "L645", PS), ("stepW:w3:majX", "L652", PS), ("stepW:w3:majY", "L656", PS),
              ("stepW:w3:majint", "L662", PS), ("stepW:w3:majps", "L666", PS), ("stepW:w3:majreal", "L669", PS)]),
    "stepW:w3:majcalc": dict(H="", Q="(t,w)-series P^i, multilinear B", C="majorant calculus: composite series have "
        "mu_{B(P^1..P^n)} <= ||B|| prod mu_{P^i} and sum to B(P^1(t,w),..); sums add coefficientwise; graded series and "
        "shifts", S="none",
        deps=[("bpW:w3:ext-multilinear", "L630", "norms of composites"), ("bpW:w3:ext-tsum", "L631", "regrouping")]),
    "stepW:w3:majflow": dict(H="", Q="s, rho", C="the series Gamma (shift 1) sums to Gamma_t(w) with mu_Gamma <= rho/(1-r)",
        S="none", deps=[("bpW:w3:flow", "L636", "Gamma_t"), ("bpW:w3:leibniz", "L637", "(ii)"),
                        ("stepW:w3:majcalc", "L636", "(t,w)-series")]),
    "stepW:w3:majA": dict(H="", Q="k >= 1", C="A_{k,2k} with ||A_{k,2k}|| <= (2k+1)(2C_F)^k, mu_A <= 5r <= 1/16, sums to "
        "D Gamma_t(w) - I on W+", S="none",
        deps=[("bpW:w3:leibniz", "L641", "(ii)"), ("stepW:w3:est", "L643", "sum (2k+1) r^k <= 5r"),
              ("bpW:w3:ext-multilinear", "L643", "derivative of the diagonal"),
              ("bpW:w3:flow", "L644", "(i) termwise derivative")]),
    "stepW:w3:majN": dict(H="", Q="none", C="N = sum_n (-A)^n regrouped is a graded series (shift 0) with mu_N <= 16/15 "
        "summing to D Gamma_t(w)^{-1} on W+", S="none",
        deps=[("stepW:w3:majA", "L647", "mu_A <= 1/16"), ("stepW:w3:majcalc", "L647", "composite series"),
              ("bpW:w3:ext-tsum", "L649", "regrouping"), ("bpW:w3:ext-neumann", "L650", "Neumann series")]),
    "stepW:w3:majX": dict(H="", Q="none", C="4 nabla frak z(Gamma,Gamma,Gamma) has majorant <= C_* rho^3 (1-r)^{-3}, sums "
        "to X_{Z'}(Gamma_t w), shift 3", S="none",
        deps=[("bpW:w3:quartic", "L653", "4 nabla frak z trilinear of norm <= C_*"),
              ("stepW:w3:majflow", "L654", "the series Gamma"), ("stepW:w3:majcalc", "L654", "composites")]),
    "stepW:w3:majY": dict(H="", Q="none", C="the composite series cal Y sums to Y(t,w), has shift 3 and mu_Y(1,rho_1) <= "
        "4 C_* rho_1^3; Y_j = cal Y_{j,2j+3}", S="C_* depends only on p",
        deps=[("stepW:w3:majN", "L658", "N"), ("stepW:w3:majX", "L658", "the cubic field along the flow"),
              ("bpW:w3:main-sec#data", "L659", "Y(t,w)")]),
    "stepW:w3:majint": dict(H="", Q="w", C="termwise integration in t: int_0^1 Y dt = sum Y_j(w,..,w)/(j+1)", S="none",
        deps=[("stepW:w3:majY", "L664", "the bounds on Y_j"), ("bpW:w3:ext-integral", "L664", "termwise integration")]),
    "stepW:w3:majps": dict(H="", Q="none", C="sum ||q_n|| rho_1^n < infinity, so the formal power series and analyticity",
        S="none", deps=[("stepW:w3:majY", "L667", "sum ||Y_j|| rho_1^{2j+3}"),
                        ("bpW:w3:ext-series", "L667", "power series give analyticity")]),
    "stepW:w3:majreal": dict(H="", Q="t real", C="Y(t, rho w) = rho Y(t,w) and rho commutes with the t-integral", S="none",
        deps=[("bpW:w3:flow", "L670", "(iv) reality of Gamma_t"), ("bpW:w3:hamfield-def", "L671", "X_{Z'} commutes with rho"),
              ("bpW:w3:ext-integral", "L672", "continuous R-linear maps commute with the integral")]),
    "bpW:w3:main": dict(
        H=SD + "; Gamma = Gamma_1, rho_1 = rho_1(m) = (1/2)(40 C_F(m))^{-1/2}; H = Lambda + G; K = H o Gamma - Lambda - "
          "bar G - G^nor on B_{rho_1}", Q="for all w in B_{rho_1} ((iv): w in B_{rho_1} cap W+)",
        C="(i) K is analytic on B_{rho_1} and real, ¦K(w)¦ <= C_K ||w||^6, C_K = 10 C_* C_F; (ii) K in A(B_{rho_1}): X_K is "
          "analytic B_{rho_1} -> W+, real, ||X_K(w)||_+ <= C'_K ||w||^5, C'_K = 66 C_* C_F; X_K^R = Z^{-1} X_K o Z is real "
          "analytic B^E_{r_1} -> E_{a,p+1} (r_1 = rho_1/sqrt2) and equals (d_p K^R, -d_q K^R) for K^R = K o Z; (iii) bar G "
          "= (1/2)<AI,I> + <BI,Z> with the corrected coefficients, G^nor depends only on hat w, ¦G^nor¦ <= (C_*/4)"
          "||hat w||^4, both in A(W) with cubic fields bounded by C_*||w||^3 (C_*||hat w||^3); (iv) for w in B_{rho_1} cap "
          "W+, Gamma(w) in W+ and D Gamma(w)[X_Lambda(w) + X_{bar G}(w) + X_{G^nor}(w) + X_K(w)] = X_H(Gamma(w))",
        S="C_K, C'_K, rho_1 depend on m and p",
        deps=[("bpW:w3:main-sec#data", "L679", "H = Lambda + G"), ("bpW:w3:flow", "L678", "Gamma = Gamma_1"),
              ("bpW:w3:hamfield-def", "L683", "the class A"),
              ("stepW:w3:Kanalytic", "L700", PS), ("stepW:w3:K1", "L704", PS), ("stepW:w3:K2", "L708", PS),
              ("stepW:w3:XK1", "L714", PS), ("stepW:w3:XK2", "L722", PS), ("stepW:w3:XKconcl", "L732", PS),
              ("stepW:w3:iii", "L737", PS), ("stepW:w3:conj", "L739", PS)]),
    "stepW:w3:Kanalytic": dict(H="", Q="none", C="K is analytic on B_{rho_1} and real", S="none",
        deps=[("bpW:w3:flow", "L702", "(i) Gamma analytic; (iv) reality"), ("bpW:w3:ext-series", "L702", "compositions"),
              ("bpW:w3:Lambda", "L701", "Lambda a continuous polynomial"), ("bpW:w3:quartic", "L701", "G, bar G, G^nor polynomials")]),
    "stepW:w3:K1": dict(H="", Q="w", C="¦K_1(w)¦ = ¦G(Gamma w) - G(w)¦ <= 5 C_* C_F ||w||^6", S="none",
        deps=[("bpW:w3:ext-mvt", "L706", "mean value inequality on the segment"),
              ("bpW:w3:flow", "L707", "(iii) estimates"), ("bpW:w3:quartic", "L706", "||X_G(y)||_+ <= C_*||y||^3"),
              ("bpW:w3:omega", "L706", "DG(y)v = Omega(X_G(y),v)")]),
    "stepW:w3:K2": dict(H="", Q="w", C="h(t) = Lambda(Gamma_t w) - Lambda(w) - t Z'(w) has h(0) = 0, h'(t) = Z'(Gamma_t w) - "
        "Z'(w), ¦h'(t)¦ <= 5 C_* C_F t ||w||^6, so ¦K_2(w)¦ <= 5 C_* C_F ||w||^6; with K_1, (i)", S="none",
        deps=[("bpW:w3:flow", "L710", "(ii) flow equation"), ("bpW:w3:homological", "L710", "DLambda . X_F = Z' at Gamma_t w"),
              ("stepW:w3:K1", "L712", "the same mean value argument"), ("stepW:w3:Kanalytic", "L713", "(i) analyticity part")]),
    "stepW:w3:XK1": dict(H="", Q="w", C="X_{K_1}(w) = D Gamma^{-1} X_G(Gamma w) - X_G(w), ||X_{K_1}(w)||_+ <= 44 C_* C_F "
        "||w||^5, analytic into W+", S="none",
        deps=[("bpW:w3:symplectic", "L715", "gradient transport"), ("bpW:w3:forms", "L717", "Lipschitz bound d = 4"),
              ("bpW:w3:flow", "L717", "(iii)"), ("bpW:w3:ext-series", "L720", "analyticity of D(Gamma - id), inversion")]),
    "stepW:w3:XK2": dict(H="", Q="w", C="K_2(w) = int_0^1 (Z'(Gamma_t w) - Z'(w)) dt, X_{K_2}(w) = int_0^1 Y(t,w) dt with "
        "||X_{K_2}(w)||_+ <= 22 C_* C_F ||w||^5, analytic B_{rho_1} -> W+", S="none",
        deps=[("bpW:w3:ext-integral", "L723", "FTC and differentiation under the integral"),
              ("stepW:w3:K2", "L723", "h'(t)"), ("bpW:w3:symplectic", "L725", "gradient transport"),
              ("bpW:w3:main-sec#data", "L726", "Y of (bpW:w3:Ydef)"), ("stepW:w3:XK1", "L726", "the same bound"),
              ("bpW:w3:Yseries", "L727", "D_w Y bounded; analyticity of the integral")]),
    "stepW:w3:XKconcl": dict(H="", Q="none", C="(ii): X_K = X_{K_1} + X_{K_2}, 44 + 22 = 66, analytic; reality; the real "
        "restriction and (d_p K^R, -d_q K^R)", S="none",
        deps=[("stepW:w3:XK1", "L733", "X_{K_1}"), ("stepW:w3:XK2", "L733", "X_{K_2}"),
              ("bpW:w3:hamfield-def", "L734", "reality of the field"), ("bpW:w3:real-restrict", "L734", "real restriction"),
              ("bpW:w3:hamfield-def#hamilton", "L735", "Z^{-1} X_K = (d_p K, -d_q K) on real points"),
              ("bpW:w3:coords", "L736", "||Zx|| <= sqrt2 ||x||_E")]),
    "stepW:w3:iii": dict(H="", Q="none", C="(iii) from Lemmas bpW:w3:quartic and bpW:w3:quartic-ident", S="none",
        deps=[("bpW:w3:quartic", "L738", "forms and bounds"), ("bpW:w3:quartic-ident", "L738", "bar G, G^nor")]),
    "stepW:w3:conj": dict(H="", Q="w in B_{rho_1} cap W+", C="(iv): Gamma(w) in W+ and D Gamma(w)[X_Lambda + X_{bar G} + "
        "X_{G^nor} + X_K](w) = X_H(Gamma(w))", S="none",
        deps=[("bpW:w3:flow", "L740", "Gamma - id into W+"), ("bpW:w3:Lambda", "L741", "DH(y)u = Omega(X_H(y),u) on W+"),
              ("bpW:w3:symplectic", "L742", "gradient transport"), ("bpW:w3:omega", "L745", "nondegeneracy"),
              ("stepW:w3:XKconcl", "L744", "X_K")]),
    "bpW:w3:gamma-real": dict(
        H=SD + "; r_1 = rho_1/sqrt2, B^E_r = {x in E_{a,p} : ||x||_E < r}; Gamma^R = Z^{-1} o Gamma o Z", Q="x in B^E_{r_1}",
        C="Gamma^R : B^E_{r_1} -> E_{a,p} is well defined and (i) real analytic with the real power series of terms "
          "Z^{-1} Phi_k(Z.,..,Z.); (ii) ||Gamma^R(x) - x||_{E_{a,p+1}} <= 6 sqrt2 C_F ||x||_E^3 and Gamma^R(B^E_{r_1}) "
          "subset B^E_{2r_1}; (iii) symplectic for sum dq ^ dp, injective, inverse Z^{-1} Gamma_{-1} Z on its image, image "
          "contains B^E_{r_1/2}; (iv) H(Gamma^R x) = Lambda(x) + bar G(x) + G^nor(x) + K(Zx) with bar G = (1/2)<AI,I> + "
          "<BI,Z>, I_j = (q_j^2+p_j^2)/2", S="C_F, r_1 depend on m and p",
        deps=[("bpW:w3:flow", "L787", "(iii), (iv), (vi)"), ("bpW:w3:coords", "L788", "Z and real points"),
              ("bpW:w3:leibniz", "L789", "(iii) reality of Phi_k"), ("bpW:w3:ext-series", "L791", "analyticity over R"),
              ("bpW:w3:omega", "L792", "the real form"), ("bpW:w3:symplectic", "L793", "symplecticity"),
              ("bpW:w3:main", "L795", "(iv) the normal form"), ("bpW:w3:quartic-ident", "L795", "bar G on real points")]),
    "bpW:w3:transport-tori": dict(
        H=SD + "; nu in R^2; Psi : R^2 -> B_{rho_1} cap W+ differentiable into W with D Psi(theta) nu = X_{H'}(Psi(theta)), "
          "X_{H'} = X_Lambda + X_{bar G} + X_{G^nor} + X_K; for the last claim Psi real (rho Psi = Psi)",
        Q="for all such nu, Psi; all theta; j >= 1",
        C="Gamma o Psi takes values in W+ and D(Gamma o Psi)(theta) nu = X_H(Gamma o Psi(theta)); if Psi is real, (Q,P) = "
          "Z^{-1} Gamma o Psi satisfies D_nu Q_j = lambda_j P_j, D_nu P_j = -lambda_j Q_j - T(Q,Q,Q)_j, the coefficient "
          "system (bpW:w0:coeffsys) (T = G_q for a > 0)", S="none",
        deps=[("bpW:w3:main", "L810", "(iv) conjugacy"), ("bpW:w3:Lambda", "L812", "X_Lambda on real points"),
              ("bpW:w3:quartic-ident", "L812", "Z^{-1} X_G = (0,-T(q,q,q))"),
              ("bpW:w0:eqmotion", "L806", "the coefficient system")]),
}

DELETE = ["bpW:w3:ext-flows", "bpW:w3:w1-requests", "bpW:w3:class-remark", "bpW:w3:interface"]

COV = {
    "bpW:w3:ext-flows": ("EXCLUDED", "remark stating what Mathlib does not provide and that W3 does not use Lemma "
                         "bpW:w1:flow or ODE uniqueness; not an external input"),
    "bpW:w3:w1-requests": ("EXCLUDED", "administrative remark (requests to W1)"),
    "bpW:w3:class-remark": ("EXCLUDED", "administrative remark (summary of the regularity class; the facts are proved "
                            "in Theorems bpW:w3:flow, bpW:w3:main and Lemma bpW:w3:Yseries)"),
    "bpW:w3:interface": ("EXCLUDED", "administrative remark (what W3 supplies to W4-W6); no wave-1 proof consumes it; "
                         "re-examine when W4-W6 are added"),
    "w3-birkhoff:sourcegap-L366": ("NODE stepW:w3:s1, stepW:w3:s23, stepW:w3:s1inner", "two incorrect steps of P96-W "
                                   "Lemma 4's printed proof; the blueprint's own proof repairs them (constant 1/27)"),
    "w3-birkhoff:sourcegap-L750": ("NODE stepW:w3:K2, stepW:w3:XK2", "P96-W leaves implicit the application of its "
                                   "conditional facts to the remainder; the blueprint gives it via the homological "
                                   "identity"),
    "w3-birkhoff:prose-L3-L13": ("EXCLUDED", "introduction and outline"),
    "w3-birkhoff:prose-L15-L21": ("EXCLUDED", "route paragraph (outline)"),
    "w3-birkhoff:prose-L23-L27": ("NODE bpW:w3#data", "standing data of W3 (a >= 0, p >= 1/2, J)"),
    "w3-birkhoff:prose-L29-L33": ("EXCLUDED", "pointer to the W1 inputs (each use is an edge at its consumer)"),
    "w3-birkhoff:prose-L38-L39": ("EXCLUDED", "introduction of the external list"),
    "w3-birkhoff:prose-L164-L167": ("NODE bpW:w3:hamfield-def#hamilton", "Hamilton's equations on real points and "
                                    "reality of X_P, consumed by Steps stepW:w3:XG, stepW:w3:XKconcl"),
    "w3-birkhoff:prose-L224-L230": ("NODE bpW:w3:quartic-sec#data", "notation frak g, delta, pairing, T"),
    "w3-birkhoff:prose-L377-L381": ("EXCLUDED", "unlabelled remark (sharpness and asymptotics of delta_*); no proof "
                                    "consumes it"),
    "w3-birkhoff:prose-L443-L447": ("EXCLUDED", "unlabelled remark (why the identity is stated with DLambda); no proof "
                                    "consumes it"),
    "w3-birkhoff:prose-L563-L567": ("EXCLUDED", "unlabelled remark (identification with the ODE solution, explicitly "
                                    "not used)"),
    "w3-birkhoff:prose-L598-L600": ("NODE bpW:w3:main-sec#data", "H = Lambda + G on W and X_H"),
    "w3-birkhoff:prose-L602-L609": ("NODE bpW:w3:main-sec#data", "the integrand Y(t,w) (bpW:w3:Ydef)"),
    "w3-birkhoff:prose-L867-L887": ("EXCLUDED", "constants table and Lean totality notes (summary; each constant is "
                                    "defined and bounded in its result)"),
    "w3-birkhoff:prose-L891-L904": ("EXCLUDED", "status summary (administrative)"),
}

for _k, _src in {'w3-birkhoff:sourcegap-L366': 'blueprint-W/parts/w3-birkhoff.tex#sourcegap@L366-L375', 'w3-birkhoff:sourcegap-L750': 'blueprint-W/parts/w3-birkhoff.tex#sourcegap@L750-L759'}.items():
    COV[_k] = (COV[_k][0], COV[_k][1], _src)

# local data of the proof preambles (step context, round-1 rule)
for _k in ("stepW:w3:sel", "stepW:w3:signs", "stepW:w3:s0", "stepW:w3:s1", "stepW:w3:s23", "stepW:w3:s1inner",
           "stepW:w3:divconcl"):
    NODES[_k]["H"] = ("a <= b <= c <= d the sorted ¦x_1¦..¦x_4¦ (n = a); f(s) = sqrt(s^2+m), lambda_k = f(k); "
                      "beta = m/(27 lambda_a^3) (proof preamble L326-L328)")
for _k in ("stepW:w3:majcalc", "stepW:w3:majflow", "stepW:w3:majA", "stepW:w3:majN", "stepW:w3:majX", "stepW:w3:majY",
           "stepW:w3:majint", "stepW:w3:majps", "stepW:w3:majreal"):
    NODES[_k]["H"] = "0 <= s <= 1, 0 <= rho <= rho_1, r = 2 C_F s rho^2 <= 1/80 (proof preamble L622)"
for _k in ("stepW:w3:Kanalytic", "stepW:w3:K1", "stepW:w3:K2", "stepW:w3:XK1", "stepW:w3:XK2", "stepW:w3:XKconcl",
           "stepW:w3:iii", "stepW:w3:conj"):
    NODES[_k]["H"] = ("Z' = bar G - G^tan; K = K_1 + K_2 with K_1 = G o Gamma - G, K_2 = Lambda o Gamma - Lambda - Z' "
                      "(proof preamble L698-L699)")
NODES["stepW:w3:K1"]["deps"].append(("bpW:w3:homological", "L698", "Z' = bar G - G^tan in the splitting K = K_1 + K_2"))
