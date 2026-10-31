# Writer spec for slice W-w0c (blueprint-W/parts/w0-conventions.tex, all lines). Rendered by w_depgraph_fill.py.
F = "blueprint-W/parts/w0-conventions.tex"

NODES = {
    "bpW:w0:mass": dict(
        kind="assumption",
        note="STANDING_ASSUMPTIONS: the only standing assumption of track W (m > 0 fixed). In the frozen anchors it is "
             "the carrier hm : 0 < m of lam, reconU, reconV, cubicGrad, IsClassicalSolution, nlw2 (SPEC).",
        H="none", Q="m fixed", C="m > 0 is fixed; all constants may depend on m unless stated otherwise; no uniformity "
        "as m -> 0 or m -> infinity is claimed", S="none", deps=[]),
    "bpW:w0:nlw#IsClassicalSolution": dict(
        H="typing data: m in R with m > 0 (frozen carrier hm); u : R -> R -> R (frozen: on the whole time line I = R)",
        Q="m, hm, u",
        C="defines: u is a classical solution of u_tt = u_xx - m u - u^3 on I x [0,pi] with u(t,0) = u(t,pi) = 0: "
          "u, u_t, u_x, u_tt, u_xx exist (x-derivatives one-sided at the endpoints, i.e. within [0,pi]) and are "
          "continuous on I x [0,pi], and the equation and boundary conditions hold (KAM.Wave.IsClassicalSolution m hm u, "
          "I = R, derivatives as witnesses ut, ux, utt, uxx)",
        S="none",
        deps=[("bpW:w0:mass", "L33", "the mass m of the equation is the fixed m > 0 (carrier hm)")]),
    "bpW:w0:basis#lam": dict(
        H="typing data: m > 0 (carrier hm); j in N_+", Q="m, hm, j",
        C="defines lambda_j = sqrt(j^2 + m) > 0 (KAM.Wave.lam m hm j); the definition also records "
          "-phi_j'' + m phi_j = lambda_j^2 phi_j",
        S="none",
        deps=[("bpW:w0:mass", "L40", "lambda_j = sqrt(j^2+m) > 0 uses the fixed m > 0")]),
    "bpW:w0:basis#sineMode": dict(
        H="typing data: j in N_+, x in R", Q="j, x",
        C="defines phi_j(x) = sqrt(2/pi) sin(j x) (KAM.Wave.sineMode j x); the definition also records "
          "int_0^pi phi_i phi_j = delta_ij and phi_j(0) = phi_j(pi) = 0",
        S="none", deps=[]),
    "bpW:w0:ellap#ellWeight": dict(
        H="typing data: a, p in R; j in N_+", Q="a, p, j",
        C="defines the weight j^p e^{a j} of the norm ||w||_{a,p}^2 = sum_{j>=1} |w_j|^2 j^{2p} e^{2aj} of l^{a,p} "
          "(KAM.Wave.ellWeight a p j = j^p exp(a j))",
        S="none", deps=[]),
    "bpW:w0:ellap#WaveSpace": dict(
        H="none (the headline weights a = p = 1, Convention bpW:w0:weights)", Q="none",
        C="defines the phase space E_{1,1} = l^{1,1} x l^{1,1} with ||(q,p)||_E = max(||q||_{1,1}, ||p||_{1,1}); frozen "
          "in weighted coordinates as KAM.Wave.WaveSpace = l^2(N_+;R) x l^2(N_+;R) with the product (max) norm, a point "
          "(y, y') standing for q = coeff y, p = coeff y'",
        S="none",
        deps=[("bpW:w0:ellap#ellWeight", "L53", "the norm of l^{a,p} is weighted by j^p e^{aj}, at a = p = 1 the weight "
               "of the weighted coordinates")]),
    "bpW:w0:ellap#coeff": dict(
        H="typing data: y in l^2(N_+;R); j in N_+", Q="y, j",
        C="defines the coefficient q_j = y_j / (j e^j) of the point of l^{1,1} represented by y (KAM.Wave.coeff y j = "
          "y j / ellWeight 1 1 j)",
        S="none",
        deps=[("bpW:w0:ellap#ellWeight", "L53", "the coefficient divides by the weight j^p e^{aj} at a = p = 1")]),
    "bpW:w0:twosided": dict(
        H="typing data: a >= 0, s in R", Q="a, s",
        C="defines l^{a,s}_b, complex sequences (c_l)_{l in Z} with ||c||_{a,s}^2 = sum_l <l>^{2s} e^{2a|l|} |c_l|^2 < "
          "infinity, <l> = max(1,|l|), and the convolution (c*d)_l = sum_i c_i d_{l-i}",
        S="none", deps=[]),
    "bpW:w0:reconstruction#reconU": dict(
        H="typing data: m > 0 (carrier hm); (q,p) in E_{a,p} with a > 0 (frozen: a = 1, q = coeff y for y in "
          "l^2(N_+;R)); x in R",
        Q="m, hm, y, x",
        C="defines U_m(q)(x) = sum_{j>=1} q_j / sqrt(lambda_j) phi_j(x) (KAM.Wave.reconU m hm y x, a tsum over j in N_+ "
          "with q = coeff y); intended dictionary u = U_m(q)",
        S="none",
        deps=[("bpW:w0:basis#lam", "L77", "the weight 1/sqrt(lambda_j)"),
              ("bpW:w0:basis#sineMode", "L77", "the modes phi_j"),
              ("bpW:w0:ellap#coeff", "L76", "q is the coefficient sequence of a point of E (frozen: q = coeff y)")]),
    "bpW:w0:reconstruction#reconV": dict(
        H="typing data: m > 0 (carrier hm); (q,p) in E_{a,p} with a > 0 (frozen: a = 1, p = coeff y for y in "
          "l^2(N_+;R)); x in R",
        Q="m, hm, y, x",
        C="defines V_m(p)(x) = sum_{j>=1} sqrt(lambda_j) p_j phi_j(x) (KAM.Wave.reconV m hm y x with p = coeff y); "
          "intended dictionary u_t = V_m(p)",
        S="none",
        deps=[("bpW:w0:basis#lam", "L77", "the weight sqrt(lambda_j)"),
              ("bpW:w0:basis#sineMode", "L77", "the modes phi_j"),
              ("bpW:w0:ellap#coeff", "L76", "p is the coefficient sequence of a point of E (frozen: p = coeff y)")]),
    "bpW:w0:H": dict(
        H="typing data: (q,p) in E_{1,1}", Q="(q,p)",
        C="defines H_m(q,p) = Lambda(q,p) + G(q), Lambda(q,p) = (1/2) sum_j lambda_j (q_j^2 + p_j^2), "
          "G(q) = (1/4) int_0^pi U_m(q)(x)^4 dx; and states that Lambda is finite on E_{a,p} for p >= 1/2",
        S="none",
        deps=[("bpW:w0:basis#lam", "L89", "Lambda is weighted by lambda_j"),
              ("bpW:w0:reconstruction#reconU", "L90", "G integrates U_m(q)^4"),
              ("bpW:w0:ellap#WaveSpace", "L88", "H is defined on E_{1,1}")]),
    "bpW:w0:Gq#cubicGrad": dict(
        H="typing data: m > 0 (carrier hm); q in l^{1,1} (frozen: q = coeff y, y in l^2(N_+;R)); l in N_+",
        Q="m, hm, y, l",
        C="defines G_q(q)_l = (1/sqrt(lambda_l)) int_0^pi U_m(q)(x)^3 phi_l(x) dx (KAM.Wave.cubicGrad m hm y l); the "
          "remarks that G_q(q)_l = dG/dq_l and G_q(q) in l^{1,2} are forward pointers to Lemma bpW:w0n:gradient and "
          "Theorem bpW:w0n:cubic-bound, not part of the definition",
        S="none",
        note="The \\ref{bpW:w0n:gradient} and \\ref{bpW:w0n:cubic-bound} of L99-L100 are forward pointers (they would "
             "close the cycle cubicGrad -> gradient -> cubicGrad); not edges.",
        deps=[("bpW:w0:reconstruction#reconU", "L98", "the integrand U_m(q)^3"),
              ("bpW:w0:basis#lam", "L98", "the factor 1/sqrt(lambda_l)"),
              ("bpW:w0:basis#sineMode", "L98", "the test mode phi_l")]),
    "bpW:w0:eqmotion": dict(
        H="typing data: (q,p) in E_{1,1}", Q="(q,p), j >= 1",
        C="defines the symplectic form sum_j dq_j ^ dp_j and the Hamiltonian equations, i.e. the coefficient system "
          "(bpW:w0:coeffsys) dq_j/dt = lambda_j p_j, dp_j/dt = -lambda_j q_j - G_q(q)_j (j >= 1), read in l^{1,0} for "
          "(q,p) in E_{1,1} or coordinatewise; records that q -> (lambda_j q_j) is bounded l^{a,p+1} -> l^{a,p} (norm "
          "<= sqrt(1+m)) but not l^{a,p} -> l^{a,p}",
        S="none",
        note="The \\ref{bpW:w0n:cubic-bound} of L111 (smoothing of order one) is a forward pointer, not an edge.",
        deps=[("bpW:w0:H", "L104", "the equations are Hamilton's equations of H"),
              ("bpW:w0:basis#lam", "L107", "the linear part lambda_j"),
              ("bpW:w0:Gq#cubicGrad", "L107", "the nonlinear part G_q(q)_j")]),
    "bpW:w0:z": dict(
        H="typing data: (q,p) in E_{a,p}", Q="(q,p), j >= 1",
        C="defines z_j = (q_j + i p_j)/sqrt 2, zbar_j = (q_j - i p_j)/sqrt 2, so q_j = sqrt2 Re z_j, p_j = sqrt2 Im z_j, "
          "|z_j|^2 = (q_j^2+p_j^2)/2, sum dq ^ dp = i sum dz ^ dzbar, Lambda = sum lambda_j |z_j|^2; under the linear "
          "flow dz_j/dt = -i lambda_j z_j",
        S="none",
        deps=[("bpW:w0:H", "L121", "Lambda = sum lambda_j |z_j|^2 rewrites the quadratic part of H"),
              ("bpW:w0:eqmotion", "L122", "the linear flow dq_j = lambda_j p_j, dp_j = -lambda_j q_j and the form sum dq ^ dp")]),
    "bpW:w0:actions": dict(
        H="typing data: (q,p) in E_{a,p}; on {I_j > 0} for the angle", Q="(q,p), j >= 1",
        C="defines I_j = (q_j^2+p_j^2)/2 = |z_j|^2 and, on {I_j > 0}, the radian angle phi_j by q_j = sqrt(2I_j) cos "
          "phi_j, p_j = -sqrt(2I_j) sin phi_j, z_j = sqrt(I_j) e^{-i phi_j}; dq_j ^ dp_j = dphi_j ^ dI_j, Lambda = sum "
          "lambda_j I_j, linear flow dphi_j/dt = lambda_j, dI_j/dt = 0; I = (I_1,I_2) tangential (J = {1,2}), Z_j = I_j "
          "normal (j >= 3)",
        S="none",
        deps=[("bpW:w0:z", "L128", "I_j = |z_j|^2 and z_j = sqrt(I_j) e^{-i phi_j}"),
              ("bpW:w0:eqmotion", "L132", "the linear flow in action-angle form")]),
    "bpW:w0:periodone#linearTorus": dict(
        H="typing data: I in (0,infinity)^2 (frozen carrier hI : forall i, 0 < I i); theta in R^2", Q="I, hI, theta",
        C="convention: torus angles have period one, phi_j = 2 pi theta_j, campaign frequency nu = omega/(2 pi), "
          "(theta, Y = 2 pi I) canonical, small divisors 2 pi k.nu + l.Omega; defines the linear torus K^0_I(theta) = "
          "(Q^0,P^0) with Q^0_j = sqrt(2I_j) cos(2 pi theta_j), P^0_j = -sqrt(2I_j) sin(2 pi theta_j) for j = 1,2 and "
          "Q^0_j = P^0_j = 0 for j >= 3 (KAM.Wave.linearTorus I hI theta, stored in weighted coordinates "
          "ellWeight 1 1 j * Q^0_j; tangential i : Fin 2 is mode j = i+1); records invariance under the linear flow "
          "with nu = (lambda_1, lambda_2)/(2 pi)",
        S="none",
        deps=[("bpW:w0:actions", "L141", "the formula is the action-angle map with phi_j = 2 pi theta_j"),
              ("bpW:w0:ellap#WaveSpace", "L141", "K^0_I takes values in E (frozen: WaveSpace, weighted coordinates)"),
              ("bpW:w0:ellap#ellWeight", "L141", "frozen weighted coordinates ellWeight 1 1 j * Q^0_j")]),
    "bpW:w0:basis#lambda-facts": dict(
        new=True, kind="claim", title="Elementary facts about lambda_j",
        stmt=f"{F}#bpW:w0:basis@L45-L47", proof=f"{F}#bpW:w0:basis@L45-L47",
        H="m > 0; lambda_j = sqrt(j^2+m)", Q="j >= 1; s in R",
        C="j < lambda_j < j + sqrt m; j/lambda_j < 1; j -> lambda_j strictly increasing; f(s) = sqrt(s^2+m) strictly "
          "convex on R with 0 < f'(s) = s/f(s) < 1 for s > 0 and f' strictly increasing; lambda_{j+1} - lambda_j = "
          "(2j+1)/(lambda_{j+1}+lambda_j) < 1",
        S="none",
        note="Unlabelled prose (L45-L47) stating facts that later proofs consume (SPEC section-data rule); justification "
             "is elementary and inline.",
        deps=[("bpW:w0:basis#lam", "L45", "facts about lambda_j = sqrt(j^2+m)"),
              ("bpW:w0:mass", "L46", "strict convexity and j < lambda_j use m > 0")]),
}

DELETE = ["bpW:w0:weights", "bpW:w0:harmless"]

COV = {
    "bpW:w0:weights": ("NODE bpW:w0:ellap#WaveSpace, bpW:w0:ellap#coeff",
                       "the convention a = p = 1 is realized by the frozen WaveSpace and coeff (weights ellWeight 1 1); "
                       "its remark on lower exponents is an outline"),
    "bpW:w0:harmless": ("EXCLUDED", "administrative remark on the printed-convention disagreements (errata "
                        "E-PDE-W-1/2); no proof consumes it"),
    "w0-conventions:prose-L3-L6": ("EXCLUDED", "introduction and pointer to the comparison table"),
    "w0-conventions:prose-L10-L20": ("EXCLUDED", "list of pinned sources and locators (provenance)"),
    "w0-conventions:prose-L45-L47": ("NODE bpW:w0:basis#lambda-facts", "elementary facts about lambda consumed by later proofs"),
    "w0-conventions:prose-L84-L85": ("EXCLUDED", "forward pointer to Lemma bpW:w0n:recon-bounded"),
    "w0-conventions:prose-L148-L149": ("EXCLUDED", "introduction of the comparison table (provenance)"),
    "w0-conventions:prose-L151-L172": ("EXCLUDED", "comparison table with the printed conventions of P96-W/KP96 "
                                       "(provenance and errata E-PDE-W-1/2); no proof consumes it"),
    "w0-conventions:prose-L174-L174": ("EXCLUDED", "layout line"),
}
