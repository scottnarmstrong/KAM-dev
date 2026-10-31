# Writer spec for slice W-w5b (blueprint-W/parts/w5-kamstep.tex L450-end). Wave 2. Rendered by w_depgraph_fill.py.
F = "blueprint-W/parts/w5-kamstep.tex"
STEP_CONTEXT = True
SYMBOL_EDGES = True
SYMBOL_OVERRIDE = {"bpW:w0:basis#lam": r"\\lambda_(?:[1-9JjiIn]|\{[jJiI])"}
PS = "proof step"
FL = "the setting of Lemma bpW:w5:flow (step data, (bpW:w5:small), the flow phi^t of X_F)"

NODES = {
    "bpW:w5:newham-sec#bracket": dict(
        new=True, kind="definition", title="Poisson bracket and field commutator", stmt=f"{F}#bpW:w5:newham-sec@L454-L455",
        proof="-", H="G C^1, X_F a field; G, F in W4's class T", Q="none",
        C="defines {G,F} = DG . X_F and [X_G,X_F] = DX_G . X_F - DX_F . X_G", S="none",
        note="Unlabelled prose L454-L455 fixing notation used by Lemmas bpW:w5:new-ham and bpW:w5:commutator.",
        deps=[("bpW:w4:taylor", "L455", "the class T")]),
    "bpW:w5:new-ham": dict(
        H=FL + "; Phi = phi^1, D_+ = D(s-5sigma,eta r), R(t) = (1-t) hat N + t R, H = N + P, N_+ = N + hat N = <omega_+,y> + "
          "sum Omega_{+,j} z_j zbar_j, P_+ = (P - R) o Phi + int_0^1 {R(t),F} o phi^t dt", Q="for w in D_+, W in P^{p_+}",
        C="(i) H o Phi = N_+ + P_+ + hat a_0 on D_+; (ii) P_+ in S_{p_+}(D_+), real and periodic, X_{P_+} = Phi^*(X_P - X_R) + "
          "int_0^1 (phi^t)^* [X_{R(t)},X_F] dt; (iii) varpi(X_H(Phi w), D Phi(w) W) = varpi(X_{N_+}(w) + X_{P_+}(w), W) with "
          "X_N : P -> P^{p-1} of Lemma bpW:w4:lie(i) and varpi extended to P^{p-1} x P^{p_+}", S="none",
        deps=[("bpW:w5:flow", "L458", "the flow and its setting"), ("bpW:w5:newham-sec#bracket", "L461", "{R(t),F}"),
              ("bpW:w5:solve", "L459", "hat N, hat omega, hat Omega"), ("bpW:w4:lie", "L469", "(i) X_N"),
              ("bpW:w4:index", "L470", "(bpW:w4:pairing)"), ("bpW:w5:class", "L464", "S_{p_+}"),
              ("stepW:w5:n-exp", "L474", PS), ("stepW:w5:n-br", "L481", PS), ("stepW:w5:n-field", "L485", PS),
              ("stepW:w5:n-conj", "L488", PS)]),
    "stepW:w5:n-exp": dict(H="", Q="w in D_+", C="H(Phi w) = N(w) + hat N(w) + hat a_0 + (P - R)(Phi w) + int_0^1 {(1-tau) "
        "hat N + tau R, F}(phi^tau w) dtau; this is (i)", S="none",
        deps=[("bpW:w5:flow", "L475", "(iii)"), ("bpW:w5:flow-calc", "L475", "(v)"), ("bpW:w5:ext-ftc", "L475", "calculus along curves")]),
    "stepW:w5:n-br": dict(H="", Q="G, F in T", C="{G,F} in S_{p_+} with field [X_G,X_F]", S="none",
        deps=[("stepW:w5:c-skew", "L483", "skewness of DX")]),
    "stepW:w5:n-field": dict(H="", Q="none", C="(ii): the field of P_+; reality", S="none",
        deps=[("bpW:w5:flow-calc", "L485", "(iv) transport, (i) continuity"), ("stepW:w5:n-br", "L486", "the bracket field"),
              ("bpW:w3:ext-integral", "L486", "differentiation under the t-integral")]),
    "stepW:w5:n-conj": dict(H="", Q="w, W", C="(iii) weak conjugacy", S="none",
        deps=[("bpW:w4:lie", "L491", "(i) convergence of the pairings"), ("stepW:w5:n-field", "L492", "(ii)"),
              ("stepW:w5:n-exp", "L488", "(i) H o Phi = N_+ + P_+ + hat a_0")]),
    "bpW:w5:pullback": dict(
        H=FL + "; Y(.,xi) holomorphic fields D(s-3sigma,4 eta r) -> P^{p_+}", Q="for |t| <= 1",
        C="|(phi^t)^* Y|^lambda_{eta r,D_+} <= 7 |Y|^lambda_{eta r,D(s-3sigma,4 eta r)} (norm |.|_{p_+,eta r})", S="7 absolute",
        deps=[("bpW:w5:flow", "L503", "the setting"), ("stepW:w5:p-inv", "L508", PS), ("stepW:w5:p-dy", "L514", PS),
              ("stepW:w5:p-ass", "L517", PS)]),
    "stepW:w5:p-inv": dict(H="", Q="W", C="|D(phi^t)^{-1}|_{p_+->p_+,eta r} <= 2 and lambda|Delta(D phi^t)^{-1}| <= 4",
        S="none", deps=[("bpW:w5:omega", "L509", "norm comparisons"), ("bpW:w5:flow", "L509", "(ii)"),
                        ("stepW:w5:f-der", "L512", "the parameter bound")]),
    "stepW:w5:p-dy": dict(H="", Q="w", C="|DY|_{p->p_+,eta r} <= 2|Y|/sigma on D(s-4sigma,2 eta r)", S="none",
        deps=[("bpW:w1:kam-domain", "L514", "margins"), ("bpW:w1:cauchy", "L516", "Cauchy estimate")]),
    "stepW:w5:p-ass": dict(H="", Q="none", C="the total bound 7 |Y|^lambda", S="none",
        deps=[("stepW:w5:p-inv", "L517", "inverse bounds"), ("stepW:w5:p-dy", "L519", "derivative of Y"),
              ("bpW:w5:lambda-product", "L518", "lambda-norm of products")]),
    "bpW:w5:commutator": dict(
        H=FL, Q="for 0 <= t <= 1", C="|[X_{R(t)},X_F]|^lambda_{eta r,D(s-3sigma,4 eta r)} <= 24 eps M_F/(sigma eta^2)",
        S="24 absolute",
        deps=[("bpW:w5:flow", "L527", "the setting"), ("bpW:w5:newham-sec#bracket", "L528", "the commutator"),
              ("stepW:w5:k-cauchy", "L531", PS), ("stepW:w5:k-bd", "L534", PS)]),
    "stepW:w5:k-cauchy": dict(H="", Q="G in {R(t),F}", C="|DX_G|_{p->p_+,r} <= (2/sigma)|X_G| on D(s-2sigma,r/2) and for "
        "parameter differences", S="none", deps=[("bpW:w1:kam-domain", "L532", "margins"), ("bpW:w1:cauchy", "L533", "Cauchy")]),
    "stepW:w5:k-bd": dict(H="", Q="t", C="the commutator bound", S="none",
        deps=[("bpW:w5:taylor", "L535", "|X_R| <= 3 eps"), ("bpW:w5:solve", "L535", "|X_{hat N}| <= 6 eps, |X_F| <= M_F"),
              ("bpW:w5:lambda-product", "L535", "submultiplicativity"), ("stepW:w5:k-cauchy", "L536", "derivative bounds"),
              ("bpW:w5:omega", "L537", "|.|_{eta r} <= eta^{-2}|.|_r")]),
    "bpW:w5:step": dict(
        H="step data (Definition bpW:w5:data) and the smallness condition (bpW:w5:small); in the modified case also 2 beta <= "
          "p+1-p_+ for the Lipschitz parts; C_2 = 896 + 168 c_F",
        Q="there exist a real holomorphic family Phi(.,xi) : D_+ = D(s-5sigma,eta r) -> D(s-4sigma,2 eta r), N_+, P_+; then for "
          "all xi in Pi",
        C="(i) H o Phi = N_+ + P_+ + hat a_0(xi) on D_+ with the weak conjugacy; Phi symplectic, D Phi(w) maps P^{p_+} onto "
          "itself, real, Phi(w + tau_k) = Phi(w) + tau_k; (ii) P_+ in S_{p_+}(D_+) real periodic with (bpW:w5:newerror) "
          "|X_{P_+}|^lambda_{eta r,D_+} <= C_2(eps^2/(alpha sigma^t eta^2) + eta eps); (iii) |omega_+ - omega| + lambda|.|^L <= "
          "6 pi eps, sup (j+2)^{p_+-p}(|Omega_{+,j} - Omega_j| + lambda|.|^L) <= 3 eps, so (omega_+,Omega_+) satisfies "
          "(bpW:w5:freq) with M_0 + 3 eps and M_+ <= M + (6pi+3) eps/lambda (lambda > 0); (iv) for K >= 1, 0 < alpha_+ <= "
          "alpha with 6 pi (1+K)(1+K^tau) eps <= alpha - alpha_+, the divisor bounds with alpha_+ for |k|_1 <= K (also with "
          "<l>^w); (v) |Phi - id|^lambda_{p_+,r,D_+} <= 2 M_F and |D Phi - I|^lambda_{p->p_+,r,D_+} <= 16 M_F/sigma",
        S="C_2 = 896 + 168 c_F depends only on tau",
        deps=[("bpW:w5:data", "L544", "step data and (bpW:w5:small)"), ("bpW:w5:new-ham", "L548", "(iii) weak conjugacy"),
              ("bpW:w5:flow", "L550", "(iv)"), ("bpW:w4:wave", "L562", "(ii) <l>^w"), ("bpW:w4:melnikov", "L560", "Z, A_k, <l>"),
              ("stepW:w5:st-con", "L568", PS), ("stepW:w5:st-1", "L571", PS), ("stepW:w5:st-2", "L573", PS),
              ("stepW:w5:st-freq", "L575", PS), ("stepW:w5:st-div", "L577", PS)]),
    "stepW:w5:st-con": dict(H="", Q="none", C="Phi = phi^1, (i), the formula for X_{P_+}, and (v)", S="none",
        deps=[("bpW:w5:taylor", "L568", "R"), ("bpW:w5:solve", "L568", "F"), ("bpW:w5:flow", "L568", "the flow; (i)-(ii)"),
              ("bpW:w5:flow-calc", "L569", "calculus"), ("bpW:w5:new-ham", "L569", "the new Hamiltonian")]),
    "stepW:w5:st-1": dict(H="", Q="none", C="the first term is <= 896 eta eps", S="none",
        deps=[("bpW:w5:taylor", "L572", "(iv)"), ("bpW:w5:pullback", "L572", "pull-back bound")]),
    "stepW:w5:st-2": dict(H="", Q="none", C="the second term is <= 168 c_F eps^2/(alpha sigma^t eta^2)", S="none",
        deps=[("bpW:w5:commutator", "L573", "commutator bound"), ("bpW:w5:pullback", "L573", "pull-back bound")]),
    "stepW:w5:st-freq": dict(H="", Q="none", C="(iii) from Lemma bpW:w5:solve; Lipschitz constants", S="none",
        deps=[("bpW:w5:solve", "L575", "the frequency corrections")]),
    "stepW:w5:st-div": dict(H="", Q="|k|_1 <= K", C="(iv): the corrections shift the divisors by at most (alpha - alpha_+)"
        "<l>/A_k", S="none", deps=[("stepW:w5:st-freq", "L577", "the frequency corrections")]),
    "bpW:w5:action-angle": dict(
        H="W3's normal form H' = Lambda + bar G + G^nor + K on B_{rho_1} (Theorem bpW:w3:main), W = W_{a,p}; a = p = 1; xi in "
          "C^2, w = (theta,y,u,v) in P with Re(xi_i + y_i) > 0; A_xi(w) as displayed (principal square root); (ii) 0 < s <= "
          "1/8, r > 0, t > 0, |xi|_infty <= t, Re xi_i >= 2r^2, c_A = 2200", Q="for all such xi, w; every q in R in (iii)",
        C="(i) (xi,w) -> A_xi(w) holomorphic, 1-periodic in theta_i, real points to W_R; Z^{-1} A_xi(theta,0,0,0) = K^0_xi"
          "(theta) for real theta, xi in (0,infinity)^2; (ii) A_xi(D(s,r)) subset B_rho with rho^2 = c_A(t + r^2), in B_{rho_1} "
          "when c_A(t + r^2) < rho_1(m)^2; (iii) D A_xi(w) is a linear bijection P^q -> W^q with the displayed inverse, and "
          "Omega(D A_xi W, D A_xi W') = varpi(W,W') for q + q' >= 0; (iv) H' o A_xi = e(xi) + N_xi + P_xi with e(xi) = "
          "<lambda_J,xi> + (1/2)<A xi,xi>, N_xi = <omega^0(xi),y> + sum Omega^0_{j+2}(xi) z_j zbar_j, P_xi = tilde Q + G^nor o "
          "A_xi + K o A_xi; (v) P_xi in S_{p+1}(D(s,r)), real for real xi, with the displayed field, and X_{H'}(A_xi w) = D "
          "A_xi(w)(X_{N_xi}(w) + X_{P_xi}(w)) in W^{p-1}; (vi) no weight conversion is needed; ||hat w|| <= ||u|| + ||v|| <= "
          "sqrt2 ||hat w|| and ||x||_E <= ||Zx|| <= sqrt2 ||x||_E", S="c_A = 2200 absolute",
        note="The pointer to Proposition bpW:w5:initial in (vi) is a forward pointer; not an edge.",
        deps=[("bpW:w3:main", "L597", "H' and B_{rho_1}"), ("bpW:w3:space", "L596", "W, W^q"),
              ("bpW:w3:omega", "L596", "the form Omega"), ("bpW:w5:setting", "L601", "P and varpi"),
              ("bpW:w0:periodone#linearTorus", "L608", "the linear torus K^0_xi"), ("bpW:w3:coords", "L609", "Z"),
              ("bpW:w7:omega0", "L623", "omega^0, Omega^0"), ("bpW:w4:from-w3", "L632", "the weight identification"),
              ("bpW:w5:class", "L627", "S_{p+1}"),
              ("stepW:w5:a-hol", "L640", PS), ("stepW:w5:a-dom", "L644", PS), ("stepW:w5:a-der", "L647", PS),
              ("stepW:w5:a-nf", "L651", PS), ("stepW:w5:a-field", "L655", PS), ("stepW:w5:a-conj", "L661", PS)]),
    "stepW:w5:a-hol": dict(H="", Q="none", C="(i) holomorphy, reality and the linear torus", S="none", deps=[]),
    "stepW:w5:a-dom": dict(H="", Q="w in D(s,r)", C="(ii) the tangential part is <= 2173(t + r^2), the normal part < r^2",
        S="none", deps=[]),
    "stepW:w5:a-der": dict(H="", Q="w", C="(iii) the inverse of D A and the form identity", S="none",
        deps=[("bpW:w4:index", "L650", "(bpW:w4:pairing)")]),
    "stepW:w5:a-nf": dict(H="", Q="w", C="(iv) by substituting w_i w_{-i} = xi_i + y_i into Lambda and bar G", S="none",
        deps=[("bpW:w3:main", "L653", "(iii) bar G"), ("bpW:w0n:AB", "L653", "A, B"), ("bpW:w3:Lambda", "L652", "Lambda")]),
    "stepW:w5:a-field": dict(H="", Q="w", C="(v) the field of P_xi lies in P^{p+1}", S="none",
        deps=[("bpW:w3:main", "L655", "(ii)-(iii) fields into W+"), ("stepW:w5:a-der", "L656", "(iii)")]),
    "stepW:w5:a-conj": dict(H="", Q="w, W", C="(v) the conjugacy identity in W^{p-1}", S="none",
        deps=[("bpW:w3:Lambda", "L663", "D Lambda(w')W'' = Omega(X_Lambda(w'),W'')"), ("stepW:w5:a-nf", "L663", "(iv)"),
              ("bpW:w5:new-ham", "L663", "(iii)'s computation for N_xi"), ("stepW:w5:a-der", "L665", "(iii)"),
              ("bpW:w3:omega", "L666", "nondegeneracy")]),
    "bpW:w5:initial": dict(
        H="m > 0, a = p = 1; rho_1, C_*, C'_K W3's constants; 0 < s <= 1/8, 0 < r <= 1, t > 0, rho_xi > 0, Pi subset R^2 such "
          "that every zeta in C^2 with |zeta - xi|_infty < rho_xi for some xi in Pi satisfies Re zeta_i >= 2r^2 and "
          "|zeta|_infty <= t, and c_A(t + r^2) < rho_1^2; eps_in as displayed", Q="for every lambda >= 0",
        C="P_xi in S_{p+1}(D(s,r)) is a real periodic family on Pi and |X_P|^lambda_{r,D(s,r)} <= eps_in(1 + 4 lambda/rho_xi); "
          "omega^0, Omega^0_{j+2} satisfy (bpW:w4:freq) (hence (bpW:w5:freq)) with the constants of Lemma bpW:w4:wave and "
          "|omega^0(xi) - omega^0(xi')| <= N_A |xi - xi'|", S="eps_in explicit in r, t, C_*, C'_K, c_A",
        deps=[("bpW:w3:main", "L674", "rho_1, C'_K"), ("bpW:w3:majorant", "L674", "C_*"),
              ("bpW:w5:action-angle", "L678", "P_xi"), ("bpW:w4:wave", "L681", "the frequency constants"),
              ("stepW:w5:i-q", "L684", PS), ("stepW:w5:i-g", "L689", PS), ("stepW:w5:i-k", "L692", PS),
              ("stepW:w5:i-par", "L697", PS), ("stepW:w5:i-freq", "L702", PS)]),
    "stepW:w5:i-q": dict(H="", Q="w in D(s,r)", C="the field of tilde Q is <= r^2", S="none",
        deps=[("bpW:w7:freqcoords", "L685", "(ii) N_A <= 3/5"), ("bpW:w4:index", "L686", "(bpW:w4:zu)")]),
    "stepW:w5:i-g": dict(H="", Q="w", C="the G^nor contribution is <= 2 C_* r^2", S="none",
        deps=[("bpW:w3:main", "L690", "(iii)"), ("bpW:w5:action-angle", "L691", "(iii) inverse formula")]),
    "stepW:w5:i-k": dict(H="", Q="w", C="the K contribution", S="none",
        deps=[("bpW:w3:main", "L692", "(ii) ||X_K|| <= C'_K ||w||^5"), ("bpW:w5:action-angle", "L692", "(ii), (iii)")]),
    "stepW:w5:i-par": dict(H="", Q="xi, xi'", C="the Lipschitz constant 4 eps_in/rho_xi", S="none",
        deps=[("bpW:w1:cauchy", "L700", "Cauchy estimate in xi")]),
    "stepW:w5:i-freq": dict(H="", Q="none", C="the frequency conditions", S="none",
        deps=[("bpW:w4:wave", "L702", "(i)"), ("bpW:w7:freqcoords", "L702", "(ii)")]),
}

DELETE = ["bpW:w5:notation"]

COV = {
    "bpW:w5:notation": ("EXCLUDED", "administrative remark (notation clash in P96-K)"),
    "w5-kamstep:sourcegap-L498": ("NODE bpW:w5:new-ham, stepW:w5:n-exp", "P96-K p. 130 asserts the new field without "
        "derivation; supplied in Lemma bpW:w5:new-ham", "blueprint-W/parts/w5-kamstep.tex#sourcegap@L498-L500"),
    "w5-kamstep:prose-L454-L455": ("NODE bpW:w5:newham-sec#bracket", "notation {G,F} and [X_G,X_F]"),
    "w5-kamstep:prose-L594-L598": ("NODE bpW:w5:action-angle", "introduction of the action-angle subsection (W3's H' on "
                                   "B_{rho_1}, principal square root), recorded in the lemma's hypotheses"),
    "w5-kamstep:prose-L711-L718": ("EXCLUDED", "constants ledger (summary)"),
    "w5-kamstep:prose-L720-L724": ("EXCLUDED", "ledger of results (administrative)"),
    "w5-kamstep:prose-L726-L731": ("EXCLUDED", "ledger of source issues (administrative)"),
}
