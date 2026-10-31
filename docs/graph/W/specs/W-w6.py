# Writer spec for slice W-w6 (blueprint-W/parts/w6-iteration.tex, all lines). Wave 2. Rendered by w_depgraph_fill.py.
F = "blueprint-W/parts/w6-iteration.tex"
STEP_CONTEXT = True
SYMBOL_EDGES = True
SYMBOL_OVERRIDE = {"bpW:w0:basis#lam": r"\\lambda_(?:[1-9JjiIn]|\{[jJiI])", "bpW:w0:periodone#linearTorus": r"K\^0_"}
PS = "proof step"
SD = "W6 notation (L22-L27): m > 0, a = p = 1, tau = 24, t = 52, W5's constants c_F, c_0, C_2 (modified step: t^natural = 53, c^natural_F, c^natural_0, C^natural_2), Melnikov conditions with W7's Dirichlet weight <l>"
SEQ = "the data of Definition bpW:w6:sequences (0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0) with eps_0 <= gamma_0 alpha_0 sigma_0^t; p_+ = p + 1/2"

NODES = {
    "bpW:w6#data": dict(
        new=True, kind="definition", title="W6 fixed data and notation", stmt=f"{F}#bpW:w6@L22-L27", proof="-",
        H="none", Q="none",
        C="writes P96-K's kappa = 4/3 as varkappa; fixes m > 0, a = p = 1, tau = 24, t = 2 tau + 4 = 52 and W5's constants c_F, "
          "c_0, C_2 (modified step t^natural = 53, c^natural_F, c^natural_0, C^natural_2); Melnikov conditions use W7's Dirichlet "
          "weight <l> (by Lemma bpW:w4:wave(ii) they imply W4's)", S="none",
        note="Unlabelled 'Notation' paragraph (SPEC hypothesis packages); recorded in the SOURCE_HYPOTHESES of W6 results.",
        deps=[("bpW:w5:data", "L24", "W5's constants and t"), ("bpW:w7:indexdef", "L26", "W7's Dirichlet weight <l>"),
              ("bpW:w4:wave", "L26", "(ii) reindexing")]),
    "bpW:w6:sequences": dict(
        H=SD + "; 0 < s_0 <= 1, r_0 > 0, 0 < alpha_0 <= 1, M_0 > 0, eps_0 > 0", Q="s_0, r_0, alpha_0, M_0, eps_0",
        C="defines sigma_0 = s_0/40 and sigma_nu, s_nu, alpha_nu, M_nu, lambda_nu, eta_nu, r_nu, eps_nu, D_nu, gamma_0 = "
          "(2^{t+4} C_2 + c_0)^{-3}, K_0 = (96 pi gamma_0 sigma_0^t)^{-1/(tau+1)}, K_nu = K_0 2^nu, K_{-1} = 0; records s_nu "
          "decreasing to (3/4) s_0, sigma_nu <= min(1/4, s_nu/6), lambda_nu >= lambda_0/4, K_0 >= 1, K_nu >= 2^nu",
        S="gamma_0, K_0 depend only on tau and W5's constants (and sigma_0)",
        deps=[("bpW:w6#data", "L36", "C_2, c_0, t, tau")]),
    "bpW:w6:iter-lemma": dict(
        H=SD + "; " + SEQ + "; at stage nu: Pi_nu subset R^2; (omega_nu,Omega_nu) satisfying (bpW:w5:freq) with M_omega + "
          "M_Omega <= M_nu; (bpW:w6:melnikov) on Pi_nu for (k,l) in Z; a real periodic family P_nu in S_{p_+}(D_nu) with "
          "|X_{P_nu}|^{lambda_nu}_{r_nu,D_nu} <= eps_nu; q_nu = eps_nu/(alpha_nu sigma_nu^t)", Q="for every stage nu >= 0",
        C="q_nu <= gamma_0 2^{-nu}, q_{nu+1} <= q_nu/4; W5's step (unmodified) applies and yields Phi_{nu+1} : D_{nu+1} -> D_nu, "
          "N_{nu+1}, P_{nu+1} such that with Pi_{nu+1} = Pi_nu minus the zones R^{nu+1}_{kl} (|k| > K_nu) all hypotheses hold "
          "at stage nu+1, provided (bpW:w6:melnikov) for k = 0 holds at nu+1; the transformation, derivative and frequency "
          "increment bounds (with M_{F,nu} = c_F q_nu sigma_nu)", S="as in Definition bpW:w6:sequences",
        deps=[("bpW:w6:sequences", "L48", "the sequences"), ("bpW:w5:w4-general", "L50", "(bpW:w5:freq)"),
              ("bpW:w7:indexdef", "L50", "W7's index set Z and <l>"), ("bpW:w5:class", "L54", "S_{p_+} and the lambda-norm"),
              ("bpW:w5:step", "L56", "W5's step"),
              ("stepW:w6:il-small", "L69", PS), ("stepW:w6:il-err", "L72", PS), ("stepW:w6:il-lip", "L76", PS),
              ("stepW:w6:il-div", "L79", PS), ("stepW:w6:il-tr", "L83", PS)]),
    "stepW:w6:il-small": dict(H="", Q="nu", C="q_nu <= gamma_0 2^{-nu}; (bpW:w5:small) holds; Theorem bpW:w5:step applies",
        S="none", deps=[("bpW:w5:data", "L70", "(bpW:w5:small)"), ("bpW:w5:step", "L71", "applicability")]),
    "stepW:w6:il-err": dict(H="", Q="nu", C="|X_{P_{nu+1}}| <= eps_{nu+1} and q_{nu+1} <= q_nu/4", S="none",
        deps=[("bpW:w5:step", "L72", "(ii) (bpW:w5:newerror)"), ("stepW:w6:il-small", "L74", "q_nu <= gamma_0")]),
    "stepW:w6:il-lip": dict(H="", Q="nu", C="the Lipschitz constants stay <= M_{nu+1}", S="none",
        deps=[("bpW:w5:step", "L76", "(iii)")]),
    "stepW:w6:il-div": dict(H="", Q="nu", C="(bpW:w6:melnikov) at nu+1 on Pi_nu for 0 < |k| <= K_nu, and on Pi_{nu+1} for "
        "|k| > K_nu by construction", S="none", deps=[("bpW:w5:step", "L81", "(iv) divisors")]),
    "stepW:w6:il-tr": dict(H="", Q="nu", C="the transformation bounds", S="none", deps=[("bpW:w5:step", "L83", "(v)")]),
    "bpW:w6:k0": dict(
        H="the setting of Lemma bpW:w6:iter-lemma; |<l,Omega_0>| >= 2 beta_0 <l> for l in Lambda on Pi_0, beta_0 >= alpha_0, "
          "8 eps_0 <= beta_0", Q="for every nu",
        C="(bpW:w6:melnikov) with k = 0 holds on Pi_nu, and sup_j (j+2)^{1/2}|Omega_{nu,j} - Omega_{0,j}| <= sum_{mu<nu} 3 "
          "eps_mu <= 4 eps_0", S="none",
        note="Inline proof (L94-L98).",
        deps=[("bpW:w6:iter-lemma", "L90", "the setting and the increments"), ("bpW:w7:indexdef", "L90", "Lambda and <l>")]),
    "bpW:w6:convergence": dict(
        H=SD + "; " + SEQ + "; Pi_{-1} subset R^2; (omega_0,Omega_0) on Pi_{-1} with (bpW:w5:freq), M_omega + M_Omega <= M_0; "
          "the k = 0 bound of Lemma bpW:w6:k0 on Pi_{-1}; a real periodic family P_0 in S_{p_+}(D_0) with |X_{P_0}|^{lambda_0} "
          "<= eps_0; Pi_0, Pi_nu, Pi_* = cap Pi_nu, Phi^nu = Phi_1 o ... o Phi_nu", Q="for all such data",
        C="(i) Pi_{-1} minus Pi_* is the union of the zones R^nu_{kl} (|k| > K_{nu-1}); Borel if Pi_{-1} is Borel and the "
          "frequencies continuous; (ii) omega_nu -> omega_*, Omega_nu -> Omega_* uniformly on Pi_* with |omega_* - omega_0| "
          "<= 8 pi eps_0, Lipschitz <= 64 pi eps_0/lambda_0, sup (j+2)^{1/2}|Omega_* - Omega_0| <= 4 eps_0 (Lipschitz <= 16 "
          "eps_0/lambda_0), and |<k,omega_*> + <l,Omega_*>| >= (alpha_0/2)<l>/A_k on Pi_*; (iii) theta -> Phi^nu(iota theta) "
          "converge uniformly on T_{s_infty} x Pi_* to Phi_*, holomorphic, periodic, real, jointly continuous, with values in "
          "closure D(s_0-4sigma_0,2 eta_0 r_0) and |Phi_* - iota|_{p_+,r_0} <= e_Phi = 5 c_F eps_0/(alpha_0 sigma_0^{t-1}); "
          "derivatives converge on T_{s_0/2}; (iv) |D Phi^nu(w) W|_{q,r_0} <= 2|W|_{q,r_nu}, D Phi^nu symplectic and onto "
          "P^{p_+}", S="e_Phi explicit",
        deps=[("bpW:w6:sequences", "L104", "the sequences"), ("bpW:w6:k0", "L106", "the k = 0 bound"),
              ("bpW:w6:iter-lemma", "L109", "Pi_nu"),
              ("stepW:w6:c-ind", "L135", PS), ("stepW:w6:c-par", "L137", PS), ("stepW:w6:c-freq", "L139", PS),
              ("stepW:w6:c-dom", "L143", PS), ("stepW:w6:c-op", "L147", PS), ("stepW:w6:c-cauchy", "L151", PS),
              ("stepW:w6:c-lim", "L155", PS), ("stepW:w6:c-cont", "L158", PS)]),
    "stepW:w6:c-ind": dict(H="", Q="nu", C="all stages exist; eps_nu <= 4^{-nu} eps_0", S="none",
        deps=[("bpW:w6:k0", "L136", "k = 0"), ("bpW:w6:iter-lemma", "L136", "induction")]),
    "stepW:w6:c-par": dict(H="", Q="none", C="(i) and Borel measurability", S="none",
        deps=[("bpW:w7:ext-borel", "L138", "relatively open zones in a Borel set")]),
    "stepW:w6:c-freq": dict(H="", Q="none", C="(ii) by summing the increments; the divisor bound in the limit", S="none",
        deps=[("bpW:w6:iter-lemma", "L139", "the increments")]),
    "stepW:w6:c-dom": dict(H="", Q="nu", C="Phi^nu is defined, holomorphic, real and equivariant on D_nu", S="none",
        deps=[("bpW:w5:step", "L143", "(i), the image domain")]),
    "stepW:w6:c-op": dict(H="", Q="W", C="(iv) operator bounds, symplecticity, surjectivity on P^{p_+}", S="none",
        deps=[("bpW:w6:iter-lemma", "L148", "derivative bounds"), ("bpW:w5:omega", "L148", "norm comparison"),
              ("bpW:w5:step", "L150", "(i)")]),
    "stepW:w6:c-cauchy": dict(H="", Q="theta", C="|Phi^{nu+1}(iota theta) - Phi^nu(iota theta)|_{p_+,r_0} <= 4 c_F q_nu sigma_nu, "
        "summing to e_Phi", S="none", deps=[("stepW:w6:c-op", "L152", "(iv)"), ("bpW:w6:iter-lemma", "L152", "transformation bounds")]),
    "stepW:w6:c-lim": dict(H="", Q="none", C="the limit Phi_* is holomorphic, periodic, real; derivatives converge; image bound",
        S="none", deps=[("bpW:w1:uniform-limit", "L155", "holomorphy of the uniform limit"), ("stepW:w6:c-cauchy", "L154", "Cauchy sequence")]),
    "stepW:w6:c-cont": dict(H="", Q="none", C="joint continuity in (theta,xi)", S="none",
        deps=[("bpW:w5:flow", "L158", "(i) Lipschitz in xi")]),
    "bpW:w6:strong": dict(
        H=SD + "; Phi : O -> P C^1 on open O with D Phi(w) symplectic and onto P^{p_+} from P^{p_+}; H, H_+ with fields X_H : "
          "Phi(O) -> P^{p-1}, X_{H_+} : O -> P^{p-1} and varpi(X_H(Phi w), D Phi(w) W) = varpi(X_{H_+}(w), W) for W in P^{p_+}; "
          "X_{H_+}(w) in P", Q="for such Phi, H, H_+, w",
        C="X_H(Phi w) = D Phi(w) X_{H_+}(w)", S="none",
        deps=[("bpW:w5:setting", "L171", "P, varpi"), ("stepW:w5:omnd", "L178", "test with unit vectors")]),
    "bpW:w6:invariance": dict(
        H="the setting of Proposition bpW:w6:convergence; H_0 = N_0 + P_0; nu_* = omega_*/(2pi); X_{N_0}(w) = (omega_0/(2pi), "
          "0, Omega_0 v, -Omega_0 u)", Q="for xi in Pi_* and theta in T_{s_0/2}",
        C="X_{H_0}(Phi_*(theta)) = d_theta Phi_*(theta) nu_* in P^{p-1}, and both sides lie in P", S="none",
        deps=[("bpW:w6:convergence", "L183", "Phi_*, omega_*"),
              ("stepW:w6:i-weak", "L189", PS), ("stepW:w6:i-torus", "L197", PS), ("stepW:w6:i-lim", "L200", PS)]),
    "stepW:w6:i-weak": dict(H="", Q="nu, w, W", C="varpi(X_{H_0}(Phi^nu w), D Phi^nu W) = varpi(X_{H_nu}(w), W)", S="none",
        deps=[("bpW:w5:step", "L190", "(i)"), ("bpW:w6:convergence", "L193", "(iv)"), ("stepW:w5:n-conj", "L193", "derivative formulas")]),
    "stepW:w6:i-torus": dict(H="", Q="theta", C="at torus points the strong identity holds", S="none",
        deps=[("bpW:w6:strong", "L198", "strong conjugacy"), ("bpW:w6:convergence", "L198", "(iv)"), ("stepW:w6:i-weak", "L198", "weak chain")]),
    "stepW:w6:i-lim": dict(H="", Q="theta", C="passage to the limit in P^{p-1}", S="none",
        deps=[("bpW:w4:lie", "L202", "(i) X_{N_0} bounded"), ("bpW:w6:convergence", "L200", "(ii), (iii)"), ("stepW:w6:i-torus", "L200", "identity")]),
    "bpW:w6:constants": dict(
        H=SD + "; W7's constants (Definition bpW:w7:constdef) and W5's", Q="none",
        C="defines s = 1/8, sigma_P = s/40, s_0 = (7/8)s, sigma_0 = s_0/40, M = M_omega + M_Omega of Lemma bpW:w4:wave(i), M_0 = "
          "2M, gamma_0, gamma_1 = min{gamma_0 sigma_0^t, theta_0/(425(1+M)), beta_*/8}, gamma = min{1/40, (c^natural_0)^{-3} "
          "sigma_P^{t^natural}, theta_0/(425(1+M)), (gamma_1 sigma_P^{t^natural/3}/(2 C^natural_2))^{3/4}}; all depend on m only",
        S="all depend on m only (through M, theta_0, beta_*)",
        deps=[("bpW:w7:constdef", "L212", "W7's constants theta_0, beta_*"), ("bpW:w4:wave", "L213", "(i) M"),
              ("bpW:w6:sequences", "L214", "gamma_0"), ("bpW:w6#data", "L216", "c^natural_0, C^natural_2, t^natural")]),
    "bpW:w6:prep-step": dict(
        H=SD + "; constants of Definition bpW:w6:constants; Pi subset {|xi|_infty <= 1/2} Borel; 0 < alpha <= alpha_0 (W7 (C4)); "
          "hat alpha = alpha^{44/47}, check alpha = alpha^{48/47}; Xi W7's preparatory set; r > 0; a real periodic family P in "
          "S_{p+1}(D(s,r)) on Pi minus Xi with the unperturbed frequencies (omega^0,Omega^0) and eps with 0 < eps <= gamma alpha, "
          "|X_P|^lambda_{r,D(s,r)} <= eps, lambda = alpha/M; eta_P = (eps/(hat alpha sigma_P^{t^natural}))^{1/3}, r_0 = eta_P r",
        Q="for all such data",
        C="one step of Theorem bpW:w5:step in the modified case (beta = 1/4, p_+ = p + 1/2, level hat alpha) applies on Pi minus "
          "Xi and gives Phi_P : D_0 = D(s_0,r_0) -> D(s,r) symplectic, real, holomorphic, with (N + P) o Phi_P = N_0 + P_0 + "
          "const and the weak conjugacy, and (i) the divisor hypotheses hold (Corollary bpW:w7:melnikov(i)); (ii) the frequency "
          "shift bounds and (bpW:w5:freq) with M_omega + M_Omega <= 2M; (iii) |Phi_P - id|_{p_+,r,D_0} <= M_{F,P} and Lipschitz "
          "in xi; (iv) sup |X_{P_0}|_{p_+,r_0,D_0} <= eps^flat_0 = 2 C^natural_2 eps^{4/3}(hat alpha sigma_P^{t^natural})^{-1/3} "
          "<= gamma_1 check alpha; (v) |X_{P_0}|^{lambda_0}_{r_0,D_0} <= eps^flat_0 with lambda_0 = check alpha/M_0",
        S="as in Definition bpW:w6:constants",
        deps=[("bpW:w6:constants", "L220", "s, sigma_P, gamma, gamma_1"), ("bpW:w7:constdef", "L221", "(C4) alpha_0"),
              ("bpW:w7:zones", "L222", "the preparatory set Xi"), ("bpW:w7:omega0", "L223", "the unperturbed frequencies"),
              ("bpW:w5:class", "L223", "S_{p+1} and the lambda-norm"), ("bpW:w5:step", "L228", "W5's step (modified)"),
              ("bpW:w5:new-ham", "L230", "(iii) weak conjugacy"), ("bpW:w7:melnikov", "L233", "(i)"),
              ("stepW:w6:p-data", "L247", PS), ("stepW:w6:p-div", "L250", PS), ("stepW:w6:p-step", "L253", PS),
              ("stepW:w6:p-lipp", "L258", PS), ("stepW:w6:p-size", "L260", PS), ("stepW:w6:p-gap", "L264", PS)]),
    "stepW:w6:p-data": dict(H="", Q="none", C="step data and (bpW:w5:small) hold; frequencies satisfy (bpW:w4:freq)", S="none",
        deps=[("bpW:w5:data", "L248", "(bpW:w5:small)"), ("bpW:w4:wave", "L249", "the frequencies")]),
    "stepW:w6:p-div": dict(H="", Q="(k,l)", C="(i) the modified divisor hypotheses with beta = 1/4", S="none",
        deps=[("bpW:w7:indexdef", "L251", "W7's weights hat w"), ("bpW:w5:w4-modified", "L251", "(bpW:w5:modified)")]),
    "stepW:w6:p-step": dict(H="", Q="none", C="Theorem bpW:w5:step in the modified case; the frequency shifts", S="none",
        deps=[("bpW:w5:step", "L253", "modified case"), ("bpW:w5:w4-modified", "L254", "both parts"),
              ("bpW:w5:taylor", "L256", "the Taylor polynomial"), ("bpW:w4:lemma1", "L256", "(iv)")]),
    "stepW:w6:p-lipp": dict(H="", Q="none", C="(iii)", S="none", deps=[("bpW:w5:step", "L258", "(v)")]),
    "stepW:w6:p-size": dict(H="", Q="none", C="(iv) sup |X_{P_0}| <= eps^flat_0 <= gamma_1 check alpha", S="none",
        deps=[("bpW:w5:step", "L260", "(bpW:w5:newerror), modified")]),
    "stepW:w6:p-gap": dict(H="", Q="none", C="(v) the lambda-norm bound", S="none",
        deps=[("bpW:w5:w4-modified", "L264", "(ii)"), ("stepW:w6:p-size", "L265", "the size computation")]),
    "bpW:w6:wave-iteration": dict(
        H="the setting of Lemma bpW:w6:prep-step with (v)", Q="none",
        C="defines the wave iteration: Proposition bpW:w6:convergence with s_0, sigma_0 of Definition bpW:w6:constants, r_0 = "
          "eta_P r, alpha_0^it = check alpha, M_0 = 2M, a starting size eps_0 in [eps^flat_0, gamma_1 check alpha] (a "
          "parameter, > 0), Pi_{-1} = Pi minus Xi, (omega_0,Omega_0), P_0, beta_0 = beta_*; outputs Pi_*, omega_*, Omega_*, "
          "Phi_*, (omega_nu,Omega_nu), R^nu_{kl}", S="none",
        deps=[("bpW:w6:prep-step", "L276", "the preparatory step"), ("bpW:w6:convergence", "L276", "the iteration"),
              ("bpW:w6:constants", "L277", "s_0, sigma_0, gamma_1"), ("bpW:w7:constdef", "L280", "beta_*")]),
    "bpW:w6:applicable": dict(
        H="Definition bpW:w6:wave-iteration", Q="none", C="the hypotheses of Proposition bpW:w6:convergence hold", S="none",
        note="Inline proof (L287-L293).",
        deps=[("bpW:w6:wave-iteration", "L285", "the data"), ("bpW:w6:convergence", "L285", "its hypotheses"),
              ("bpW:w6:prep-step", "L288", "(iv)-(v)"), ("bpW:w7:unpert-bounds", "L289", "(ii) k = 0"),
              ("bpW:w7:constdef", "L290", "(C4)"), ("bpW:w6:constants", "L292", "gamma_1"), ("bpW:w6:k0", "L289", "its hypothesis")]),
    "bpW:w6:freq-lip": dict(
        H="Definition bpW:w6:wave-iteration; D_nu = Pi_{nu-1}; Omega_{nu,J} at the Dirichlet label J >= 3; K_nu of "
          "Definition bpW:w6:sequences", Q="none",
        C="(D_nu,omega_nu,Omega_nu,K_nu)_{nu>=0} is admissible for (Pi,alpha) in the sense of Definition bpW:w7:family with "
          "eps_omega = 6 pi gamma alpha + 8 pi eps_0, eps_1 = 3 gamma alpha, eps_2 = 4 eps_0, theta = 425(1+M) max(gamma,gamma_1) "
          "<= theta_0, all <= alpha; Lipschitz constants for |.|_infty", S="none",
        deps=[("bpW:w6:wave-iteration", "L297", "the data"), ("bpW:w7:family", "L300", "admissible families"),
              ("bpW:w6:sequences", "L298", "K_nu"),
              ("stepW:w6:fl-size", "L306", PS), ("stepW:w6:fl-lip", "L309", PS), ("stepW:w6:fl-borel", "L313", PS)]),
    "stepW:w6:fl-size": dict(H="", Q="nu", C="the size bounds, all <= alpha", S="none",
        deps=[("bpW:w6:prep-step", "L306", "(ii)"), ("bpW:w6:convergence", "L307", "(ii)")]),
    "stepW:w6:fl-lip": dict(H="", Q="nu", C="the Lipschitz totals <= 425 max(gamma,gamma_1) M; theta <= theta_0", S="none",
        deps=[("bpW:w6:constants", "L312", "gamma, gamma_1"), ("bpW:w6:prep-step", "L309", "(ii)"), ("bpW:w6:convergence", "L309", "(ii)")]),
    "stepW:w6:fl-borel": dict(H="", Q="none", C="Borel measurability", S="none",
        deps=[("bpW:w6:convergence", "L313", "(i)"), ("bpW:w7:measurable", "L313", "Pi minus Xi Borel")]),
    "bpW:w6:exclusion": dict(
        H="Definition bpW:w6:wave-iteration", Q="none",
        C="Pi minus Pi_* subset E, W7's excluded set for the admissible family of Lemma bpW:w6:freq-lip; thresholds K_nu >= "
          "2^nu, levels alpha_nu <= check alpha", S="none", note="Inline proof (L323-L325).",
        deps=[("bpW:w6:freq-lip", "L319", "the admissible family"), ("bpW:w7:zones", "L319", "the excluded set E and zones"),
              ("bpW:w6:convergence", "L323", "(i)")]),
    "bpW:w6:final-freq": dict(
        H="Definition bpW:w6:wave-iteration", Q="for xi in Pi_*",
        C="|<k,omega_*(xi)>| >= check alpha/(2 A_k) for k != 0, |omega_*(xi) - omega^0(xi)|_infty <= eps_omega; omega_* is "
          "Lipschitz on Pi_* with constant <= N_A + theta", S="none", note="Inline proof (L335-L336).",
        deps=[("bpW:w6:convergence", "L335", "(ii)"), ("bpW:w6:freq-lip", "L336", "size and Lipschitz bounds"),
              ("bpW:w7:freqcoords", "L336", "(ii) N_A")]),
    "bpW:w6:tori": dict(
        H="Definition bpW:w6:wave-iteration; H_in = N_xi + P_xi of Lemma bpW:w5:action-angle(iv) on D(s,r) (P supplied by "
          "Proposition bpW:w5:initial); tilde Psi_xi(theta) = A_xi(Phi_P(Phi_*(theta))), nu_* = omega_*/(2pi)",
        Q="for xi in Pi_*, theta in T_{s_0/2} (resp. R^2)",
        C="(i) tilde Psi_xi is holomorphic on T_{s_0/2} with values in B_{rho_1} (if c_A(t + r^2) < rho_1^2), 1-periodic, real "
          "for real theta, normal part in W^{p+1/2}; (ii) (xi,theta) -> tilde Psi_xi(theta) continuous on Pi_* x R^2, nu_* "
          "Lipschitz; (iii) d_theta tilde Psi_xi(theta) nu_* = X_{H'}(tilde Psi_xi(theta)) in W^{p-1}; (iv) closeness with e_tor "
          "= M_{F,P} + e_Phi: |X| <= e_tor, |y| <= r^2 e_tor, ||u||_{a,p+1/2} + ||v||_{a,p+1/2} <= r e_tor on T_{s_0/2}, hence "
          "the displayed form of tilde Psi and ||hat tilde Psi|| <= r e_tor; (v) theta -> Z^{-1} Gamma(tilde Psi_xi(theta)) on R^2 "
          "is AnalyticOnNhd R into E_{a,p} (WaveSpace for a = p = 1)", S="e_tor explicit",
        deps=[("bpW:w5:action-angle", "L343", "A_xi, H_in, (ii), (v)"), ("bpW:w5:initial", "L344", "P"),
              ("bpW:w6:wave-iteration", "L342", "Phi_P, Phi_*, omega_*"), ("bpW:w3:main", "L358", "Gamma"),
              ("bpW:w0:ellap#WaveSpace", "L359", "the frozen WaveSpace"),
              ("stepW:w6:t-hol", "L363", PS), ("stepW:w6:t-cont", "L366", PS), ("stepW:w6:t-prep", "L368", PS),
              ("stepW:w6:t-bk", "L371", PS), ("stepW:w6:t-close", "L372", PS), ("stepW:w6:t-an", "L374", PS)]),
    "stepW:w6:t-hol": dict(H="", Q="theta", C="(i) holomorphy, reality, periodicity; normal part in P^{p_+}", S="none",
        deps=[("bpW:w6:convergence", "L363", "(iii)"), ("bpW:w5:action-angle", "L364", "holomorphic A_xi")]),
    "stepW:w6:t-cont": dict(H="", Q="none", C="(ii) continuity; nu_* Lipschitz", S="none",
        deps=[("bpW:w6:convergence", "L366", "(iii)"), ("bpW:w6:prep-step", "L366", "(iii)"), ("bpW:w6:final-freq", "L367", "Lipschitz")]),
    "stepW:w6:t-prep": dict(H="", Q="theta", C="X_{H_in}(Phi_P Phi_* theta) = d_theta(Phi_P o Phi_*) nu_*", S="none",
        deps=[("bpW:w6:invariance", "L368", "invariance in KAM coordinates"), ("bpW:w5:new-ham", "L369", "(iii)"),
              ("bpW:w6:strong", "L369", "strong conjugacy")]),
    "stepW:w6:t-bk": dict(H="", Q="theta", C="(iii) in Birkhoff coordinates", S="none",
        deps=[("bpW:w5:action-angle", "L371", "(v)"), ("stepW:w6:t-prep", "L371", "the KAM-coordinate identity")]),
    "stepW:w6:t-close": dict(H="", Q="theta", C="(iv) closeness", S="none",
        deps=[("bpW:w6:prep-step", "L372", "(iii)"), ("bpW:w6:convergence", "L372", "(iii)")]),
    "stepW:w6:t-an": dict(H="", Q="none", C="(v) real analyticity via Corollary bpW:w1:torus-analytic", S="none",
        note="The text cites the excluded Remark bpW:w3:class-remark for 'Gamma is analytic'; that fact is Theorem "
             "bpW:w3:flow(i), used here.",
        deps=[("bpW:w3:flow", "L374", "(i) Gamma analytic, (iv) real"), ("bpW:w3:coords", "L375", "Z"),
              ("bpW:w1:torus-analytic", "L376", "real-analytic tori from complex strips")]),
    "bpW:w6:to-w8": dict(
        kind="claim",
        H="for each shell, W8's choices r, t, rho_xi, Pi, alpha subject to Proposition bpW:w5:initial, eps_in(1 + 4 lambda/"
          "rho_xi) <= gamma alpha with lambda = alpha/M, c_A(t + r^2) < rho_1^2, Pi subset {|xi|_infty <= 1/2} Borel, alpha <= "
          "alpha_0", Q="for every value of the parameter eps_0 in [eps^flat_0, gamma_1 check alpha]",
        C="(a)-(c) of Theorem bpW:w6:tori and Lemmas bpW:w6:exclusion, bpW:w6:final-freq hold for every eps_0 in [eps^flat_0, "
          "gamma_1 check alpha]; with eps_0 = eps^flat_0: eps^flat_0/check alpha = 2 C^natural_2 sigma_P^{-t^natural/3}(eps/"
          "alpha)^{4/3}, M_{F,P} = c^natural_F sigma_P^{1-t^natural} alpha^{3/47} eps/alpha and the displayed bound on e_tor; "
          "Theorem bpW:w6:tori(i),(iii) on R^2 is the hypothesis of Corollary bpW:w3:transport-tori-weak", S="as displayed",
        note="Remark kept as a node: its starting-size computation (e_tor bound) and the return-trip statement are facts "
             "W8 may consume; its 'what W8 must still supply' list is administrative.",
        deps=[("bpW:w6:tori", "L391", "(i)-(v)"), ("bpW:w6:exclusion", "L387", "(a)"), ("bpW:w6:final-freq", "L390", "(b)"),
              ("bpW:w6:prep-step", "L398", "(v)"), ("bpW:w3:transport-tori-weak", "L405", "the return to Cartesian coordinates")]),
}

DELETE = []

COV = {
    "w6-iteration:prose-L7-L12": ("EXCLUDED", "introduction"),
    "w6-iteration:prose-L14-L20": ("EXCLUDED", "route paragraph (outline)"),
    "w6-iteration:prose-L22-L27": ("NODE bpW:w6#data", "fixed data and notation of W6"),
    "w6-iteration:prose-L417-L421": ("EXCLUDED", "ledger (administrative)"),
    "w6-iteration:prose-L423-L426": ("EXCLUDED", "order of constants (summary; each constant is defined in Definition "
                                     "bpW:w6:constants or W5/W7)"),
}
