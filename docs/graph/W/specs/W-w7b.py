# Writer spec for slice W-w7b (blueprint-W/parts/w7-measure.tex L460-end). Wave 2. Rendered by w_depgraph_fill.py.
F = "blueprint-W/parts/w7-measure.tex"
STEP_CONTEXT = True
SYMBOL_EDGES = True
SYMBOL_OVERRIDE = {"bpW:w0:basis#lam": r"\\lambda_(?:[1-9JjiIn]|\{[jJiI])",
                   "bpW:w0:basis#sineMode": r"\\Lean\{sineMode"}
PS = "proof step"
FIX = "the fixed data of L339-L343 (bpW:w7:basic#data): Pi, alpha in (0,alpha_0], an admissible family, rho, rho_zeta"

NODES = {
    "bpW:w7:prep": dict(
        H=FIX, Q="none", C="Xi is Borel and Leb(Xi) <= C_P rho_zeta D_A^{-1} hat alpha^{8/11}", S="C_P depends only on m",
        deps=[("bpW:w7:zones", "L463", "Xi"), ("bpW:w7:constdef", "L463", "C_P"), ("bpW:w7:basic#data", "L463", "rho_zeta"),
              ("bpW:w7:sep", "L466", "S_{0l} empty"),
              ("stepW:w7:prep-0", "L467", PS), ("stepW:w7:prep-plus", "L469", PS), ("stepW:w7:prep-minus-group", "L474", PS),
              ("stepW:w7:prep-j0", "L482", PS), ("stepW:w7:prep-n", "L494", PS), ("stepW:w7:prep-X", "L497", PS),
              ("stepW:w7:prep-sum", "L500", PS)]),
    "stepW:w7:prep-0": dict(H="", Q="k != 0", C="Leb(S_k0) <= 8 rho_zeta hat alpha/(|k| A_k D_A)", S="none",
        deps=[("bpW:w7:zone", "L468", "psi = 0")]),
    "stepW:w7:prep-plus": dict(H="", Q="k != 0", C="the Lambda^+ zones not in X sum to <= 32 rho_zeta hat alpha |k|^2/(vartheta^3 "
        "A_k D_A)", S="none", deps=[("bpW:w7:dichotomy", "L471", "dichotomy"), ("bpW:w7:zone", "L470", "zone estimate"),
                                    ("bpW:w7:count", "L472", "(i)")]),
    "stepW:w7:prep-minus-group": dict(H="", Q="k, n", C="grouping of the Lambda^- zones by n = i - j and the inclusion "
        "S_{k,ij} subset Q_{knj} subset Q_{knj_0}", S="none",
        deps=[("bpW:w7:zone", "L477", "zone estimate"), ("bpW:w7:unpert-bounds", "L479", "(iii)")]),
    "stepW:w7:prep-j0": dict(H="", Q="k, n", C="with j_0 = ceil((A_k/hat alpha)^{4/11}) the union is <= (8 rho_zeta n/(|k| D_A))"
        "(3 + a_kappa)(hat alpha/A_k)^{8/11}", S="none",
        deps=[("bpW:w7:zone", "L484", "psi = n"), ("bpW:w7:ext-ennreal", "L493", "ceil(x) <= 2x and real powers"),
              ("stepW:w7:prep-minus-group", "L486", "the grouping")]),
    "stepW:w7:prep-n": dict(H="", Q="k", C="summing over n and doubling", S="none", deps=[("stepW:w7:prep-j0", "L496", "per n")]),
    "stepW:w7:prep-X": dict(H="", Q="none", C="the exceptional zones have total measure <= 4 N_X rho_zeta hat alpha K_*/(vartheta "
        "sigma_X D_A)", S="none", deps=[("bpW:w7:Xzones", "L498", "a = hat alpha")]),
    "stepW:w7:prep-sum": dict(H="", Q="none", C="summing over k gives the bound with C_P; Borel", S="none",
        deps=[("bpW:w7:count", "L502", "(iii)"), ("bpW:w7:measurable", "L503", "Borel"),
              ("stepW:w7:prep-0", "L501", "l = 0"), ("stepW:w7:prep-plus", "L501", "Lambda^+"), ("stepW:w7:prep-n", "L501", "Lambda^-"),
              ("stepW:w7:prep-X", "L502", "X")]),
    "bpW:w7:iter": dict(
        H=FIX, Q="none",
        C="E_it = union over nu and (k,l) in Z with |k| > K_{nu-1} of R^nu_kl is Borel and Leb(E_it) <= rho_zeta D_A^{-1}(Z_3(8 + "
          "32 vartheta^{-3} + 16(2 + a_kappa) vartheta^{-2}) check alpha^{2/3} + 32 Z_3 vartheta^{-1}(eps_1 + eps_2) + 4 N_X K_*^2 "
          "vartheta^{-1} sigma_X^{-1} check alpha)", S="constants depend only on m",
        deps=[("bpW:w7:family", "L511", "R^nu_kl"), ("bpW:w7:basic#data", "L512", "rho_zeta"),
              ("stepW:w7:it-plus", "L518", PS), ("stepW:w7:it-group", "L521", PS), ("stepW:w7:it-j0", "L527", PS),
              ("stepW:w7:it-n", "L533", PS), ("stepW:w7:it-sum", "L537", PS), ("stepW:w7:it-X", "L541", PS)]),
    "stepW:w7:it-plus": dict(H="", Q="nu, k", C="the l = 0 and Lambda^+ zones as in the preparatory case with check alpha",
        S="none", deps=[("stepW:w7:prep-0", "L519", "as there"), ("stepW:w7:prep-plus", "L519", "as there")]),
    "stepW:w7:it-group": dict(H="", Q="nu, k, n", C="R^nu_{k,ij} subset Q_{knj}, decreasing in j", S="none",
        deps=[("bpW:w7:family", "L522", "(H2)"), ("bpW:w7:unpert-bounds", "L522", "(iii)")]),
    "stepW:w7:it-j0": dict(H="", Q="nu, k, n", C="with j_0 = ceil((A_k/check alpha)^{1/3}) the bound", S="none",
        deps=[("bpW:w7:zone", "L528", "zone estimate"), ("stepW:w7:it-group", "L529", "the grouping")]),
    "stepW:w7:it-n": dict(H="", Q="nu, k", C="summing over n and the sign", S="none", deps=[("stepW:w7:it-j0", "L534", "per n")]),
    "stepW:w7:it-sum": dict(H="", Q="none", C="summing over nu and k", S="none",
        deps=[("bpW:w7:count", "L538", "(ii), (iii)"), ("stepW:w7:it-n", "L539", "per k"), ("stepW:w7:it-plus", "L539", "per k")]),
    "stepW:w7:it-X": dict(H="", Q="none", C="the exceptional zones; Borel", S="none",
        deps=[("bpW:w7:Xzones", "L542", "a = check alpha"), ("bpW:w7:measurable", "L543", "Borel")]),
    "bpW:w7:measurable": dict(
        H=FIX, Q="none", C="every zone S_kl, R^nu_kl, Q_knj is Borel, and so are Xi, E_it, E and Pi minus E", S="none",
        deps=[("bpW:w7:zones", "L551", "the zones"), ("bpW:w7:family", "L551", "E"),
              ("stepW:w7:meas-cont", "L555", PS), ("stepW:w7:meas-union", "L558", PS)]),
    "stepW:w7:meas-cont": dict(H="", Q="none", C="each phi_kl is continuous on its Borel domain", S="none",
        deps=[("bpW:w7:omega0", "L556", "affine"), ("bpW:w7:family", "L556", "(H1)-(H2)")]),
    "stepW:w7:meas-union": dict(H="", Q="none", C="countable unions", S="none",
        deps=[("bpW:w7:ext-borel", "L559", "Borel sets"), ("stepW:w7:meas-cont", "L559", "continuity")]),
    "bpW:w7:measure": dict(
        H="m > 0 and the constants of Definition bpW:w7:constdef; Pi subset {|xi|_infty <= 1/2} Borel with rho = diam_infty Pi; "
          "0 < alpha <= alpha_0; an admissible family (Definition bpW:w7:family)", Q="for all such Pi, alpha, families",
        C="E is Borel and Leb(E) <= C_7 rho alpha^{32/47}; equivalently Leb(omega^0(E)) <= (C_P + C_I) N_A rho alpha^{32/47}",
        S="C_7 depends on m only",
        deps=[("bpW:w7:constdef", "L564", "C_7"), ("bpW:w7:family", "L566", "admissible families, E"),
              ("bpW:w7:measurable", "L566", "E Borel"),
              ("stepW:w7:assemble", "L572", PS), ("stepW:w7:return", "L577", PS)]),
    "stepW:w7:assemble": dict(H="", Q="none", C="Leb(E) <= Leb(Xi) + Leb(E_it) and the exponent substitutions", S="none",
        deps=[("bpW:w7:ext-borel", "L573", "subadditivity"), ("bpW:w7:prep", "L574", "preparatory zones"),
              ("bpW:w7:iter", "L574", "iteration zones")]),
    "stepW:w7:return": dict(H="", Q="none", C="rho_zeta/D_A <= L_A rho", S="none",
        deps=[("bpW:w7:freqcoords", "L578", "(ii)")]),
    "bpW:w7:melnikov": dict(
        H="the setting of Theorem bpW:w7:measure", Q="xi as stated",
        C="(i) for xi in Pi minus Xi and (k,l) in Z: |<k,omega^0> + <l,Omega^0>| >= hat alpha hat w(l)/A_k, in particular "
          "|<k,omega^0>| >= hat alpha/A_k for k != 0; (ii) for xi in D_nu minus the R^nu_kl (|k| > K_{nu-1}): the bound with check "
          "alpha <l>/A_k; (iii) for every frequency pair and l in Lambda: |<l,Omega'>| >= 2 beta_* <l> >= hat alpha <l>",
        S="none", note="Inline proof (L598).",
        deps=[("bpW:w7:measure", "L586", "the setting"), ("bpW:w7:zones", "L598", "negation of the zone definitions"),
              ("bpW:w7:sep", "L598", "(iii)")]),
    "bpW:w7:density-sec#data": dict(
        new=True, kind="definition", title="Positive quadrant and max-norm balls of clause (1)", stmt=f"{F}#bpW:w7:density-sec@L604-L606",
        proof="-", H="none", Q="h > 0",
        C="clause (1) compares Gamma with P = (0,infinity)^2 in the max-norm ball B_h = (-h,h)^2; density is obtained on "
          "shrinking action shells (KP96 Step 5)", S="none",
        note="Unlabelled prose L604-L606 fixing P and B_h for Theorem bpW:w7:density. It restates the sets of clause (1) of "
             "the headline; no edge to the root (that would be circular once W8 proves the root).",
        deps=[]),
    "bpW:w7:shells": dict(
        H="q in (0,1), t_0 in (0,1/2]", Q="k; a > 0",
        C="defines t_k = q^k t_0, the shells R_k = (0,t_k)^2 minus (0,t_{k+1})^2 = {I in (0,t_k)^2 : max I_i >= t_{k+1}}, and "
          "U_{-a} R_k = {I in R_k : dist_infty(I, R^2 minus R_k) > a}", S="none", deps=[]),
    "bpW:w7:shell-geom": dict(
        H="the shells of Definition bpW:w7:shells", Q="k; 0 < a <= t_k",
        C="(i) the shells R_l, l >= k, are pairwise disjoint Borel with union (0,t_k)^2 and Leb(R_l) = (1-q^2) t_l^2; (ii) "
          "Leb(R_k minus U_{-a} R_k) <= 7 a t_k; (iii) R_k subset {|I|_infty >= t_{k+1}} and diam_infty R_k <= t_k", S="none",
        deps=[("bpW:w7:shells", "L617", "the shells"), ("stepW:w7:partition", "L622", PS), ("stepW:w7:layer", "L625", PS),
              ("stepW:w7:shell-size", "L630", PS)]),
    "stepW:w7:partition": dict(H="", Q="I", C="(i)", S="none", deps=[("bpW:w7:ext-ball", "L624", "Leb of boxes")]),
    "stepW:w7:layer": dict(H="", Q="I", C="(ii) the boundary layer bound", S="none", deps=[]),
    "stepW:w7:shell-size": dict(H="", Q="none", C="(iii)", S="none", deps=[]),
    "bpW:w7:density": dict(
        H="q, t_k, R_k as in Definition bpW:w7:shells; Gamma subset P Borel with eps_k = Leb(R_k minus Gamma)/Leb(R_k) -> 0",
        Q="for all such Gamma",
        C="lim_{h -> 0+} Leb(Gamma cap B_h)/Leb(P cap B_h) = 1 in [0,infinity] (volume on Fin 2 -> R, B_h = Metric.ball 0 h), "
          "clause (1) of KAM.Wave.nlw2; for t_{k+1} < h <= t_k the ratio lies in [1 - q^{-2} sup_{l>=k} eps_l, 1]", S="none",
        deps=[("bpW:w7:shells", "L636", "the shells"), ("bpW:w7:density-sec#data", "L636", "P and B_h"),
              ("stepW:w7:den", "L644", PS), ("stepW:w7:upper", "L646", PS), ("stepW:w7:lower", "L648", PS),
              ("stepW:w7:limit", "L654", PS)]),
    "stepW:w7:den": dict(H="", Q="h > 0", C="Leb(P cap B_h) = h^2", S="none", deps=[("bpW:w7:ext-ball", "L645", "balls")]),
    "stepW:w7:upper": dict(H="", Q="h", C="the ratio is <= 1", S="none", deps=[]),
    "stepW:w7:lower": dict(H="", Q="h", C="Leb(Gamma cap B_h) >= h^2(1 - bar eps_k/q^2)", S="none",
        deps=[("bpW:w7:shell-geom", "L650", "(i)")]),
    "stepW:w7:limit": dict(H="", Q="none", C="the limit is 1 (squeeze; ENNReal quotient, nhdsWithin 0 (Ioi 0))", S="none",
        deps=[("bpW:w7:ext-ennreal", "L655", "squeeze"), ("stepW:w7:lower", "L655", "lower bound"), ("stepW:w7:upper", "L655", "upper bound")]),
    "bpW:w7:shell-est": dict(
        H="the shells; for every k, alpha_k in (0,alpha_0] with alpha_k <= t_k, a Borel Pi_k with U_{-alpha_k} R_k subset Pi_k "
          "subset (0,t_k)^2, and an admissible family for (Pi_k,alpha_k) with excluded set E_k such that Gamma contains R_k cap "
          "(Pi_k minus E_k)", Q="for every k",
        C="eps_k <= (7 alpha_k + C_7 alpha_k^{32/47})/((1-q^2) t_k) <= (7 + C_7) alpha_k^{32/47}/((1-q^2) t_k); hence eps_k -> 0 "
          "whenever alpha_k^{32/47}/t_k -> 0, and Theorem bpW:w7:density applies", S="C_7 depends on m only",
        note="Inline proof (L669-L672).",
        deps=[("bpW:w7:shell-geom", "L670", "(ii), (iii)"), ("bpW:w7:measure", "L670", "the measure bound"),
              ("bpW:w7:density", "L666", "conclusion"), ("bpW:w7:family", "L663", "admissible families")]),
    "bpW:w7:exponents": dict(
        kind="claim",
        H="the shells and Theorem bpW:w7:measure; KP96's smallness alpha >= c_1 t^{3/2}", Q="t -> 0",
        C="the excluded fraction is <= C alpha^{32/47}/t; density needs alpha = o(t^{47/32}); the admissible window is "
          "t^{3/2} <~ alpha = o(t^{47/32}); the explicit choice alpha(t) = t^{95/64} gives alpha^{32/47}/t = t^{1/94} -> 0, "
          "t^{3/2}/alpha = t^{1/64} -> 0 and alpha(t) <= t for t <= 1", S="none",
        note="Remark kept as a node: W8 cites it (4x) for the choice alpha(t) = t^{95/64}.",
        deps=[("bpW:w7:measure", "L679", "the exponent 32/47"), ("bpW:w7:freqcoords", "L678", "N_A, D_A")]),
    "bpW:w7:dioph": dict(
        H="c > 0, omega in R^2 with |<k,omega>| >= c/A_k for all k in Z^2 minus 0 (A_k = 1 + |k|^24)", Q="for all such c, omega",
        C="nu = omega/(2pi) satisfies KAM.IsDiophantine (c/(4 pi)) 24 nu, i.e. (c/(4pi))/(sum |k_i|)^24 <= |sum k_i nu_i| for "
          "k != 0", S="none",
        deps=[("bpW:wh:dioph#IsDiophantine", "L699", "the frozen KAM.IsDiophantine"),
              ("bpW:w7:indexdef", "L698", "A_k with tau = 24"),
              ("stepW:w7:dioph-base", "L703", PS), ("stepW:w7:dioph-scale", "L706", PS)]),
    "stepW:w7:dioph-base": dict(H="", Q="k != 0", C="A_k <= 2 S^24 with S = sum |k_i| >= 1", S="none", deps=[]),
    "stepW:w7:dioph-scale": dict(H="", Q="k != 0", C="|sum k_i nu_i| >= c/(4 pi S^24)", S="none",
        deps=[("stepW:w7:dioph-base", "L707", "A_k <= 2 S^24")]),
    "bpW:w7:dioph-use": dict(
        kind="claim",
        H="the final parameter set of a shell with |<k,omega_*>| >= check alpha/(2 A_k)", Q="I in that shell's part of Gamma",
        C="gamma_I = check alpha_k/(8 pi) > 0 (check alpha_k = alpha_k^{48/47}) with the exponent tau = 24 > 1; gamma_I depends "
          "on the shell and tends to 0 as I -> 0", S="gamma_I per shell",
        note="Remark kept as a node: W8 cites it for gamma_I in clause (2). Its pointer to bpW:w6:final-freq is a forward "
             "pointer (the premise is supplied by W8).",
        deps=[("bpW:w7:dioph", "L715", "with c = check alpha/2")]),
    "bpW:w7:limit": dict(
        H="Gamma subset union R_k; omega_* : Gamma -> R^2 with sup_{Gamma cap R_k} |omega_* - omega^0|_infty <= e_k, e_k -> 0",
        Q="for all such Gamma, omega_*",
        C="nu = omega_*/(2pi) satisfies nu(I) -> lambda_J/(2pi) as I -> 0 in Gamma, i.e. Tendsto nu (nhdsWithin 0 Gamma) (nhds "
          "fun i => lam m hm (i : Nat).succPNat/(2 pi))", S="none",
        deps=[("bpW:w7:shells", "L721", "the shells"), ("bpW:w7:omega0", "L722", "omega^0"),
              ("stepW:w7:lim-index", "L727", PS), ("stepW:w7:lim-est", "L730", PS)]),
    "stepW:w7:lim-index": dict(H="", Q="I", C="small |I|_infty forces a large shell index", S="none",
        deps=[("bpW:w7:shell-geom", "L729", "(iii)")]),
    "stepW:w7:lim-est": dict(H="", Q="eps > 0", C="|nu(I) - lambda_J/(2pi)| <= (e_k + N_A |I|_infty)/(2pi), whence the limit",
        S="none", deps=[("bpW:w7:freqcoords", "L731", "N_A"), ("stepW:w7:lim-index", "L732", "shell index")]),
}

DELETE = ["bpW:w7:errata", "bpW:w7:interface"]

COV = {
    "bpW:w7:errata": ("EXCLUDED", "administrative remark (pages read, suspected P96-K errata, deviations)"),
    "bpW:w7:interface": ("EXCLUDED", "administrative remark (consumed and supplied; pointers)"),
    "w7-measure:prose-L604-L606": ("NODE bpW:w7:density-sec#data", "P and B_h of clause (1)"),
}
