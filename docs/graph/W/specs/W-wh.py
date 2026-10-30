# Writer spec for slice W-wh (blueprint-W/parts/w-headline.tex, all lines). Rendered by w_depgraph_fill.py.
F = "blueprint-W/parts/w-headline.tex"

NODES = {
    "bpW:wh:embedding#IsAnalyticTorusEmbedding": dict(
        H="typing data: a real normed space E (frozen: any NormedSpace R E); K : R^2 -> E", Q="E, K",
        C="defines: K is an analytic torus embedding iff K is Z^2-periodic, real analytic (blueprint: locally the "
          "restriction of a holomorphic map into E_C; frozen: AnalyticOnNhd R K univ), injective modulo Z^2 "
          "(K(theta) = K(theta') implies theta - theta' in Z^2), and DK(theta) is injective at every theta "
          "(KAM.Wave.IsAnalyticTorusEmbedding K)",
        S="none", deps=[]),
    "bpW:wh:dioph#IsDiophantine": dict(
        H="typing data: gamma, tau in R; nu in R^2 (frozen: KAM.IsDiophantine for n = 2)", Q="gamma, tau, nu",
        C="defines: nu is (gamma,tau)-Diophantine iff |k.nu| >= gamma |k|_1^{-tau} for all k in Z^2 \\ {0}, "
          "|k|_1 = |k_1| + |k_2| (the frozen track-K definition KAM.IsDiophantine, transcribed here)",
        S="none", deps=[]),
    "bpW:wh:nlw2": dict(
        H="m > 0 (frozen hm : 0 < m); the data fixed at L13-L16: weights a = p = 1, E = E_{1,1} with the max norm, "
          "U_m, V_m, G_q, P = (0,infinity)^2, r(I) = sqrt(I_1+I_2), B_h = {I : max_i |I_i| < h}",
        Q="for every m > 0, there exist r_0 > 0, C > 0, tau > 1, eta : (0,r_0) -> [0,infinity) with eta(r) -> 0 as "
          "r -> 0+, a Borel set Gamma subset {I in P : r(I) < r_0}, a continuous nu : Gamma -> R^2 and maps "
          "K_I = (Q_I,P_I) : R^2 -> E (I in Gamma) with (I,theta) -> K_I(theta) continuous on Gamma x R^2; then "
          "(1)-(6) hold with inner quantifiers: (2) for every I in Gamma there is gamma_I > 0; (3)-(5) for every I in "
          "Gamma, theta (resp. theta_0, t, x) and j >= 1; (6) for all I, I' in Gamma and theta, theta'",
        C="(1) Leb_2(Gamma cap B_h)/Leb_2(P cap B_h) -> 1 as h -> 0+; (2) nu(I) is (gamma_I,tau)-Diophantine and "
          "nu(I) -> (lambda_1,lambda_2)/(2 pi) as I -> 0 in Gamma; (3) each K_I is an analytic torus embedding, "
          "sup_theta ||K_I(theta) - K^0_I(theta)||_E <= eta(r(I)) r(I) and sup_theta ||K_I(theta)||_E <= C r(I); "
          "(4) D_{nu(I)} Q_{I,j} = lambda_j P_{I,j} and D_{nu(I)} P_{I,j} = -lambda_j Q_{I,j} - G_q(Q_I)_j for all "
          "theta, j >= 1 (frozen: HasDerivAt of t -> coeff (K I (theta + t nu I)).i j at t = 0); (5) for every "
          "theta_0, u(t,x) = U_m(Q_I(theta_0 + t nu(I)))(x) is real analytic near every point of R x [0,pi], is a "
          "classical solution of u_tt = u_xx - m u - u^3 on R, u_t(t,.) = V_m(P_I(theta_0 + t nu(I))), and "
          "sup_{t, x in [0,pi]} (|u| + |u_x| + |u_t|) <= C r(I) (frozen: u_x as derivWithin on [0,pi]); (6) "
          "K_I(theta) = K_I'(theta') implies I = I' and theta - theta' in Z^2",
        S="r_0, C, tau, eta, Gamma, nu, K are chosen after m and before I, theta, theta_0; they may depend on m; "
          "gamma_I is chosen per I (it may degenerate as I -> 0); C is common to (3) and (5); no uniformity in m",
        note="Root of track W. Its proof (assembly) is milestone W8, not yet in the corpus (W4-W8 pending); until then "
             "DEPS lists only the statement-level definitions. W2 (bpW:w2:clause5) supplies conclusion (5) from (3)-(4) "
             "and becomes a dependency when W8 is added. D_nu (bpW:wh:Dnu) is inlined in the frozen statement.",
        deps=[("bpW:w0:mass", "L42", "for every m > 0 (hm)"),
              ("bpW:w0:ellap#WaveSpace", "L44", "K_I : R^2 -> E, E = E_{1,1} (frozen WaveSpace)"),
              ("bpW:wh:dioph#IsDiophantine", "L50", "(2) nu(I) is (gamma_I,tau)-Diophantine"),
              ("bpW:w0:basis#lam", "L50", "(2) limit (lambda_1,lambda_2)/(2 pi); (4) lambda_j"),
              ("bpW:wh:embedding#IsAnalyticTorusEmbedding", "L51", "(3) each K_I is an analytic torus embedding"),
              ("bpW:w0:periodone#linearTorus", "L52", "(3) closeness to K^0_I"),
              ("bpW:w0:ellap#coeff", "L54", "(4) the coefficients Q_{I,j}, P_{I,j} (frozen coeff)"),
              ("bpW:w0:Gq#cubicGrad", "L55", "(4) the cubic gradient G_q(Q_I(theta))_j"),
              ("bpW:w0:reconstruction#reconU", "L57", "(5) u = U_m(Q_I(theta_0 + t nu(I)))"),
              ("bpW:w0:nlw#IsClassicalSolution", "L58", "(5) classical solution of (bpW:w0:eq) on R"),
              ("bpW:w0:reconstruction#reconV", "L59", "(5) u_t = V_m(P_I(theta_0 + t nu(I)))")]),
}

DELETE = ["bpW:wh:lintorus", "bpW:wh:Dnu", "bpW:wh:reading", "bpW:wh:weakenings"]

COV = {
    "bpW:wh:lintorus": ("NODE bpW:w0:periodone#linearTorus",
                        "restates Convention bpW:w0:periodone; the frozen KAM.Wave.linearTorus is bound to that node"),
    "bpW:wh:Dnu": ("NODE bpW:wh:nlw2", "notation D_nu K = DK nu used in (4); the frozen statement inlines it as a "
                   "HasDerivAt along t -> theta + t nu at t = 0"),
    "bpW:wh:reading": ("EXCLUDED", "administrative remark (reading of the statement: quantifier order, recorded in the "
                       "SOURCE_QUANTIFIERS and CONSTANT_SCOPE of bpW:wh:nlw2; pointers to W2/W8; deviations); no proof "
                       "consumes it"),
    "bpW:wh:weakenings": ("EXCLUDED", "administrative remark (declared weakenings W-A2, D30 Q3); no proof consumes it"),
    "w-headline:prose-L3-L3": ("EXCLUDED", "status line (\\proposed), superseded by the owner freeze D41"),
    "w-headline:prose-L5-L9": ("EXCLUDED", "introduction (provenance, D30)"),
    "w-headline:prose-L13-L16": ("NODE bpW:wh:nlw2", "fixes the data of the statement (m, a = p = 1, E, U_m, V_m, "
                                 "G_q, P, r(I), B_h)"),
}
