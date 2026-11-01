# Track LP, slice LP-m4a, wave 2: MAIN L272-L379, Lemmas 9-11 (exponential averaging with evolving slow variables).
# Lemmas 9-11 are generic in the numbers n ≥ 1 of fast and m ≥ 0 of slow pairs and in the slow set Z; they feed the
# drift supplier Lemma 12 (route lpM:L14#route-L12). The contour estimate of Lemma 9 is also used by Lemma 13 (the
# Lean route). AMENDED N5: the flow existence, the Lie-series identification and c_D are sketched in MAIN; they are
# kept as steps with SOURCE_GAP notes (they lie on route-L12 only, not on the Lean route).

L9H = ("context of the proof of lpM:L9: integers n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; "
       "D = 2n + 2m; the domains D_ρ (23) and the norm (24)")
L9Q = "for every 1 ≤ ρ ≤ 4, 0 < σ < ρ - 1 and periodic holomorphic vector fields V, W (inherited from lpM:L9)"
L10H = ("context of the proof of lpM:L10: the setting of lpM:L9; ω satisfying (5); h_0 = ω·(I - I^0) + c_0; a real "
        "holomorphic H = h_0 + g + f with g independent of θ; E = ‖X_f‖_ρ, G = ‖X_g‖_ρ; a loss 0 < σ < ρ - 1")
L10Q = "for every such H and loss σ (inherited from lpM:L10)"
L11H = ("context of the proof of lpM:L11: the setting of Lemmas 9-10; H = h_0 + F with ‖X_F‖_3 ≤ ε; an integer N ≥ 1 "
        "with A ε N^{τ+1} ≤ q_D (30); local data ρ_j = 3 - j/N, g_0 = 0, f_0 = F")
L11Q = "for every such H, ε and N (inherited from lpM:L11)"
N5 = ("SOURCE_GAP: AMENDED N5 (AMENDMENTS.md L14): MAIN only sketches the flow existence, the Lie-series identification "
      "and the choice of c_D; they matter only for the optional packages 9-11 (route lpM:L14#route-L12), not for the "
      "Lean route through Lemma 13")

NODES = {
    # ---------------- Lemma 9
    "lpM:L9": dict(
        kind="lemma", title="Lemma 9: Fourier, Cauchy and commutator estimates in the norm (24)", stmt="L9:279-296",
        proof="L9:298-304",
        H="integers n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; the domains D_ρ (23) and the norm (24) "
          "with D = 2n + 2m",
        Q="for every 1 ≤ ρ ≤ 4, every loss 0 < σ < ρ - 1, all periodic holomorphic vector fields V, W and every K",
        C="norms are monotone under restriction; the mean and complementary Fourier projections have norm at most one; "
          "‖[V,W]‖_{ρ-σ} ≤ (2D/σ)‖V‖_ρ‖W‖_ρ (25); the Fourier tail with ¦k¦_1 > K on a strip narrowed by σs has norm at "
          "most e^{-σsK}‖V‖_ρ; a uniform supremum bound for V̂ on D_4 gives a finite bound on ‖V‖_3 depending only on "
          "that bound, n and s",
        S="the bound on ‖V‖_3 depends only on the supremum bound, n and s",
        deps=[("lpM:L9#domains", "279-284", "the domains (23)"),
              ("lpM:L9#norm", "285-291", "the norm (24)"),
              ("lpM:L9#sup-to-fourier", "298-299", "the supremum-to-Fourier bound"),
              ("lpM:L9#commutator", "302-304", "(25)"),
              ("lpM:L9#projections-tail", "304", "monotonicity, projections and the tail")]),
    "lpM:L9#domains": dict(
        kind="definition", title="the complex domains D_rho (23): action, angle-strip and slow max-norm tube",
        stmt="L9:279-285", proof="-",
        H="n ≥ 1, m ≥ 0; a nonempty real compact Z ⊂ ℝ^{2m}; r, b, s > 0; I^0", Q="for every 1 ≤ ρ ≤ 4",
        C="D_ρ = {‖I - I^0‖_∞ < ρr, ¦Im θ¦_∞ < ρs, dist_∞(z, Z) < ρb} (23); the slow tube uses the maximum norm and Z "
          "need not be a polydisk; Hamiltonian fields use the standard constant symplectic form in (I, θ, z), with "
          "blocks rs and b^2 after scaling",
        S="none"),
    "lpM:L9#norm": dict(
        kind="definition", title="scaled components and the weighted Fourier norm (24)", stmt="L9:285-291", proof="-",
        H="the domains D_ρ (lpM:L9#domains); D = 2n + 2m",
        Q="for every periodic holomorphic vector field V and 1 ≤ ρ ≤ 4",
        C="V̂ = (V_I/r, V_θ/s, V_z/b) and ‖V‖_ρ = Σ_{k ∈ ℤ^n} sup_{‖I - I^0‖ < ρr, dist(z,Z) < ρb} ¦V̂_k(I,z)¦_∞ e^{ρs¦k¦_1} (24)",
        S="none",
        deps=[("lpM:L9#domains", "289", "the supremum runs over the action and slow parts of D_ρ")]),
    "lpM:L9#sup-to-fourier": dict(
        kind="step", title="contour shift: a sup bound M on width 4s gives |V_k| <= M e^{-4s|k|_1}, hence ||V||_3 <= M((1+e^{-s})/(1-e^{-s}))^n",
        stmt="L9:296-296", proof="L9:298-299", H=L9H, Q=L9Q,
        C="a supremum bound M for V̂ on D_4 gives coefficient bound M e^{-4s¦k¦_1} on the parameter domain of D_3 (limits "
          "from narrower contours), and summing at width 3s gives ‖V‖_3 ≤ M Σ_k e^{-s¦k¦_1} = M((1 + e^{-s})/(1 - e^{-s}))^n",
        S="the bound depends only on M, n and s",
        deps=[("lpM:ext-fourier-contour", "298", "Fourier coefficients as torus integrals and the contour shift"),
              ("lpM:L9#norm", "299", "summing the coefficients in the norm (24)"),
              ("lpM:L9#domains", "298", "the strip of width 4s of D_4")]),
    "lpM:L9#banach-algebra": dict(
        kind="step", title="products have convolution coefficients: the Banach-algebra estimate",
        stmt="L9:300-300", proof="L9:300-300", H=L9H, Q=L9Q,
        C="products of Fourier series have convolution coefficients and ¦k + l¦_1 ≤ ¦k¦_1 + ¦l¦_1, so the weighted norm "
          "is submultiplicative; absolute convergence on smaller domains justifies multiplication and differentiation",
        S="none",
        deps=[("lpM:L9#norm", "300", "the weights e^{ρs¦k¦_1} of (24)")]),
    "lpM:L9#cauchy-derivative": dict(
        kind="step", title="Cauchy: derivative bound 1/sigma in scaled action and slow coordinates; angle factor 1/(e sigma)",
        stmt="L9:302-303", proof="L9:302-303", H=L9H, Q=L9Q,
        C="a complex disk of radius σr or σb about a point of D_{ρ-σ} lies in D_ρ (triangle inequality for dist to Z), so "
          "Cauchy's formula gives derivative bound 1/σ in scaled coordinates; for angles s¦k_j¦e^{-σs¦k¦_1} ≤ 1/(eσ)",
        S="none",
        deps=[("lpM:ext-cauchy-estimates", "302", "Cauchy's formula on the disks"),
              ("lpM:L9#domains", "302", "the disks lie in the larger tube"),
              ("lpM:L9#norm", "303", "the angle derivative acts on the weights of (24)")]),
    "lpM:L9#commutator": dict(
        kind="display", title="(25): ||[V,W]||_{rho-sigma} <= (2D/sigma) ||V||_rho ||W||_rho", stmt="L9:292-295",
        proof="L9:302-304", H=L9H, Q=L9Q,
        C="each of the D terms in a component of DV W - DW V is bounded by the product of the norms divided by σ, giving "
          "‖[V,W]‖_{ρ-σ} ≤ (2D/σ)‖V‖_ρ‖W‖_ρ (25)",
        S="none",
        deps=[("lpM:L9#cauchy-derivative", "304", "the derivative bounds 1/σ and 1/(eσ)"),
              ("lpM:L9#banach-algebra", "304", "products of the derivative and the field")]),
    "lpM:L9#projections-tail": dict(
        kind="step", title="monotonicity; mean and complementary projections have norm <= 1; tail bound e^{-sigma s K}",
        stmt="L9:292-296", proof="L9:304-304", H=L9H, Q=L9Q,
        C="norms are monotone under restriction; removing the zero coefficient proves that the mean and complementary "
          "Fourier projections have norm at most one; extracting e^{-σsK} bounds the tail with ¦k¦_1 > K on the strip "
          "narrowed by σs by e^{-σsK}‖V‖_ρ",
        S="none",
        deps=[("lpM:L9#norm", "304", "the norm (24) is a weighted sum over k")]),
    # ---------------- Lemma 10
    "lpM:L10": dict(
        kind="lemma", title="Lemma 10: cohomological equation (26) and a controlled Lie step (27)", stmt="L10:308-321",
        proof="L10:323-349",
        H="the setting of lpM:L9 (n, m, Z, r, b, s); ω satisfying (5); h_0 = ω·(I - I^0) + c_0; a real holomorphic "
          "H = h_0 + g + f with g independent of θ; E = ‖X_f‖_ρ, G = ‖X_g‖_ρ",
        Q="for every such H and every loss 0 < σ < ρ - 1; constants c_D, B_D > 0 depending only on D are fixed first",
        C="there is a Hamiltonian generator χ, real on real points, with ω·∂_θχ = f - ⟨f⟩ and ‖X_χ‖_{ρ-σ/2} ≤ Aσ^{-τ}E =: u, "
          "A = γ^{-1} max{1, (2τ/(es))^τ} (26); if u/σ ≤ c_D its time-one map φ is holomorphic, real, symplectic and "
          "periodic-equivariant on D_{ρ-σ}, with H∘φ = h_0 + g + ⟨f⟩ + f_+ and ‖X_{f_+}‖_{ρ-σ} ≤ B_D (u/σ)(G + E) (27); "
          "the map and the negative-time map move points by at most u in scaled coordinates where the collar is "
          "available, their derivatives differ from the identity by at most a dimension constant times u/σ on a further "
          "half-collar, and they are mutual inverses on their common inner domain",
        S="c_D, B_D depend only on D; the constants do not depend on r, b, Z, I^0 or the coefficients of the scaled "
          "symplectic form",
        deps=[("lpM:L10#homological", "323-328", "the generator χ and (26)"),
              ("lpM:L10#flow-existence", "340", "the time-one map, its displacement, inverse and symplecticity"),
              ("lpM:L10#remainder", "342-349", "the exact remainder (29) and (27)"),
              ("lpM:L9#norm", "308", "the norms ‖X_f‖_ρ of (24)"),
              ("lpM:s1:dioph", "308", "ω satisfies the Diophantine condition (5)")]),
    "lpM:L10#homological": dict(
        kind="step", title="chi_k = f_k/(i k.omega): (26), the scalar series and reality",
        stmt="L10:309-314", proof="L10:323-328", H=L10H, Q=L10Q,
        C="χ_0 = 0 and χ_k = f_k/(ik·ω) for k ≠ 0; the Fourier coefficients of X_χ are those of X_f divided by ik·ω; with "
          "¦k¦_1^τ e^{-σs¦k¦_1/2} ≤ (2τ/(eσs))^τ this gives (26); the scalar series exists (a fast action component of "
          "X_f equals -ik_j f_k); f_{-k} = conj(f_k) gives the same relation for χ (reality)",
        S="A = γ^{-1} max{1, (2τ/(es))^τ}",
        deps=[("lpM:s1:dioph", "323", "(5): ¦ik·ω¦ ≥ γ¦k¦_1^{-τ} for k ≠ 0"),
              ("lpM:L9#norm", "325", "the coefficients are weighted as in (24) on the narrowed strip")]),
    "lpM:L10#lie-series-bound": dict(
        kind="display", title="(28): (1/j!)||ad_Y^j V||_{rho-eta} <= (2eDu/eta)^j ||V||_rho",
        stmt="L10:330-336", proof="L10:330-336", H=L10H + "; a holomorphic field Y of norm u on a larger domain; a collar η",
        Q=L10Q + "; for every j ≥ 1",
        C="repeated application of (25), dividing the collar η into j equal parts, gives (1/j!)‖ad_Y^j V‖_{ρ-η} ≤ "
          "(j^j/j!)(2Du/η)^j‖V‖_ρ ≤ (2eDu/η)^j‖V‖_ρ (28), using j! ≥ (j/e)^j; the Lie series converges when 2eDu/η < 1",
        S="none",
        deps=[("lpM:L9#commutator", "331", "(25) applied j times with loss η/j")]),
    "lpM:L10#lie-flow-identification": dict(
        kind="step", title="the Lie series represents the pullback by the flow; exact scalar identity",
        stmt="L10:315-321", proof="L10:336-338", H=L10H + "; 4eDu/σ ≤ 1/4", Q=L10Q,
        C="the Lie series of the pullback converges and equals the pullback by the actual flow (the flow solves the "
          "integral equation, its derivative the variational equation, and differentiating the pullback gives the "
          "commutator equation); the scalar series converges after its first bracket (a scalar bracket is bounded by "
          "D max(rs, b^2)‖X_F‖‖X_χ‖); trajectories from D_{ρ-σ} stay in D_{ρ-3σ/4}, and the Taylor remainders have "
          "geometric ratio ≤ 8eDu/σ ≤ 1/2, proving the exact scalar identity",
        S="none",
        deps=[("lpM:L10#lie-series-bound", "336-338", "(28) bounds the iterated brackets and the remainders"),
              ("lpM:L10#flow-existence", "336-338", "the actual flow exists and moves points by at most u")],
        note=N5),
    "lpM:L10#flow-existence": dict(
        kind="step", title="the flow exists for |t| <= 1: contraction on paths, holomorphy, inverse, reality, displacement, symplecticity",
        stmt="L10:315-321", proof="L10:340-340", H=L10H + "; u a sufficiently small multiple of the collar",
        Q=L10Q + "; both signs of time up to one",
        C="in a scaled ball about any starting point of the inner domain, Cauchy bounds DY by a dimension constant times "
          "u/η; the integral map on continuous paths stays in the ball and contracts, its iterates converge uniformly "
          "(holomorphic dependence, also for complex initial values); uniqueness gives the inverse, reality and lattice "
          "equivariance; displacement ≤ u and ‖Dφ - 1‖ ≤ e^{C_D u/η} - 1 ≤ 2C_D u/η; (DY)^T Ω + Ω DY = 0 gives "
          "symplecticity, for any constant nondegenerate Ω; c_D is decreased so that these estimates hold",
        S="C_D and c_D depend only on D",
        deps=[("lpM:L10#homological", "340", "the generator χ with ‖X_χ‖ ≤ u"),
              ("lpM:ext-cauchy-estimates", "340", "Cauchy's estimate for DY"),
              ("lpM:ext-picard", "340", "the integral map on continuous paths is a contraction (Picard iteration)"),
              ("lpM:ext-holomorphic-limit", "340", "uniform limits of the holomorphic iterates are holomorphic"),
              ("lpM:ext-gronwall", "340", "uniqueness of the flow gives the inverse, reality and equivariance")],
        note=N5),
    "lpM:L10#remainder": dict(
        kind="step", title="L_chi h_0 = -f^osc and the exact remainder (29); (27) with B_D = 16eD",
        stmt="L10:316-320", proof="L10:342-349", H=L10H + "; v = 4eDu/σ ≤ 1/4", Q=L10Q,
        C="with L_χF = {F, χ}, L_χ h_0 = -(f - ⟨f⟩); the exact remainder is f_+ = Σ_{j≥1} L_χ^j(g + f)/j! - Σ_{j≥1} "
          "L_χ^j f^osc/(j+1)! (29); each bracket is a vector-field commutator, so (28) with η = σ/2 bounds the two sums by "
          "v(1 - v)^{-1}(G + 2E) ≤ 4v(G + E), proving (27) with B_D = 16eD; the field X_{h_0} disappears through the "
          "homological identity",
        S="B_D = 16eD",
        deps=[("lpM:L10#homological", "342", "ω·∂_θχ = f - ⟨f⟩ gives L_χ h_0 = -f^osc"),
              ("lpM:L10#lie-series-bound", "347", "(28) with η = σ/2"),
              ("lpM:L10#lie-flow-identification", "349", "H∘φ equals the Lie series (exact scalar identity)")],
        note="AMENDED: N5 (AMENDMENTS.md L14): c_D is only implicit ('decreased to satisfy the flow estimates')"),
    # ---------------- Lemma 11
    "lpM:L11": dict(
        kind="lemma", title="Lemma 11: exponential normal form on the full slow set (30)-(31)", stmt="L11:353-363",
        proof="L11:365-379",
        H="the setting of Lemmas 9-10; H = h_0 + F with ‖X_F‖_3 ≤ ε; an integer N ≥ 1",
        Q="a number q_D > 0 depending only on D is fixed first; then for every such H, ε, N with A ε N^{τ+1} ≤ q_D (30)",
        C="there is a real holomorphic symplectic map Φ : D_2 → D_3 with H∘Φ = h_0 + Z + R, ∂_θZ = 0, ‖X_R‖_2 ≤ ε2^{-N}, "
          "‖X_Z‖_2 ≤ 2ε (31); its scaled displacement is at most 1/16; its inverse exists on D_{3/2}, takes values in "
          "D_2 and has the same displacement bound, so the two action-coordinate errors are at most r/16; this holds on "
          "the entire tube around Z, with no restriction on the slow dynamics",
        S="q_D depends only on D",
        deps=[("lpM:L11#qD-choice", "371-375", "q_D and the validity of each step under (30)"),
              ("lpM:L11#induction", "375", "the estimates E_j ≤ ε2^{-j}, ‖X_{g_j}‖ ≤ 2ε"),
              ("lpM:L11#composition", "375-379", "Φ, (31) and the displacement 1/32 < 1/16"),
              ("lpM:L11#inverse", "379", "the inverse on D_{3/2}")]),
    "lpM:L11#step-estimate": dict(
        kind="step", title="one Lie step with loss 1/N: u_j <= A N^tau eps 2^{-j}, E_{j+1} <= 3 B_D A eps N^{tau+1} E_j",
        stmt="L11:365-370", proof="L11:365-370", H=L11H + "; E_j ≤ ε2^{-j}, G_j ≤ 2ε at step j", Q=L11Q + "; every j < N",
        C="Lemma 10 with σ = 1/N on ρ_j gives u_j ≤ A N^τ ε 2^{-j} and E_{j+1} ≤ 3B_D A ε N^{τ+1} E_j",
        S="none",
        deps=[("lpM:L10", "365-370", "Lemma 10 with loss σ = 1/N on D_{ρ_j}")]),
    "lpM:L11#qD-choice": dict(
        kind="step", title="q_D = min(c_D, 1/(6 B_D), 1/64): (30) validates every step and halves E_j",
        stmt="L11:371-374", proof="L11:371-375", H=L11H, Q=L11Q,
        C="with q_D = min(c_D, 1/(6B_D), 1/64), condition (30) gives u_j/σ ≤ c_D (the step is valid) and E_{j+1} ≤ E_j/2",
        S="q_D depends only on D",
        deps=[("lpM:L11#step-estimate", "375", "the step estimates"),
              ("lpM:L10", "373", "the constants c_D and B_D of Lemma 10")]),
    "lpM:L11#induction": dict(
        kind="step", title="g_{j+1} = g_j + <f_j>: |X_g| <= 2 eps, angle independent; induction on j",
        stmt="L11:375-375", proof="L11:375-375", H=L11H, Q=L11Q + "; every j ≤ N",
        C="g_{j+1} = g_j + ⟨f_j⟩ has norm at most Σ_{l<j+1} E_l ≤ 2ε and stays angle independent; induction proves "
          "E_j ≤ ε2^{-j}, G_j ≤ 2ε for all j ≤ N",
        S="none",
        deps=[("lpM:L11#qD-choice", "375", "E_{j+1} ≤ E_j/2 under (30)"),
              ("lpM:L11#step-estimate", "375", "the estimates at each step")]),
    "lpM:L11#composition": dict(
        kind="step", title="Phi = phi_0 o ... o phi_{N-1}: (31) with Z = g_N, R = f_N; displacement <= 2 q_D/N <= 1/32",
        stmt="L11:358-363", proof="L11:375-379", H=L11H, Q=L11Q,
        C="composing the actual flow maps gives Φ = φ_0∘...∘φ_{N-1} and the exact identity (31) with Z = g_N, R = f_N; the "
          "telescoped displacement is Σ_{j<N} u_j ≤ 2AεN^τ ≤ 2q_D/N ≤ 1/32 < 1/16; each factor maps its smaller domain "
          "into its larger one, so Φ : D_2 → D_3 is defined, injective and symplectic",
        S="none",
        deps=[("lpM:L11#induction", "375", "the estimates of every step"),
              ("lpM:L10", "375", "each φ_j is a holomorphic real symplectic time-one map with displacement u_j")]),
    "lpM:L11#inverse": dict(
        kind="step", title="the inverse on D_{3/2} by negative-time flows in reverse order, values in D_2",
        stmt="L11:363-363", proof="L11:379-379", H=L11H, Q=L11Q,
        C="for an initial point in D_{3/2}, the negative-time flows in reverse composition order keep every intermediate "
          "point within scaled distance 1/32 of D_{3/2}, hence in D_2, inside every factor's domain; this constructs the "
          "inverse with the same telescoped bound, and the compositions are identities by uniqueness of each flow",
        S="none",
        deps=[("lpM:L11#composition", "379", "the telescoped displacement 1/32"),
              ("lpM:L10", "379", "the negative-time maps are inverses of the time-one maps")]),
}
DELETE = {"lpM:L11#derivative-bounds": "the Cauchy bounds on DΦ (L379) are proved but not consumed downstream (MAIN: "
          "'They are not used to infer invertibility'); its item is EXCLUDED"}
COV = {
    "lpM:L11#derivative-bounds": ("EXCLUDED", "outside every root closure of track LP: the loose bounds ‖DΦ - 1‖ ≤ D/8, "
                                  "‖DΦ^{-1} - 1‖ ≤ D/4 are stated in the proof only and no later proof uses them (L379: "
                                  "'They are not used to infer invertibility'; Lemma 12 uses only Φ, (31), the "
                                  "displacement and the inverse)"),
    "lpM:eq30": ("NODE lpM:L11", "display (30) is the smallness premise in Lemma 11's statement"),
    "lpM:eq31": ("NODE lpM:L11", "display (31) is Lemma 11's conclusion"),
}
