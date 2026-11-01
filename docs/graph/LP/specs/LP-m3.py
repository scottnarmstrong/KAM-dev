# Track LP, slice LP-m3, wave 2: MAIN L190-L271, Lemmas 7-8 (the planar chart and its whole-sublevel complex domain).
# Both lemmas are planar (d = 2): Lemma 7 is the one-planet chart, Lemma 8 the product chart on the whole secular
# ball (21). The spatial chain (wave 3, Lemmas 17-18) reuses Lemma 7 and the L8 pattern. Externals of the closed list
# (SPEC §3) first consumed here are rendered in the writer-owned packet LP-ext-w2.

L7H = ("context of the proof of lpM:L7: ν > 0; the region I > 0, λ ∈ 𝕋, (x, y) ∈ ℝ^2, Γ = (x^2 + y^2)/2 < I; local data "
       "a = (I/ν)^2, s = 1 - Γ/I > 0, b_e = √((1 - Γ/(2I))/I), k = b_e x, l = -b_e y")
L7Q = "for every ν > 0 and every point of the region (inherited from lpM:L7)"
L8H = ("context of the proof of lpM:L8: the data (n, ν, 𝒜, δ) (lpM:s1:data), planar; 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, "
       "𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}, Z_0 = {z : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (21)")
L8Q = "for every I^0 ∈ 𝓛_δ (inherited from lpM:L8; the widths are fixed before I^0)"
def B(line):
    return ("lpM:s1:thresholds#orderedStrongThreshold", line, "B occurs")

NODES = {
    # ---------------- Lemma 7
    "lpM:L7": dict(
        kind="lemma", title="Lemma 7: a regular planar canonical chart", stmt="L7:195-200", proof="L7:202-242",
        H="ν > 0 (one planet, d = 2)",
        Q="for every ν > 0",
        C="the map (19), with angle read modulo 2π, is a real analytic symplectic diffeomorphism from {I > 0, λ ∈ 𝕋, "
          "(x, y) ∈ ℝ^2, Γ = (x^2 + y^2)/2 < I} onto the positive-angular-momentum negative-energy planar region; its "
          "form is dI ∧ dλ + dx ∧ dy, its energy is -ν^3/(2I^2), its angular momentum is G = I - Γ; it is regular at "
          "circular orbits",
        S="none",
        deps=[("lpM:L7#kepler-equation", "207-211", "the eccentric longitude F of (18) and its analytic dependence"),
              ("lpM:L7#chart-formula", "213-220", "the chart (19)"),
              ("lpM:L7#rotated-form", "221-226", "the energy, angular momentum and eccentricity vector of the image"),
              ("lpM:L7#symplectic", "228-238", "the chart is symplectic"),
              ("lpM:L7#inverse", "240-242", "the analytic inverse onto the region: a diffeomorphism modulo the angle "
               "lattice"),
              ("lpM:s1:elements", "200", "energy, angular momentum and the negative-energy region are those of (2)",
               "L7")]),
    "lpM:L7#kepler-equation": dict(
        kind="step", title="(18): unique eccentric longitude F, analytic in the data, F(lambda + 2 pi) = F(lambda) + 2 pi",
        stmt="L7:202-210", proof="L7:207-211", H=L7H, Q=L7Q,
        C="k^2 + l^2 = 1 - s^2 < 1; F - k sin F + l cos F = λ (18) has a unique solution F modulo 2π, since D_F = 1 - k cos F "
          "- l sin F ≥ 1 - √(k^2 + l^2) > 0 and the lift increases by 2π per period; the solution is analytic in "
          "(I, λ, x, y): the Newton-type fixed-point map is a contraction on small complex disks, its holomorphic "
          "iterates converge uniformly; uniqueness patches the branches and gives F(λ + 2π) = F(λ) + 2π",
        S="none",
        deps=[("lpM:ext-holomorphic-limit", "211", "uniform limits of the holomorphic iterates are holomorphic")],
        note="the convergence of the iterates of a contraction is elementary (geometric series); only the holomorphy "
             "of the limit is an external input"),
    "lpM:L7#chart-formula": dict(
        kind="display", title="(19): the chart q = a(A c(F) - (k,l)), p = nu A c'(F)/(sqrt(a) D_F)",
        stmt="L7:213-220", proof="L7:213-220", H=L7H, Q=L7Q,
        C="with A = [[1 - l^2/(1+s), kl/(1+s)], [kl/(1+s), 1 - k^2/(1+s)]], c(F) = (cos F, sin F), c'(F) = (-sin F, cos F): "
          "q = a(A c(F) - (k,l)), p = (ν/√a) A c'(F)/D_F (19); no perihelion angle is used at zero eccentricity",
        S="none",
        deps=[("lpM:L7#kepler-equation", "219", "F solves (18) and D_F > 0")]),
    "lpM:L7#rotated-form": dict(
        kind="step", title="(20) for e > 0; energy -nu^3/(2I^2), angular momentum G = I - Gamma, eccentricity vector (k,l); e = 0 by continuity",
        stmt="L7:221-226", proof="L7:221-226", H=L7H, Q=L7Q,
        C="for e = √(k^2 + l^2) > 0, (k, l) = e(cos ϖ, sin ϖ), F = E + ϖ, (19) is the rotation of (20) q = a(cos E - e, "
          "s sin E), p = ν(-sin E, s cos E)/(√a(1 - e cos E)); multiplication gives energy -ν^3/(2I^2), angular "
          "momentum G = I - Γ and eccentricity vector (k, l); the identities extend to e = 0 by continuity",
        S="none",
        deps=[("lpM:L7#chart-formula", "221-224", "(20) is (19) in rotated coordinates"),
              ("lpM:s1:elements", "226", "energy, angular momentum and eccentricity vector are those of (2)")]),
    "lpM:L7#symplectic": dict(
        kind="step", title="p.dq = I dlambda + Gamma d(-varpi) + d(2Ie sin E): the chart is symplectic",
        stmt="L7:228-238", proof="L7:228-238", H=L7H, Q=L7Q,
        C="in the coordinates (20), p·dq = 2e sin E dI + I(1 + e cos E) dE + I sin E de; a varying perihelion rotation "
          "adds G dϖ; with ℓ = E - e sin E, p·dq = I dλ + Γ d(-ϖ) + d(2Ie sin E), and (x, y) = √(2Γ)(cos ϖ, -sin ϖ) gives "
          "Γ d(-ϖ) = (x dy - y dx)/2; exterior differentiation proves symplecticity on e > 0, and analyticity extends it "
          "across e = 0",
        S="none",
        deps=[("lpM:L7#rotated-form", "229-232", "the computation is done in the rotated coordinates (20)"),
              ("lpM:L7#kepler-equation", "232-235", "λ = ℓ + ϖ through (18) with F = E + ϖ"),
              ("lpM:ext-identity-theorem", "238", "the analytic identity of the two forms extends from e > 0 across e = 0")],
        note="AMENDED: N1 (AMENDMENTS.md L10), fixed in place at MAIN L238: Γ d(-ϖ) = (x dy - y dx)/2"),
    "lpM:L7#inverse": dict(
        kind="step", title="analytic inverse: a, I, G from energy and momentum, (k,l) from the eccentricity vector, lambda from (18)",
        stmt="L7:240-242", proof="L7:240-242", H=L7H, Q=L7Q,
        C="on the positive-angular-momentum negative-energy region: a, I, G from energy and angular momentum; (k, l) as "
          "the eccentricity vector, x = k/b_e, y = -l/b_e; A has eigenvalues 1, s > 0 and A^{-1}(q/a + (k,l)) = c(F) "
          "(length one by e·q = a(1 - e^2) - ¦q¦); λ from (18) modulo 2π via e^{iλ} = e^{iF} exp[-i(k sin F - l cos F)]; "
          "the momentum is recovered uniquely from the positive angular momentum and e = v × (q × v) - q/¦q¦; all "
          "inverse formulas are analytic, so the chart is a diffeomorphism onto the region modulo the angle lattice",
        S="none",
        deps=[("lpM:L2", "240", "(11): ¦q × p¦ = I √(1 - e^2), so s = G/I = √(1 - e^2) and k^2 + l^2 = 1 - s^2 recover "
               "the eccentricity data"),
              ("lpM:L7#rotated-form", "240", "the image has energy -ν^3/(2I^2), angular momentum I - Γ and "
               "eccentricity vector (k, l), which the inverse inverts"),
              ("lpM:L7#kepler-equation", "240-241", "λ is recovered from F through (18)"),
              ("lpM:s1:elements", "242", "the eccentricity vector of (2)")]),
    # ---------------- Lemma 8
    "lpM:L8": dict(
        kind="lemma", title="Lemma 8: a whole-sublevel planar analytic neighborhood (21)-(22)", stmt="L8:246-255",
        proof="L8:257-271",
        H="the data (n, ν, 𝒜, δ) of lpM:s1:data, planar (d = 2); 𝓛 = {(ν_i √a_i)_i : a ∈ 𝒜}, 𝓛_δ = {I^0 ∈ 𝓛 : B(I^0) ≥ δ}",
        Q="there exist r_*, s, b, M > 0 (fixed first); then for every I^0 ∈ 𝓛_δ, with Z_0 = {z = (x_i, y_i)_i : ¦z¦_2^2/2 ≤ "
          "B(I^0) - δ/4} (21)",
        C="the product chart of Lemma 7 and the exact pulled-back perturbation f are holomorphic on ‖I - I^0‖_∞ < r_*, "
          "¦Im λ¦_∞ < 4s, dist_∞(z, Z_0) < 4b (22); on a slightly smaller domain the chart, momenta, f and all their "
          "first derivatives are bounded by M; every Newtonian denominator there has a single holomorphic branch with "
          "modulus bounded away from zero; in physical coordinates the chart Hamiltonian equals h(I) + μ f(I, λ, z) "
          "without truncation; the ball (21) contains every secular state allowed by the initial margin, with a fixed "
          "collar",
        S="r_*, s, b, M depend only on (n, ν, 𝒜, δ) and are chosen before I^0 (and before μ)",
        deps=[("lpM:L8#empty-case", "257", "the empty case"),
              ("lpM:L8#shared-tube", "257", "U and r_g"),
              ("lpM:L8#real-margin", "258-261", "the real margin, safety and e_*"),
              ("lpM:L8#compact-real-set", "261", "the compact real set and analyticity of the chart near it"),
              ("lpM:L8#newton-extension", "263", "the uniform complex extension of the Kepler-equation solution"),
              ("lpM:L8#gluing", "265", "single-valued uniform complex neighborhood"),
              ("lpM:L8#denominators", "267-271", "the Newtonian denominators"),
              ("lpM:L8#widths", "271", "the widths r_*, s, b and the bound M"),
              ("lpM:L8#exact-split", "271", "the exact split h + μ f"),
              ("lpM:L7", "255", "the product chart of Lemma 7 gives ΣΓ_i = Σ(I_i - G_i) = C on prograde states, so the "
               "ball (21) contains every secular state with C ≤ B(I^0) - δ, with collar 3δ/4", "L8"),
              ("lpM:s1:model", "250", "the perturbation f of (1)", "L8"),
              ("lpM:s1:chamber#chamber", "246", "𝓛_δ lies in the chamber Q (𝒜 is ordered)", "L8"),
              ("lpM:s1:thresholds#orderedStrongThreshold", "246", "B occurs in 𝓛_δ and in (21)", "L8")],
        note="planar (d = 2) lemma; the spatial analogue is Lemma 18 (wave 3). Lemmas 12-14 take its conclusion (with "
             "m = n slow pairs here) as a premise; Theorem 15 discharges it (lpM:T15#apply-L14). AMENDED: N2, N3 "
             "(AMENDMENTS.md L11, L12)."),
    "lpM:L8#empty-case": dict(
        kind="step", title="L_delta empty: no initial state satisfies (6); otherwise L_delta is compact",
        stmt="L8:246-246", proof="L8:257-257", H=L8H, Q="for the fixed data",
        C="if 𝓛_δ is empty there is no initial state satisfying (6) (C(0) ≥ 0 and C(0) ≤ B(I^0) - δ force B(I^0) ≥ δ); "
          "otherwise 𝓛_δ is compact (a closed subset of the compact 𝓛, B being continuous)",
        S="none",
        deps=[("lpM:L3#static", "257", "C ≥ 0, so an initial state with (6) has B(I^0) ≥ δ"),
              ("lpM:L4", "257", "B is continuous, so 𝓛_δ is closed in the compact 𝓛"),
              B("257")]),
    "lpM:L8#shared-tube": dict(
        kind="step", title="compact chamber neighborhood U and width r_g: 4r_g tube in U, Omega_B(4 r_g) <= delta/16",
        stmt="L8:257-257", proof="L8:257-257", H=L8H + "; 𝓛_δ ≠ ∅", Q="for the fixed data",
        C="there are a compact chamber neighborhood U of 𝓛_δ and a fixed real action width r_g > 0 such that every "
          "4r_g-tube about 𝓛_δ (sup norm) lies in U and Ω_B(4r_g) ≤ δ/16",
        S="U and r_g depend only on (n, ν, 𝒜, δ)",
        deps=[("lpM:L6#shared-U", "257", "the compact neighborhood U of the compact 𝓛_δ and the modulus Ω_B(r) → 0"),
              ("lpM:L8#empty-case", "257", "𝓛_δ is compact"),
              ("lpM:s1:chamber#chamber", "257", "U lies in the chamber Q"), B("257")],
        note="AMENDED: N2 (AMENDMENTS.md L11): this U is the one compact set shared with Lemmas 6 and 14; it contains "
             "the closed 4r_g-tube about 𝓛_δ"),
    "lpM:L8#real-margin": dict(
        kind="step", title="real tube: sum Gamma_i <= B(I) - 3 delta/16, Gamma_i < I_i, phases safe by Lemma 5, e <= e_* < 1",
        stmt="L8:257-261", proof="L8:257-261", H=L8H + "; 𝓛_δ ≠ ∅; real I with ‖I - I^0‖_∞ ≤ 4r_g and z ∈ Z_0",
        Q=L8Q + "; for every such real (I, z) and λ",
        C="Σ_i Γ_i ≤ B(I^0) - δ/4 ≤ B(I) - 3δ/16; consequently Γ_i < I_i with a fixed margin, the corresponding planar "
          "phases are safe (a compact nonsingular set of Lemma 5) and the eccentricities are bounded by one fixed "
          "e_* < 1",
        S="the margin and e_* depend only on (n, ν, 𝒜, δ)",
        deps=[("lpM:L8#shared-tube", "258-259", "Ω_B(4r_g) ≤ δ/16 gives B(I^0) - δ/4 ≤ B(I) - 3δ/16"),
              ("lpM:L7", "261", "G_i = I_i - Γ_i, so these points are prograde states with C = ΣΓ_i"),
              ("lpM:L5", "261", "Lemma 5 with U and m = 3δ/16: the phases form a compact nonsingular set (its premise "
               "C ≤ B(I) - 3δ/16 is the display)"),
              ("lpM:L5#perihelion", "261", "√(1 - e_i^2) ≥ m/I_max bounds the eccentricities by e_* < 1"), B("259")]),
    "lpM:L8#compact-real-set": dict(
        kind="step", title="the set of (I^0, I, z, lambda) with one closed angle cell is compact; the chart is analytic near it",
        stmt="L8:261-261", proof="L8:261-261", H=L8H + "; 𝓛_δ ≠ ∅", Q="for the fixed data",
        C="the set of (I^0, I, z, λ) with I^0 ∈ 𝓛_δ, real ‖I - I^0‖_∞ ≤ 4r_g, z ∈ Z_0 and λ in one closed period cell is "
          "compact, and the chart of Lemma 7 is analytic on an open neighborhood of it; every point of (22) lies within "
          "sup distance max(r_*, 4s, 4b) of the compact projection K' of this set",
        S="none",
        deps=[("lpM:L8#real-margin", "261", "the points lie in the chart's region with a fixed margin"),
              ("lpM:L8#shared-tube", "261", "the tube is closed and bounded inside U"),
              ("lpM:L7", "261", "the chart is real analytic on its region")],
        note="AMENDED: N3 (AMENDMENTS.md L12): the projection K' over I^0 ∈ 𝓛_δ of this closed set, with r_* ≤ 4r_g"),
    "lpM:L8#newton-extension": dict(
        kind="step", title="uniform complex extension of the solution of (18): radii rho, eta, contraction by 1/2",
        stmt="L8:263-263", proof="L8:263-263", H=L8H + "; 𝓛_δ ≠ ∅", Q="at every point of the compact real set",
        C="at each real point the derivative of (18) is at least 1 - e_*; fixed radii ρ, η > 0 make the Newton "
          "fixed-point map preserve the ρ-disk and contract by 1/2, so its holomorphic iterates converge uniformly to a "
          "bounded holomorphic local branch; the positive radicands and 1 + s in (19) stay a fixed distance from zero; "
          "complexified real squares are bilinear (w·w), never Hermitian",
        S="ρ and η are fixed (depend only on (n, ν, 𝒜, δ))",
        deps=[("lpM:L8#real-margin", "263", "the derivative bound 1 - e_*"),
              ("lpM:L7#kepler-equation", "263", "the fixed-point map of (18)"),
              ("lpM:L8#compact-real-set", "263", "uniformity over the compact real set"),
              ("lpM:ext-holomorphic-limit", "263", "the uniform limit of the holomorphic iterates is holomorphic")]),
    "lpM:L8#gluing": dict(
        kind="step", title="glue local extensions on complex balls (identity theorem, finite subcover): single-valued on the angle torus",
        stmt="L8:265-265", proof="L8:265-265", H=L8H + "; 𝓛_δ ≠ ∅", Q="for the fixed data",
        C="local extensions on complex balls centered at real points agree on intersections (convex, with a nonempty "
          "real part where both equal the real analytic map; power series and the identity theorem); translates of the "
          "angle cell patch the same way; a finite subcover of the compact real set with half-sized balls leaves a "
          "uniform complex neighborhood; the periodic chart and disturbing function are single-valued on the angle torus, "
          "independently of I^0 and μ",
        S="the complex neighborhood is fixed (independent of I^0 and μ)",
        deps=[("lpM:L8#newton-extension", "265", "the local holomorphic extensions"),
              ("lpM:L8#compact-real-set", "265", "the compact real set covered by finitely many balls"),
              ("lpM:ext-identity-theorem", "265", "equality on the connected intersection"),
              ("lpM:ext-compact-cover", "265", "a finite subcover of the compact real set")]),
    "lpM:L8#denominators": dict(
        kind="step", title="Re(w.w) >= d^2/2 for every star and pair denominator; holomorphic square root, reciprocal <= sqrt 2/d",
        stmt="L8:255-255", proof="L8:267-271", H=L8H + "; 𝓛_δ ≠ ∅; local data: d a common real lower bound of ¦q_i¦ and "
        "¦q_i - q_j¦, Q a real upper bound", Q="for every complex w within η_q of a real w_0",
        C="¦w·w - ¦w_0¦^2¦ ≤ 2Qη_q + η_q^2 ≤ d^2/2 after reducing the neighborhood, so Re(w·w) ≥ d^2/2; the square root "
          "with positive real part and its reciprocal are holomorphic, the reciprocal bounded by √2/d; this applies to "
          "every star and pair denominator",
        S="d, Q and η_q depend only on (n, ν, 𝒜, δ)",
        deps=[("lpM:L5#pair-distances", "267", "the safe real phases have ¦q_i¦ ≥ d_⋆ and ¦q_i - q_j¦ ≥ d_pair: a "
               "common real lower bound d"),
              ("lpM:L8#real-margin", "267", "the real phases are those of Lemma 5's compact set (bounded lengths Q)"),
              ("lpM:L8#gluing", "271", "the neighborhood being reduced"),
              ("lpM:ext-cauchy-estimates", "271", "the holomorphic square root with positive real part")]),
    "lpM:L8#widths": dict(
        kind="step", title="Cauchy bounds on a smaller compact complex neighborhood; choice of r_*, s, b (r_* <= 4 r_g) and M",
        stmt="L8:246-255", proof="L8:271-271", H=L8H + "; 𝓛_δ ≠ ∅", Q="for the fixed data",
        C="the chart and its derivatives are bounded on a smaller compact complex neighborhood (displayed formulas and "
          "Cauchy's one-variable estimates); f and its first derivatives have a uniform bound M; r_*, s, b are chosen so "
          "that (22) and a small enlargement lie inside this neighborhood",
        S="r_*, s, b, M depend only on (n, ν, 𝒜, δ)",
        deps=[("lpM:L8#gluing", "271", "the uniform complex neighborhood"),
              ("lpM:L8#denominators", "271", "f's denominators are holomorphic and bounded away from zero"),
              ("lpM:ext-cauchy-estimates", "271", "Cauchy's one-variable estimates for the derivatives"),
              ("lpM:L8#shared-tube", "12", "N3: r_* ≤ 4r_g, so (22) lies within the 4r_g-tube data", "A:N3")],
        note="AMENDED: N3 (AMENDMENTS.md L12): r_* ≤ 4r_g is stated explicitly"),
    "lpM:L8#exact-split": dict(
        kind="step", title="the product chart gives (4): chart Hamiltonian h(I) + mu f, no truncation",
        stmt="L8:255-255", proof="L8:271-271", H=L8H, Q="for every μ > 0 and every point of (22)",
        C="the product of the Lemma 7 charts turns the Kepler part of (1) into h(I) = -Σ_i ν_i^3/(2I_i^2) of (4), so the "
          "chart Hamiltonian is exactly h(I) + μ f(I, λ, z)",
        S="none",
        deps=[("lpM:L7", "271", "each planet's Kepler term has energy -ν_i^3/(2I_i^2) in the chart"),
              ("lpM:s1:fast", "271", "h of (4)"),
              ("lpM:s1:model", "271", "the splitting (1) H_μ = Σ Kepler terms + μ f")]),
}
COV = {
    "lpM:eq21": ("NODE lpM:L8", "display (21), the whole secular ball Z_0, is part of Lemma 8's statement"),
    "lpM:eq22": ("NODE lpM:L8", "display (22), the complex domain, is part of Lemma 8's statement"),
}
