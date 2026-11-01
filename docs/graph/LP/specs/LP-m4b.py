# Track LP, slice LP-m4b, wave 2: MAIN L380-L464, Lemmas 12-13, the two alternative drift suppliers (N7).
# Both lemmas take the uniform chart-domain statement of Lemma 8 (m slow pairs) as a premise (SOURCE_HYPOTHESES); the
# applying node discharges it (Lemma 14's hypothesis, discharged by Theorem 15 / Theorem 19). Q5 (ruling root-b8):
# Lemma 12's source fields omit (35) (N4); its items are EXCLUDED. Lemma 13 consumes the track-N theorem
# KAM.Nekhoroshev.nonresonant through the IMPORTED node N:bpN:p11:nonresonant (packet LP-imports); no implementation
# file is read.

L12H = ("context of the proof of lpM:L12: the uniform chart-domain statement of Lemma 8 with m slow pairs (widths "
        "r_*, s, b, bound M); I^0 satisfying (5); 0 < μ ≤ μ_1 and the choices (32)")
L12Q = "for every I^0 and 0 < μ ≤ μ_1 (constants fixed first; inherited from lpM:L12)"
L13H = ("context of the proof of lpM:L13: the analytic data of Lemma 8 with m = n (planar) or m = 2n (spatial) slow "
        "pairs; I^0 satisfying (5); a fixed D_0 > 0; r = D_0√μ, K = ⌊κ_1 μ^{-a}⌋")
L13Q = "for every I^0 and small μ > 0 (constants fixed first; inherited from lpM:L13)"
N6 = ("AMENDED: N6 (AMENDMENTS.md L15): widths 2πs_1 < 4s with a convergence margin, w < 4b, D_0√μ < r_*, J the "
      "stopped interval of Lemma 14; stopped radius r = D_0√μ and improvement to r/2")
NR = ("N:bpN:p11:nonresonant")

NODES = {
    # ---------------- Lemma 12
    "lpM:L12": dict(
        kind="lemma", title="Lemma 12: planetary scaling, exponential time and the drift (34)", stmt="L12:383-399",
        proof="L12:405-427",
        H="the uniform chart-domain statement of Lemma 8 holds with m canonical slow pairs; I^0 satisfies (5)",
        Q="there are M_1, κ, μ_1, c > 0 (uniform in I^0); then for every 0 < μ ≤ μ_1, with r = √μ, a = 1/(2(τ+1)), "
          "N = ⌊κμ^{-a}⌋ ≥ 1, ε = M_1√μ, h_0 = h(I^0) + ω(I^0)·(I - I^0) (32), and every portion of an original solution",
        C="the normal form of Lemma 11 exists on the entire corresponding slow tube and H_μ∘Φ = h(J) + 𝒵(J, z) + "
          "R(J, θ, z), ∂_θ𝒵 = 0, ¦J̇¦_∞ ≤ rε2^{-N} along every transformed solution in D_2 (33); with T_μ = exp(cμ^{-a}), "
          "any portion of an original solution in D_1 of duration at most T_μ starting at action I^0 has ‖I(t) - I^0‖_∞ ≤ "
          "r/4 (34)",
        S="M_1, κ, μ_1, c are uniform in I^0 and depend only on the fixed chart data and (γ, τ)",
        deps=[("lpM:L12#perturbation-size", "405", "‖X_{H_μ - h_0}‖_3 ≤ M_1√μ"),
              ("lpM:L12#kappa-choice", "407-412", "κ, (36) implies (30), N and ε"),
              ("lpM:L12#time-choice", "414", "c and T_μ ≤ 2^{N/2}"),
              ("lpM:L12#normal-form", "414", "(33)"),
              ("lpM:L12#drift", "414-420", "(34)"),
              ("lpM:s1:dioph", "383", "I^0 satisfies (5)", "L12"),
              ("lpM:s1:fast", "388", "h and ω of (4) in h_0", "L12")],
        note="Q5 (ruling root-b8) and AMENDED: N4 (AMENDMENTS.md L13): (35) (L400-L403, proof L420-L425) is a remark, "
             "not a formal dependency, and is omitted from these source fields; Lemma 8's conclusion is a premise "
             "(discharged at the application); alternative supplier of the stopped drift (N7): route lpM:L14#route-L12"),
    "lpM:L12#perturbation-size": dict(
        kind="step", title="||X_{H_mu - h_0}||_3 <= M_1 sqrt(mu): h - h_0 of size r, mu f of size mu/r + mu/s + mu/b",
        stmt="L12:383-389", proof="L12:405-405", H=L12H, Q=L12Q,
        C="after decreasing the widths of Lemma 8 (D_4 closures with uniform first-derivative bounds) and restricting μ_1 "
          "so that 4r < r_* and r ≤ 1, the scaled field of h - h_0 has only angle components (ω(I) - ω(I^0))/s = O(r), "
          "the scaled components of X_{μf} are O(μ/r + μ/s + μ/b), both O(√μ); the supremum-to-Fourier estimate of Lemma 9 "
          "(losing the fixed strip between D_4 and D_3) gives ‖X_{H_μ - h_0}‖_3 ≤ M_1√μ",
        S="M_1 depends only on the fixed chart data",
        deps=[("lpM:L9#sup-to-fourier", "405", "the supremum-to-Fourier estimate from D_4 to D_3"),
              ("lpM:s1:fast", "405", "ω(I) - ω(I^0) is O(r) on the action tube"),
              ("lpM:s1:model", "405", "H_μ = h + μ f in the chart (the perturbation f)")]),
    "lpM:L12#kappa-choice": dict(
        kind="step", title="(36): A M_1 kappa^{tau+1} <= q_D/2 implies (30); N >= kappa mu^{-a}/2, eps <= 1/8",
        stmt="L12:407-412", proof="L12:407-412", H=L12H, Q=L12Q,
        C="choose κ > 0 with A M_1 κ^{τ+1} ≤ q_D/2 and 4L_ω κ^{τ+1} ≤ γ/2 (36), L_ω a complex Lipschitz bound of ω on the "
          "action neighborhood (∂_{I_i}ω_i = -3ν_i^3/I_i^4); since a(τ+1) = 1/2, (36) implies (30); decreasing μ_1 gives "
          "κμ^{-a} ≥ 2, N ≥ κμ^{-a}/2 and ε ≤ 1/8",
        S="κ depends only on M_1, A, q_D, L_ω and γ (hence on the chart data and (γ, τ))",
        deps=[("lpM:L12#perturbation-size", "408", "M_1"),
              ("lpM:L11", "412", "(30) and q_D"),
              ("lpM:L10", "408", "A of (26)"),
              ("lpM:s1:fast", "412", "ω and its Lipschitz bound L_ω")],
        note="the second restriction of (36) serves only (35), which Q5/N4 omit"),
    "lpM:L12#time-choice": dict(
        kind="step", title="c = (log 2) kappa/4, so T_mu = exp(c mu^{-a}) <= 2^{N/2}",
        stmt="L12:396-396", proof="L12:414-414", H=L12H, Q=L12Q,
        C="with c = (log 2)κ/4 and N ≥ κμ^{-a}/2, T_μ = exp(cμ^{-a}) ≤ 2^{N/2}", S="c depends only on κ",
        deps=[("lpM:L12#kappa-choice", "414", "N ≥ κμ^{-a}/2")]),
    "lpM:L12#normal-form": dict(
        kind="step", title="Lemma 11 with eps = M_1 sqrt(mu), N; Z := h_0 - h + Z gives (33) and |dJ/dt| <= r eps 2^{-N}",
        stmt="L12:390-395", proof="L12:414-414", H=L12H, Q=L12Q,
        C="Lemma 11 applies on the entire slow tube with ε, N of (32); 𝒵 := h_0 - h + Z is independent of θ, so (31) "
          "becomes (33), and ‖X_R‖_2 ≤ ε2^{-N} gives ¦J̇¦_∞ ≤ rε2^{-N} along every transformed solution in D_2",
        S="none",
        deps=[("lpM:L11", "414", "the normal form Φ and (31)"),
              ("lpM:L12#kappa-choice", "412", "(30) holds"),
              ("lpM:L12#perturbation-size", "405", "‖X_F‖_3 ≤ ε with F = H_μ - h_0")]),
    "lpM:L12#drift": dict(
        kind="step", title="(34): transformed solution in D_2, integrate (33), errors r/16 + r/16: ||I(t) - I^0|| <= r/4",
        stmt="L12:396-399", proof="L12:414-420", H=L12H + "; a portion of an original solution in D_1 of duration ≤ T_μ "
        "starting at I^0", Q=L12Q + "; both signs of t",
        C="the inverse of Lemma 11 maps the original solution to a transformed solution inside D_2, which solves the "
          "transformed Hamilton equations by symplecticity; integrating (33) with the forward error at t and the inverse "
          "error at 0 gives ‖I(t) - I^0‖_∞ ≤ r/16 + rε¦t¦2^{-N} + r/16 ≤ r/8 + rε2^{-N/2} ≤ r/4, for both signs of t",
        S="none",
        deps=[("lpM:L12#normal-form", "414", "(33) along transformed solutions"),
              ("lpM:L11", "414", "the inverse on D_{3/2} and the action errors ≤ r/16"),
              ("lpM:L12#time-choice", "418", "¦t¦ ≤ T_μ ≤ 2^{N/2}")]),
    # ---------------- Lemma 13
    "lpM:L13": dict(
        kind="lemma", title="Lemma 13: checked reuse of the repository's finite-cutoff engine (nonresonant)",
        stmt="L13:431-431", proof="L13:433-464",
        H="the analytic data of Lemma 8 with m = n (planar) or m = 2n (spatial) slow pairs; I^0 satisfies (5)",
        Q="for every fixed D_0 > 0 there are κ_1, c_1 > 0 and a smallness threshold for μ (uniform in I^0); then for every "
          "small μ > 0, with r = D_0√μ, K = ⌊κ_1μ^{-a}⌋, and every physical orbit starting at action I^0",
        C="the data can be fed to KAM.Nekhoroshev.nonresonant with the full center-dependent slow ball S = (21), radius "
          "r = D_0√μ, cutoff K ≍ μ^{-a} and a fixed slow collar; its stopped action estimate gives ‖I(t) - I^0‖_∞ ≤ r/2 "
          "for ¦t¦ ≤ exp(c_1μ^{-a}) provided the physical slow coordinates belong to S through the queried time (the "
          "same exponent a as Lemma 12)",
        S="κ_1, c_1 and the μ threshold depend only on the fixed chart data, (γ, τ) and D_0",
        deps=[("lpM:L13#interface", "433", "the slow set S of nonresonant is arbitrary: take the ball (21)"),
              ("lpM:L13#period-one", "435-440", "the period-one conversion"),
              ("lpM:L13#numeric-hypotheses", "442-457", "the numeric hypotheses (37)"),
              ("lpM:L13#structural-hypotheses", "458", "the structural hypotheses"),
              ("lpM:L13#conclusion", "460-464", "the drift ≤ r/2 through (38)"),
              ("lpM:s1:dioph", "431", "I^0 satisfies (5) (the nonresonance at I^0)", "L13")],
        note="Lemma 8's conclusion is a premise (discharged at the application); alternative supplier of the stopped "
             "drift (N7): route lpM:L14#route-L13, the Lean route. The repository citation (L433) is consumed only "
             "through the IMPORTED node N:bpN:p11:nonresonant. " + N6),
    "lpM:L13#interface": dict(
        kind="step", title="nonresonant's real slow set S is arbitrary: take S = the closed ball (21)",
        stmt="L13:431-431", proof="L13:433-433", H=L13H, Q=L13Q,
        C="the normal-form input of nonresonant leaves the real slow set S arbitrary; S is taken to be the closed ball "
          "(21), not a neighborhood of the starting secular point",
        S="none",
        deps=[(NR, "433", "the interface of the imported theorem (arbitrary slow set S)")]),
    "lpM:L13#period-one": dict(
        kind="step", title="theta = lambda/(2 pi), slow rescaling ell = w/r, H-hat = H/(2 pi); bracket 2 pi/ell^2; same equations and time",
        stmt="L13:435-440", proof="L13:435-440", H=L13H + "; local data θ = λ/(2π), ℓ = w/r, z̃ = z/ℓ",
        Q=L13Q,
        C="Ĥ(θ, I, z̃) = H(2πθ, I, ℓz̃)/(2π) with the weighted slow bracket coefficient c_s = 2π/ℓ^2 gives θ̇ = H_I/(2π), "
          "İ = -H_λ, dz̃/dt = J H_z/ℓ: exactly the original equations, in unchanged time; the unperturbed frequencies are "
          "ω/(2π); (ξ, η) = (x, -y) planar and (u, -v) for the spatial node pair give the repository's slow bracket",
        S="none",
        deps=[("lpM:s1:model", "440", "the symplectic form Σ dp ∧ dq and ι_{X_H}Ω = -dH of (1)"),
              ("lpM:s1:fast", "440", "the frequencies ω of (4)")]),
    "lpM:L13#numeric-hypotheses": dict(
        kind="step", title="(37): K L r <= alpha/2, eps <= alpha r/(256 K), 64 pi m s_1 r <= w^2, 2 pi K s_1 >= 6",
        stmt="L13:442-452", proof="L13:442-457", H=L13H + "; fixed period-one strip s_1 > 0 and slow width w > 0; p = q = 2",
        Q=L13Q,
        C="the scalar Fourier bound ε = M_2μ holds uniformly (the contour estimate of Lemma 9 applied to f/(2π)); with "
          "α = γK^{-τ}/(2π), K = ⌊κ_1μ^{-a}⌋, r = D_0√μ, the non-geometric numeric hypotheses of ExtNFHyp and "
          "nonresonant are KLr ≤ α/2, ε ≤ αr/(256K), 64πm s_1 r ≤ w^2, 2πKs_1 ≥ 6 (37); the first two follow from "
          "LD_0κ_1^{τ+1} ≤ γ/(4π) and M_2κ_1^{τ+1} ≤ γD_0/(512π), the last two by decreasing μ_0",
        S="κ_1 depends only on L, M_2, γ, τ and D_0",
        deps=[("lpM:L9#sup-to-fourier", "442", "the contour estimate of Lemma 9 applied to f/(2π) gives ε = M_2μ"),
              ("lpM:L13#period-one", "442", "the period-one Hamiltonian f/(2π) and frequencies ω/(2π)"),
              ("lpM:s1:dioph", "444", "(5) gives ¦k·ω(I^0)/(2π)¦ ≥ α for 0 < ¦k¦_1 ≤ K"),
              ("lpM:s1:fast", "442", "L bounds the complex frequency derivative of h/(2π)")],
        note=N6),
    "lpM:L13#structural-hypotheses": dict(
        kind="step", title="holomorphy, reality, periodicity, Fourier norm, widths, module {0}, tube inside (22), orbit-field equality",
        stmt="L13:458-458", proof="L13:458-458", H=L13H, Q=L13Q,
        C="holomorphy, reality, periodicity, the weighted Fourier norm, positivity of widths and perturbation bound, and "
          "the dimension hypotheses follow from Lemma 8's data and n ≥ 2, m ≥ 1; the nonresonance module is {0} "
          "(symmetric); the rescaled slow tube has physical width w (ℓr = w), not shrinking with μ; the finite action tube "
          "lies in (22) for small μ; the computed equations give the literal orbit-field equality; the initial fast "
          "action is the center",
        S="none",
        deps=[("lpM:L13#period-one", "458", "the computed equations in the new coordinates"),
              ("lpM:s1:data", "458", "n ≥ 2", "L13")]),
    "lpM:L13#conclusion": dict(
        kind="step", title="(38): drift <= r/2 through (s_1 r/(5 eps)) exp(2 pi K s_1/6) >= exp(c_1 mu^{-a}) under stopped slow membership",
        stmt="L13:460-463", proof="L13:460-464", H=L13H, Q=L13Q + "; every queried time t_1",
        C="nonresonant gives ‖I(t) - I^0‖_∞ ≤ r/2 through (s_1r/(5ε)) exp(2πKs_1/6) (38), provided the physical slow "
          "coordinates belong to S up to the queried time; since K ≥ κ_1μ^{-a}/2 for small μ, (38) exceeds "
          "exp(c_1μ^{-a}) for a fixed c_1 > 0; the stopped membership is discharged by Lemma 14",
        S="c_1 depends only on κ_1, s_1",
        deps=[(NR, "460", "the conclusion of nonresonant: drift ≤ r/2 through T_nr = (s_1r/(5ε))e^{κ/6}"),
              ("lpM:L13#numeric-hypotheses", "460", "(37) supplies its numeric hypotheses"),
              ("lpM:L13#structural-hypotheses", "460", "its structural hypotheses"),
              ("lpM:L13#interface", "460", "S is the ball (21)")],
        note="the closing sentences on nnf_disp_radius (slow displacement ≤ w/2^{10}) and on the independent paper "
             "proof are a check, not a premise of the drift conclusion; no edge"),
}
DELETE = {NR: "imported node, rendered in the writer-owned packet LP-imports (SPEC §3)",
          "lpM:L12#finite-divisors": "(35): Q5/N4, excluded (no consumer)"}
COV = {
    "lpM:eq34": ("NODE lpM:L12#drift", "display (34), the stopped drift r/4"),
    "lpM:eq35": ("EXCLUDED", "Q5 (ruling root-b8) and amendment N4: (35) is a remark, not a formal dependency (the "
                 "paper route inverts only k·ω(I^0)); omitted from Lemma 12's source fields"),
    "lpM:L12#finite-divisors": ("EXCLUDED", "Q5 (ruling root-b8) and amendment N4: the proof of (35) (L420-L425) "
                                "serves only the remark (35), which has no consumer"),
    "lpM:L12#drift": ("NODE lpM:L12#normal-form, lpM:L12#drift", "L414-L420: the rewrite (33) and the drift (34)"),
}
