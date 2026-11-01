# Track LP, slice LP-imports (writer-owned): IMPORTED nodes from other tracks' graphs (SPEC §3). KIND external,
# LEAN_STATUS EXTERNAL, PROOF_SOURCE -, DEPS -, source fields copied verbatim from docs/graph/N/DEPGRAPH.md.
# Wave 2: Lemma 13 consumes KAM.Nekhoroshev.nonresonant (graph N node bpN:p11:nonresonant). The candidates
# N:bpN:p11:s-nf#data (its hypotheses are restated in the nonresonant record) and the P imports are not used by any
# extracted proof and are not rendered; N:bpN:p0:partial (partialConvex_nekhoroshev) serves LP3 (wave 4).

NODES = {
    "N:bpN:p11:nonresonant": dict(
        kind="external", title="[N] Nonresonant stability in the extended phase space (KAM.Nekhoroshev.nonresonant)",
        stmt="blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L65-L68", proof="-",
        H="r,s,K_a,alpha>0, L>=0, p>1, q=p/(p-1), kappa=2 pi K_a s>=6; r=r_B; h holomorphic on V_r(I_c), real on real "
          "points; ¦k.omega(I_c)¦>=alpha for 0<¦k¦_1<=K_a (cond-nr, Lambda={0}), cond-L with L, K_a L r<=alpha/p; (SL); "
          "f in O(r,s)^{e,R}, ¦f¦<=eps with eps>0, eps<=alpha r/(2^7 q K_a); H=h+f; T_nr=(s r/(5 eps))e^{kappa/6}",
        Q="r,s,K_a,alpha,L,p; h; f; eps; F; J; y; t_1",
        C="for every F with F=X^c_{H^R} on W^e_r, J containing 0, y with y'=F(y) on J, y(0)=(theta_0,I_c,x-tilde_0), "
          "x-tilde_0 in S-tilde, and t_1 in J with ¦t_1¦<=T_nr and x-tilde(u) in S-tilde between 0 and t_1: "
          "¦I(u)-I_c¦<=r/2 between 0 and t_1",
        S="none",
        note="IMPORTED: proved in the track-N graph, node bpN:p11:nonresonant (there KIND proposition, contract "
             "bpN:p11:nonresonant v1); Lean theorem KAM.Nekhoroshev.nonresonant cited by MAIN L433 (never read here)"),
    "N:bpN:p0:partial": dict(
        kind="external", title="[N] N-PARTIAL-CONVEX: partialConvex_nekhoroshev (sealed, root of graph N)",
        stmt="blueprint-N/parts/p0-conventions.tex#bpN:p0:partial@L319-L335", proof="-",
        H="a Lean frozen statement; n ≥ 2, k ≥ 1, G, G' ⊂ ℝⁿ open and convex, D ⊂ Ph_k open, ρ, g, m, M_ℂ ∈ ℝ with ρ > 0, "
          "M_ℂ > 0, B̄(I,ρ) ⊂ G' for every I ∈ G (closed max-norm ball); h : ℂⁿ → ℂ complex differentiable and complex C² "
          "on G'_ρ, Im h(I) = 0 for real I ∈ G'_ρ, ‖D²h(z)‖ ≤ M_ℂ on G'_ρ, HasDefiniteFastPart G' ρ g m h; then for "
          "μ ∈ (0,μ₀), P with IsPartialPerturbation G' D ρ P, C > 0, z : ℝ → Ph_{n+k}: (Z1) IsSolutionOn H_μ {𝖨 : "
          "fast(𝖨) ∈ G} [0,C] z with H_μ = Re h(fast 𝖨) + μ Re P(cx(φ,𝖨)) (degenerateHamiltonian (realPart h) (Re P ∘ "
          "cx) μ); (Z2) fast(z(0)_2) ∈ core(G, μ^{b_n}); t ∈ [0, min(C, μ^{−1} exp(μ^{−a_n}))] with (slow z(u)_1, "
          "slow z(u)_2) ∈ core(D, μ^{b_n}) for all u ∈ [0,t]",
        Q="n, k; G, G', D, ρ, g, m, M_ℂ, h (with their hypotheses); then ∃ μ₀ > 0; then ∀ μ ∈ (0,μ₀), P, C > 0, z (with "
          "Z1, Z2); then ∀ t ∈ [0, min(C, μ^{−1} exp(μ^{−a_n}))] with slow confinement on [0,t]",
        C="¦fast(z(t)_2) − fast(z(0)_2)¦ ≤ ½ μ^{b_n}",
        S="μ₀ > 0 depends only on (n, k, G, G', D, ρ, g, m, M_ℂ, h) and is chosen before μ, P, C, z, t; a_n = 2/(6n² − 3n "
          "+ 14), b_n = 3/(6n² − 3n + 14); slow confinement is tested only on [0,t]; the initial erosion core(G, "
          "μ^{b_n}) is used only as fast(z(0)_2) ∈ G",
        note="IMPORTED: proved in the track-N graph, node bpN:p0:partial (there KIND theorem, the frozen root "
             "nekhoroshev.d25.partialConvex_nekhoroshev v1, sealed, D58); consumed by LP3 (wave 4)"),
}
NEWCOV = [
    ("N:bpN:p11:nonresonant", "citation", "blueprint-N/parts/p11c-partial-stability.tex#bpN:p11:nonresonant@L65-L68",
     "NODE N:bpN:p11:nonresonant", "imported node consumed by Lemma 13 (MAIN L433, L460); the MAIN citation item "
     "lpM:L13#cite-repository maps to it as well"),
]
