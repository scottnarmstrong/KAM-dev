# Track LP, packet LP-adef-pl-w2: the 7 reused frozen definitions that the LP1/LP1-H statements import directly (Q6),
# bound as LP anchor nodes. DEPS are the bound frozen definitions each declaration uses (read from the frozen file);
# movingHamiltonian and KAM.Iso.IsHamiltonianSolutionOn (used by IsMovingSolutionOn) are typing data in wave 2
# (SPEC §1.3); the latter becomes an LP anchor in wave 3 (packet LP-adef-sp), where the edge is added.

T = "typing data"


def d(stmt, title, H, Q, C, deps=(), note="-"):
    line = stmt.split(":")[-1].split("-")[0]
    unit = stmt.split(":")[-2]
    return dict(kind="definition", title=title, stmt=stmt, proof="-", H=H, Q=Q, C=C, S="none",
                deps=[(t, line, why, unit) for t, why in deps], note=note)


PH = ("lpM:s1:model#Phase", "the phase type")
BV = ("lpM:s1:model#bodyVector", "planet i's coordinate vector")
R = "reused frozen definition {} ({}), bound as an LP anchor node (Q6)"

NODES = {
    "lpM:s1:dioph#IsDiophantine": d("s1:64-65", "(gamma, tau)-Diophantine vector: gamma/|k|_1^tau <= |k.omega| for k != 0",
        "n : ℕ; γ, τ : ℝ; ω : Fin n → ℝ (" + T + ")", "for every n, γ, τ, ω",
        "γ/¦k¦_1^τ ≤ ¦k·ω¦ for every 0 ≠ k ∈ ℤ^n: the condition (5) at ω = ω(I^0)",
        note=R.format("kam.IsDiophantine.v1", "core")),
    "lpM:s1:model#actualMasses": d("s1:17-17", "actual masses (m_0, mu m_1, ..., mu m_n)",
        "n : ℕ; m_0 : ℝ; m : Fin n → ℝ; μ : ℝ (" + T + ")", "for every n, m_0, m, μ",
        "the mass vector (m_0, μm_1, ..., μm_n); with m_0 = 1 and m = ν: star mass one and planet masses μν_i (MAIN L17, "
        "L99)", note=R.format("planetary.actualMasses.v1", "track P")),
    "lpM:L1#barycentricPositions": d("L1:104-104", "barycentric positions x_0 = -mu sum nu_i q_i/M, x_i = x_0 + q_i",
        "n : ℕ; m_0 : ℝ; m : Fin n → ℝ; μ : ℝ; q (" + T + ")", "for every n, m_0, m, μ, q",
        "x_0 = -μ Σ_i m_i q_i/(m_0 + μΣ_i m_i), x_i = x_0 + q_i (Lemma 1's explicit inverse, L104, with m_0 = 1, m = ν)",
        [BV], note=R.format("planetary.barycentricPositions.v1", "track P")),
    "lpM:L1#barycentricVelocities": d("L1:104-104", "barycentric velocities x_0' = -mu sum p_i/m_0, x_i' = p_i/m_i",
        "n : ℕ; m_0 : ℝ; m : Fin n → ℝ; μ : ℝ; p (" + T + ")", "for every n, m_0, m, μ, p",
        "ẋ_0 = -(μ/m_0) Σ_i p_i, ẋ_i = p_i/m_i (Lemma 1's explicit inverse, L104, with m_0 = 1, m = ν)",
        [BV], note=R.format("planetary.barycentricVelocities.v1", "track P")),
    "lpM:s1:model#IsMovingSolutionOn": d("s1:17-24", "z solves the moving-Sun Hamiltonian (1) on J without collision",
        "n : ℕ; m : Fin n → ℝ; μ : ℝ; J : Set ℝ; z : ℝ → Phase (n*2) (" + T + ")", "for every n, m, μ, J, z",
        "z is a solution on J of Hamilton's equations of (1) (frozen movingHamiltonian with star mass and G one; the "
        "differentiability-guarded ODE predicate) and every z(t), t ∈ J, is collision-free (the open domain of (1))",
        [PH, ("lpM:s1:model#NoCollision", "the configurations stay collision-free")],
        note=R.format("planetary.d25.IsMovingSolutionOn.v1", "track P")
        + "; movingHamiltonian and KAM.Iso.IsHamiltonianSolutionOn are typing data here"),
    "lpM:s1:model#MovingUniqueOn": d("s1:24-24", "z agrees with every local solution from z(0) on the overlap with J",
        "n : ℕ; m : Fin n → ℝ; μ : ℝ; J : Set ℝ; z : ℝ → Phase (n*2) (" + T + ")", "for every n, m, μ, J, z",
        "for every open convex U ∋ 0 and every solution w of (1) on U with w(0) = z(0), w = z on U ∩ J: uniqueness of the "
        "solution of (1) ('the unique maximal solution', MAIN L74)",
        [PH, ("lpM:s1:model#IsMovingSolutionOn", "the competing local solutions")],
        note=R.format("planetary.d25.MovingUniqueOn.v1", "track P")),
    "lpM:L1#IsNewtonSolutionOn": d("L1:108-108", "finite-interval Newton equations with masses m_j",
        "N : ℕ; masses : Fin N → ℝ; J : Set ℝ; Q, V : ℝ → Fin N → ℝ^2 (" + T + ")", "for every N, masses, J, Q, V",
        "on J: the bodies are pairwise distinct, Q̇_i = V_i and V̇_i = Σ_{j≠i} m_j (Q_j - Q_i)/¦Q_j - Q_i¦^3 (Newton's "
        "equations of Lemma 1, L108)",
        [("lpM:s1:data#planeLength", "the Euclidean distances ¦Q_j - Q_i¦")],
        note=R.format("planetary.d25.IsNewtonSolutionOn.v1", "track P")),
}
