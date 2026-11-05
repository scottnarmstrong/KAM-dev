# Track LP, packet LP-ext-w2 (writer-owned; the wave-2 part of slice LP-ext, kept in its own packet so that the wave-1
# packet LP-ext under review R1 is not touched): the five externals of the closed list (SPEC §3) first consumed in
# wave 2. Each is a leaf (KIND external, LEAN_STATUS EXTERNAL) located at its first appeal in MAIN; its coverage items
# are the citation items of the MAIN slices LP-m3 and LP-m4a.


def ext(stmt, title, H, C):
    return dict(kind="external", title=title, stmt=stmt, proof="-", H=H, Q="for every instance of the hypotheses",
                C=C, S="none", note="external input of the closed list (SPEC §3); Mathlib-level")


NODES = {
    "lpM:ext-holomorphic-limit": ext("L7:211-211", "uniform limits of holomorphic maps are holomorphic",
        "a sequence of holomorphic maps on an open set of ℂ^k converging uniformly (on compact subsets)",
        "the limit is holomorphic (in particular a uniformly convergent iteration of holomorphic maps has a holomorphic "
        "limit)"),
    "lpM:ext-identity-theorem": ext("L7:238-238", "identity theorem for analytic maps on a connected domain",
        "two analytic (holomorphic, or real analytic) maps on a connected open set that agree on a nonempty open subset "
        "(or have the same power series at one point)",
        "they agree on the whole connected set"),
    "lpM:ext-compact-cover": ext("L8:265-265", "finite subcover of a compact set",
        "K a compact subset of a metric space; an open cover of K (e.g. balls centered at points of K)",
        "finitely many members of the cover already cover K (with half-sized balls: a Lebesgue-number neighborhood)"),
    "lpM:ext-cauchy-estimates": ext("L8:271-271",
        "Cauchy's integral formula and estimates; holomorphic square root on a half plane",
        "f holomorphic on a neighborhood of a closed polydisk of radius ρ, bounded by M there; w in the half plane "
        "Re w > 0",
        "Cauchy's formula holds and ¦∂^α f¦ ≤ α! M ρ^{-¦α¦} at the center (one-variable form: ¦f'¦ ≤ M/ρ); the principal "
        "square root is holomorphic on Re w > 0 with positive real part"),
    "lpM:ext-fourier-contour": ext("L9:298-298",
        "Fourier coefficients of periodic holomorphic maps and the contour shift",
        "f holomorphic and 2π-periodic in each angle on the strip ¦Im θ¦_∞ < σ, bounded by M on narrower strips",
        "the Fourier coefficients are integrals over the real torus, independent of the contour within the strip, and "
        "¦f_k¦ ≤ M e^{-σ'¦k¦_1} for every σ' < σ (shift each contour with sign opposite to the Fourier index)"),
}
