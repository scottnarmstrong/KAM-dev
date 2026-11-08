# Track LP, slice LP-ext (writer-owned): the closed external list of SPEC §3, wave-1 part. Each external is a leaf
# (KIND external, LEAN_STATUS EXTERNAL) located at its first appeal in MAIN; its coverage items are the citation
# items of the MAIN slices. The five externals first consumed in wave 2 are not rendered yet.


def ext(stmt, title, H, C):
    return dict(kind="external", title=title, stmt=stmt, proof="-", H=H, Q="for every instance of the hypotheses",
                C=C, S="none", note="external input of the closed list (SPEC §3); Mathlib-level")


NODES = {
    "lpM:ext-ftc": ext("L3:139-139", "fundamental theorem of calculus (zero derivative on an interval)",
        "f differentiable on a connected interval J with derivative 0 (or with integrable derivative)",
        "f is constant on J (f(t) - f(s) = ∫_s^t f')"),
    "lpM:ext-compact-min": ext("L4:149-149", "extreme values of a continuous function on a nonempty compact set",
        "K a nonempty compact set; f : K → ℝ continuous",
        "f attains its minimum and its maximum on K (for finitely many functions, the minimum of their minima)"),
    "lpM:ext-heine-cantor": ext("L4:154-154", "Heine-Cantor: continuity on a compact set is uniform",
        "K a compact metric space; f continuous on K", "f is uniformly continuous on K"),
    "lpM:ext-picard": ext("L6:189-189", "contraction mapping principle / Picard iteration for the integral equation",
        "X bounded with bounded derivative (locally Lipschitz) on a closed ball B(z_*, ρ); a time T below ρ/sup¦X¦ and "
        "the inverse Lipschitz bound", "the map z ↦ z_* + ∫_0^t X(z(u)) du is a contraction of C([0,T], B(z_*, ρ)) and "
        "its fixed point is a solution of ż = X(z), z(0) = z_*"),
    "lpM:ext-gronwall": ext("L6:189-189", "uniqueness of ODE solutions by iterating the integral inequality",
        "X Lipschitz on a set containing two solutions with the same initial value",
        "the two solutions coincide (iterating ¦z_1 - z_2¦(t) ≤ L ∫_0^t ¦z_1 - z_2¦ gives zero)"),
}
DELETE = {e: "first consumed in wave 2 (Lemmas 7-11); rendered with its consumers" for e in (
    "lpM:ext-cauchy-estimates", "lpM:ext-compact-cover", "lpM:ext-fourier-contour", "lpM:ext-holomorphic-limit",
    "lpM:ext-identity-theorem")}
