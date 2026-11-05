# Track LP, slice LP-amend, wave 1: AMENDMENTS.md (coverage only; amendments act through the nodes they amend,
# whose NOTE says `AMENDED: N<k>`). Items whose target nodes belong to later waves are deferred until those nodes
# exist (N1 L7; N3 L8; N4 L12, the Q5 split of (35); N5 L10; N6 L13/L14; N7 the L14 routes; N10 L16).

NODES = {}
COV = {
    "lpA:N2": ("NODE lpM:L6#shared-U, lpM:L6",
               "one shared compact U ⊂ Q (closed 4r_g-tube about 𝓛_δ) with its modulus Ω_B; wave 1 records it at "
               "Lemma 6; the Lemma 8 and Lemma 14 targets (lpM:L8#shared-tube, lpM:L14#choices) join in wave 2"),
    "lpA:N8": ("NODE lpM:s1:elements, lpM:s1:elements#strongAMD",
               "AMD convention: C = ΣΛ - ¦L¦ (orientation-free) is the frozen convention (OD-1, D59); the bridge to "
               "Theorem 15's orientation step (lpM:T15#orientation) joins in wave 2"),
    "lpA:N11": ("NODE lpM:L5#perihelion, lpM:L5#bounds",
                "define d_⋆ := a_min m^2/(2 I_max^2) first (perihelion step), then bound ¦p_i¦ ≤ ν_i √(2/d_⋆) "
                "(bounds step)"),
}
DEFER = {
    "lpA:N1": "the target lpM:L7#symplectic is a wave-2 node (slice LP-m3)",
    "lpA:N3": "the target lpM:L8#widths is a wave-2 node (slice LP-m3)",
    "lpA:N4": "the target is Lemma 12's (35), split off by Q5 in wave 2 (slice LP-m4b)",
    "lpA:N5": "the targets are Lemma 10 steps, wave 2 (slice LP-m4a)",
    "lpA:N6": "the targets are Lemma 13 and the route lpM:L14#route-L13, wave 2 (slices LP-m4b, LP-m5)",
    "lpA:N7": "the targets are the route nodes of Lemma 14, wave 2 (slice LP-m5)",
    "lpA:N10": "the target lpM:L16#mu0-choice is a wave-2 node (slice LP-m5)",
}
