NODE: lpM:L17
KIND: lemma
TITLE: Lemma 17: regular spatial Poincare coordinates on the prograde region (44)-(45)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L535-L546
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L548-L578
CONTRACT_ID: lpM:L17
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: a reference unit vector e_3; ν > 0 (one planet, d = 3)
SOURCE_QUANTIFIERS: for every e_3 and ν > 0
SOURCE_CONCLUSION: the map (46) with (18)-(19) is a real analytic symplectic diffeomorphism from the region (44) onto the negative-energy spatial states with (q × p)·e_3 > 0, with form dI ∧ dλ + dx ∧ dy + du ∧ dv, energy -ν^3/(2I^2), angular-momentum magnitude G = I - Γ and projection H = I - Γ - Z (45); it is regular at circular and coplanar orbits; for n bodies the fixed-plane deficit is C_{e_3} = Σ_i I_i - L·e_3 = ½Σ_i(x_i^2 + y_i^2 + u_i^2 + v_i^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L17#rotation, lpM:L17#symplectic, lpM:L17#inverse, lpM:L17#deficit-identity, lpM:s1:elements
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L17#rotation | docs/tracks/LP/source/MAIN.md#L17@L548-L558 | the rotation R of (46) and (45)
EDGE: lpM:L17#symplectic | docs/tracks/LP/source/MAIN.md#L17@L560-L571 | symplecticity
EDGE: lpM:L17#inverse | docs/tracks/LP/source/MAIN.md#L17@L573-L578 | the analytic inverse onto the prograde region
EDGE: lpM:L17#deficit-identity | docs/tracks/LP/source/MAIN.md#L17@L578-L578 | the fixed-plane deficit identity
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#L17@L541-L541 | energy and angular momentum of (2)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L17#rotation
KIND: step
TITLE: (46): R from t = (u,-v,0)/(2 sqrt G); R orthogonal, det 1, q x p = G R e_3 gives (45)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L548-L558
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L548-L558
CONTRACT_ID: lpM:L17#rotation
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L17: a reference unit vector e_3; ν > 0; the region (44) I > 0, λ ∈ 𝕋, (x, y, u, v) ∈ ℝ^4, Γ = (x^2 + y^2)/2, Z = (u^2 + v^2)/2, Γ + Z < I
SOURCE_QUANTIFIERS: for every ν > 0 and every point of (44) (inherited from lpM:L17)
SOURCE_CONCLUSION: with Q, P of (19) embedded in the plane, G = I - Γ > 0, t = (u, -v, 0)/(2√G), c = √(1 - ¦t¦^2), R = (1 - 2¦t¦^2)Id + 2tt^T + 2c[t]_×, q = RQ, p = RP (46); ¦t¦^2 = Z/(2G) < 1/2 makes the roots analytic; [t]_×^2 = tt^T - ¦t¦^2 Id gives R^TR = Id, det R = 1, Re_3 = (-cv/√G, -cu/√G, 1 - Z/G), hence q × p = G Re_3 and (45); (46) is the definition also at Γ = 0 or Z = 0
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L7, lpM:L7#chart-formula
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L7 | docs/tracks/LP/source/MAIN.md#L17@L548-L548 | the planar chart (18)-(19) with angular momentum G = I - Γ
EDGE: lpM:L7#chart-formula | docs/tracks/LP/source/MAIN.md#L17@L548-L548 | Q, P are (19)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L17#symplectic
KIND: step
TITLE: p.dq = I dlambda + Gamma d(-varpi) + Z d(-h_n) + d(2Ie sin E); density of e > 0, Z > 0
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L541-L541
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L560-L571
CONTRACT_ID: lpM:L17#symplectic
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L17: a reference unit vector e_3; ν > 0; the region (44) I > 0, λ ∈ 𝕋, (x, y, u, v) ∈ ℝ^4, Γ = (x^2 + y^2)/2, Z = (u^2 + v^2)/2, Γ + Z < I
SOURCE_QUANTIFIERS: for every ν > 0 and every point of (44) (inherited from lpM:L17)
SOURCE_CONCLUSION: where e > 0 and Z > 0, with node longitude h_n, inclination ι and perihelion longitude ϖ, R = R_z(h_n)R_x(ι)R_z(-h_n); the varying rotations contribute G dg and H dh_n (zero about the line of nodes), so with Lemma 7's computation p·dq = I dλ + Γ d(-ϖ) + Z d(-h_n) + d(2Ie sin E); exterior differentiation gives the form; the set e > 0, Z > 0 is dense and both sides are analytic, so equality extends to the circular and coplanar loci
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L17#rotation, lpM:L7#symplectic, lpM:ext-identity-theorem
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L17#rotation | docs/tracks/LP/source/MAIN.md#L17@L566-L566 | the rotation R and q × p = G Re_3
EDGE: lpM:L7#symplectic | docs/tracks/LP/source/MAIN.md#L17@L566-L566 | the unrotated calculation of Lemma 7
EDGE: lpM:ext-identity-theorem | docs/tracks/LP/source/MAIN.md#L17@L571-L571 | analytic equality extends from a dense set
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L17#inverse
KIND: step
TITLE: inverse from w-hat = (q x p)/G: c, u, v reconstruct R; Lemma 7's inverse gives x, y, lambda
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L573-L578
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L573-L578
CONTRACT_ID: lpM:L17#inverse
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L17: a reference unit vector e_3; ν > 0; the region (44) I > 0, λ ∈ 𝕋, (x, y, u, v) ∈ ℝ^4, Γ = (x^2 + y^2)/2, Z = (u^2 + v^2)/2, Γ + Z < I
SOURCE_QUANTIFIERS: for every ν > 0 and every point of (44) (inherited from lpM:L17)
SOURCE_CONCLUSION: for ŵ = (q × p)/G with ŵ_3 > 0: recover I, G from energy and angular momentum, c = √((1 + ŵ_3)/2), u = -√G ŵ_2/c, v = -√G ŵ_1/c reconstruct R; R^{-1}q, R^{-1}p are planar with positive angular momentum and Lemma 7's inverse recovers x, y, λ: onto, unique modulo 2π, analytically invertible, image exactly the prograde negative-energy region
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L7#inverse, lpM:L17#rotation
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L7#inverse | docs/tracks/LP/source/MAIN.md#L17@L578-L578 | Lemma 7's explicit inverse
EDGE: lpM:L17#rotation | docs/tracks/LP/source/MAIN.md#L17@L576-L576 | R and q × p = G Re_3
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L17#deficit-identity
KIND: claim
TITLE: fixed-plane deficit C_{e_3} = sum I_i - L.e_3 = ¦z¦^2/2 (summing (45))
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L545-L546
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L17@L578-L578
CONTRACT_ID: lpM:L17#deficit-identity
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L17: a reference unit vector e_3; ν > 0; the region (44) I > 0, λ ∈ 𝕋, (x, y, u, v) ∈ ℝ^4, Γ = (x^2 + y^2)/2, Z = (u^2 + v^2)/2, Γ + Z < I; n bodies
SOURCE_QUANTIFIERS: for every point of the n-fold product chart
SOURCE_CONCLUSION: C_{e_3} = Σ_i I_i - L·e_3 = Σ_i(Γ_i + Z_i) = ½Σ_i(x_i^2 + y_i^2 + u_i^2 + v_i^2)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L17#rotation
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L17#rotation | docs/tracks/LP/source/MAIN.md#L17@L578-L578 | (45): H_i = I_i - Γ_i - Z_i is the e_3-projection of L_i
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L18
KIND: lemma
TITLE: Lemma 18: spatial whole-sublevel complex domain (47), m = 2n
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L582-L586
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L588-L597
CONTRACT_ID: lpM:L18
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: the data (n, ν, 𝒜, δ) of lpM:s1:data, spatial (d = 3); 𝓛_δ as in Lemma 8
SOURCE_QUANTIFIERS: there exist r_*, s, b, M > 0 (fixed first, independent of the reference direction); then for every I^0 ∈ 𝓛_δ, with Z_0 = {z ∈ ℝ^{4n} : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (47)
SOURCE_CONCLUSION: the conclusions of Lemma 8 hold spatially with m = 2n slow pairs and the product chart of Lemma 17; the domain includes all states allowed by (6) after aligning e_3 with the initial total angular momentum
CONSTANT_SCOPE: r_*, s, b, M depend only on (n, ν, 𝒜, δ), not on the reference direction
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L18#margins, lpM:L18#whole-ball-safe, lpM:L18#extension, lpM:L18#rotation-invariance, lpM:L18#alignment, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L18#margins | docs/tracks/LP/source/MAIN.md#L18@L588-L593 | the fixed positive margins
EDGE: lpM:L18#whole-ball-safe | docs/tracks/LP/source/MAIN.md#L18@L593-L593 | Lemma 5 on the whole ball
EDGE: lpM:L18#extension | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the complex extension (Lemma 8's argument in 6n coordinates)
EDGE: lpM:L18#rotation-invariance | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | independence of the reference direction
EDGE: lpM:L18#alignment | docs/tracks/LP/source/MAIN.md#L18@L597-L597 | the alignment of e_3 with L
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L18@L584-L584 | B occurs in (47)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N2, N3 (via Lemma 8's construction), N12 (AMENDMENTS.md L21: the spatial tube typing is engineering only, no graph obligation)

NODE: lpM:L18#margins
KIND: step
TITLE: Gamma_i + Z_i <= I_i - 3 delta/16: G_i, H_i >= 3 delta/16, c_i^2 > 1/2
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L582-L586
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L588-L593
CONTRACT_ID: lpM:L18#margins
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L18: the data (n, ν, 𝒜, δ), spatial; 𝓛_δ as in Lemma 8; Z_0 = {z ∈ ℝ^{4n} : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (47); real ‖I - I^0‖_∞ ≤ 4r_g and z ∈ (47)
SOURCE_QUANTIFIERS: for every I^0 ∈ 𝓛_δ (the widths are fixed before I^0; inherited from lpM:L18)
SOURCE_CONCLUSION: Γ_i + Z_i ≤ B(I^0) - δ/4 ≤ B(I) - 3δ/16 ≤ I_i - 3δ/16, hence G_i ≥ 3δ/16, H_i ≥ 3δ/16, c_i^2 = 1 - Z_i/(2G_i) > 1/2: all new radicands and denominators in (46) have a fixed positive margin
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L8#shared-tube, lpM:L17, lpM:s1:thresholds#orderedStrongThreshold
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L8#shared-tube | docs/tracks/LP/source/MAIN.md#L18@L590-L590 | the real action neighborhood of Lemma 8 with Ω_B(4r_g) ≤ δ/16
EDGE: lpM:L17 | docs/tracks/LP/source/MAIN.md#L18@L593-L593 | (45): G = I - Γ, H = I - Γ - Z
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#L18@L590-L590 | B(I) ≤ B_⋆(I) ≤ I_i
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L18#whole-ball-safe
KIND: step
TITLE: fixed-plane deficit = ¦z¦^2/2 >= sum I_i D(e_i): Lemma 5 applies on the whole ball
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L586-L586
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L593-L593
CONTRACT_ID: lpM:L18#whole-ball-safe
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L18: the data (n, ν, 𝒜, δ), spatial; 𝓛_δ as in Lemma 8; Z_0 = {z ∈ ℝ^{4n} : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (47)
SOURCE_QUANTIFIERS: for every I^0 ∈ 𝓛_δ (the widths are fixed before I^0; inherited from lpM:L18)
SOURCE_CONCLUSION: the fixed-plane deficit equals ¦z¦_2^2/2 and each I_i - H_i ≥ I_i - ¦L_i¦ = I_i D(e_i); hence Lemma 5 applies to every point of the ball, including points whose total angular momentum is not parallel to e_3
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L17#deficit-identity, lpM:L2, lpM:L5, lpM:L18#margins, lpM:s1:thresholds#eccDeficit
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L17#deficit-identity | docs/tracks/LP/source/MAIN.md#L18@L593-L593 | C_{e_3} = ¦z¦^2/2
EDGE: lpM:L2 | docs/tracks/LP/source/MAIN.md#L18@L593-L593 | ¦L_i¦ = I_i √(1 - e_i^2) by (11)
EDGE: lpM:L5 | docs/tracks/LP/source/MAIN.md#L18@L593-L593 | Lemma 5 in its list form Σ I_i D(e_i) ≤ B(I) - m
EDGE: lpM:L18#margins | docs/tracks/LP/source/MAIN.md#L18@L593-L593 | Σ(Γ_i + Z_i) ≤ B(I) - 3δ/16
EDGE: lpM:s1:thresholds#eccDeficit | docs/tracks/LP/source/MAIN.md#L18@L593-L593 | D(e) = 1 - √(1 - e^2)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L18#extension
KIND: step
TITLE: Lemma 8's gluing, uniform widths and complex denominators verbatim in 6n coordinates
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L582-L586
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L595-L595
CONTRACT_ID: lpM:L18#extension
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L18: the data (n, ν, 𝒜, δ), spatial; 𝓛_δ as in Lemma 8; Z_0 = {z ∈ ℝ^{4n} : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (47)
SOURCE_QUANTIFIERS: for every I^0 ∈ 𝓛_δ (the widths are fixed before I^0; inherited from lpM:L18)
SOURCE_CONCLUSION: the family over compact 𝓛_δ, the real action neighborhood and a full angle cell is compact; (18)-(19) and (46) with the margins give holomorphic local extensions; the gluing, uniform-width and complex-denominator arguments of Lemma 8 apply verbatim in 6n coordinates; every (q_i - q_j)·(q_i - q_j) has positive real part on the chosen complex tube
CONSTANT_SCOPE: the widths depend only on (n, ν, 𝒜, δ)
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L18#margins, lpM:L18#whole-ball-safe, lpM:L8#newton-extension, lpM:L8#gluing, lpM:L8#denominators, lpM:L8#widths, lpM:L8#exact-split, lpM:L17
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L18#margins | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the positive margins of (46)
EDGE: lpM:L18#whole-ball-safe | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the real phases are safe (Lemma 5)
EDGE: lpM:L8#newton-extension | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the local extension argument
EDGE: lpM:L8#gluing | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the gluing and finite-subcover argument
EDGE: lpM:L8#denominators | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the complex-denominator estimate
EDGE: lpM:L8#widths | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the uniform widths and bounds
EDGE: lpM:L8#exact-split | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the product chart gives the exact split h + μf
EDGE: lpM:L17 | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the chart (46) is analytic on its region
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L18#rotation-invariance
KIND: step
TITLE: scalar products and potentials are invariant under a simultaneous rotation: bounds independent of the frame
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L584-L586
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L595-L595
CONTRACT_ID: lpM:L18#rotation-invariance
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L18: the data (n, ν, 𝒜, δ), spatial; 𝓛_δ as in Lemma 8; Z_0 = {z ∈ ℝ^{4n} : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (47)
SOURCE_QUANTIFIERS: for every I^0 ∈ 𝓛_δ (the widths are fixed before I^0; inherited from lpM:L18)
SOURCE_CONCLUSION: the exact scalar products and Newtonian potentials are invariant under a simultaneous real orthogonal rotation of positions and momenta, so the domain bounds can be chosen for an abstract orthonormal frame, independently of its orientation
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:s1:model, lpM:L18#extension
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:s1:model | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | (1) is rotation invariant
EDGE: lpM:L18#extension | docs/tracks/LP/source/MAIN.md#L18@L595-L595 | the bounds being made frame-independent
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:L18#alignment
KIND: step
TITLE: one fixed rotation per solution takes L/¦L¦ to e_3; C_{e_3} = C along it; Lemma 17 covers it
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L586-L586
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#L18@L597-L597
CONTRACT_ID: lpM:L18#alignment
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:L18: the data (n, ν, 𝒜, δ), spatial; 𝓛_δ as in Lemma 8; Z_0 = {z ∈ ℝ^{4n} : ¦z¦_2^2/2 ≤ B(I^0) - δ/4} (47); an actual initial state with (6)
SOURCE_QUANTIFIERS: for every I^0 ∈ 𝓛_δ (the widths are fixed before I^0; inherited from lpM:L18)
SOURCE_CONCLUSION: Lemma 3 gives L ≠ 0; a fixed orientation-preserving orthogonal map taking L/¦L¦ to e_3, applied to q and p, is symplectic (one per solution, constants rotation invariant); conservation of L gives C_{e_3} = C along the solution; positive individual projections let Lemma 17 cover it until the stopped boundary
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L3, lpM:L18#rotation-invariance, lpM:L17
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L3 | docs/tracks/LP/source/MAIN.md#L18@L597-L597 | Lemma 3: L ≠ 0 and positive projections H_i under C < B_⋆ (supplied by (6)), and conservation of L
EDGE: lpM:L18#rotation-invariance | docs/tracks/LP/source/MAIN.md#L18@L597-L597 | constants are rotation invariant
EDGE: lpM:L17 | docs/tracks/LP/source/MAIN.md#L18@L597-L597 | the chart covers the prograde states
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:T19
KIND: theorem
TITLE: Theorem 19: spatial nonresonant exponential safety (the §1 conclusion for d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L601-L601
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
CONTRACT_ID: lpM:T19
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: d = 3; n ≥ 2; ν_i > 0 with max_i ν_i = 1; 𝒜 ⊂ {0 < a_1 < ... < a_n} compact; δ, γ > 0; τ > n - 1
SOURCE_QUANTIFIERS: there exist μ_0, c, T_0, A_I, A_a, d_⋆, d_pair, A_osc > 0; then for every 0 < μ ≤ μ_0 and every spatial initial state with q_i ≠ 0, E_i < 0 and (6), including circular or coplanar initial orbits
SOURCE_CONCLUSION: the conclusion of §1 in d = 3: the unique maximal solution exists on [-T_μ, T_μ] (7), with ellipticity, I(t) ∈ Q, (8), (9), the star and all pair distances, and the osculating radii and half gaps
CONSTANT_SCOPE: the constants depend only on (n, ν, 𝒜, δ, γ, τ) (d = 3) and precede μ and the initial state; N10
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:T19#align, lpM:T19#apply-L14, lpM:T19#osculating, lpM:T19#reconstruction, lpM:T19#unrotate, lpM:s1:data, lpM:s1:dioph, lpM:s1:elements, lpM:s1:thresholds#orderedStrongThreshold, lpM:s1:chamber#chamber
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:T19#align | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | alignment, the ball (47), the symplectic chart
EDGE: lpM:T19#apply-L14 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | Lemma 14 with m = 2n
EDGE: lpM:T19#osculating | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | Lemma 16 in dimension three
EDGE: lpM:T19#reconstruction | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | Lemma 1
EDGE: lpM:T19#unrotate | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | back to the original frame
EDGE: lpM:s1:data | docs/tracks/LP/source/MAIN.md#s1@L70-L70 | the fixed data
EDGE: lpM:s1:dioph | docs/tracks/LP/source/MAIN.md#s1@L72-L72 | (6) contains (5)
EDGE: lpM:s1:elements | docs/tracks/LP/source/MAIN.md#s1@L72-L72 | C, a, e, I
EDGE: lpM:s1:thresholds#orderedStrongThreshold | docs/tracks/LP/source/MAIN.md#s1@L72-L72 | B occurs in (6)
EDGE: lpM:s1:chamber#chamber | docs/tracks/LP/source/MAIN.md#s1@L79-L79 | I(t) ∈ Q
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: spatial MAIN theorem; its frozen statement is LP2 (packet LP-athm-w3). 'Lemmas 1-6, 9-14, 16-18' is read with N7 (Lemmas 12, 13 are alternative routes inside Lemma 14). AMENDED: N7, N8, N10.

NODE: lpM:T19#align
KIND: step
TITLE: Lemma 18 aligns the frame, gives the ball (47) and the collar; Lemma 17 symplectic chart; (1), (4) exact
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L601-L601
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
CONTRACT_ID: lpM:T19#align
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:T19: the data of §1 with d = 3; 0 < μ ≤ μ_0; a spatial initial state with q_i ≠ 0, E_i < 0 and (6)
SOURCE_QUANTIFIERS: for every such μ and initial state (inherited from lpM:T19)
SOURCE_CONCLUSION: after the fixed rotation of Lemma 18, the entire ball (47) and a uniform complex collar are available; the chart is symplectic (Lemma 17) and the Kepler energy and exact perturbation are (1), (4)
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L18, lpM:L18#alignment, lpM:L17, lpM:s1:fast
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L18 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the aligned frame and the domain
EDGE: lpM:L18#alignment | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | one fixed rotation per solution
EDGE: lpM:L17 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the symplectic chart
EDGE: lpM:s1:fast | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the Kepler energy h of (4)
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:T19#apply-L14
KIND: step
TITLE: n fast angles, 2n slow pairs; ¦z(t)¦^2/2 = C(t) by conservation; Lemma 14 proves (7)-(9)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L601-L601
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
CONTRACT_ID: lpM:T19#apply-L14
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:T19: the data of §1 with d = 3; 0 < μ ≤ μ_0; a spatial initial state with q_i ≠ 0, E_i < 0 and (6)
SOURCE_QUANTIFIERS: for every such μ and initial state (inherited from lpM:T19)
SOURCE_CONCLUSION: with n fast angles and m = 2n slow pairs, the drift suppliers apply with only dimension constants changed (small divisors k·ω(I^0), k ∈ ℤ^n, no secular divisors); conservation of the vector angular momentum gives ¦z(t)¦^2/2 = C(t) in the physical chart; these discharge every condition of Lemma 14, which proves the exponential interval, the action and AMD bounds, moving-threshold safety, separation and continuation
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L14, lpM:T19#align, lpM:L17#deficit-identity, lpM:L3#dynamic
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L14 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | Lemma 14
EDGE: lpM:T19#align | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the chart and domain premises
EDGE: lpM:L17#deficit-identity | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | C_{e_3} = ¦z¦^2/2
EDGE: lpM:L3#dynamic | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | conservation of L keeps C_{e_3} = C
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:T19#osculating
KIND: step
TITLE: Lemma 16 in dimension three: the osculating conclusion
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L601-L601
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
CONTRACT_ID: lpM:T19#osculating
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:T19: the data of §1 with d = 3; 0 < μ ≤ μ_0; a spatial initial state with q_i ≠ 0, E_i < 0 and (6)
SOURCE_QUANTIFIERS: for every such μ and initial state (inherited from lpM:T19); t ∈ [-T_μ, T_μ]
SOURCE_CONCLUSION: as lpM:T15#osculating, in d = 3
CONSTANT_SCOPE: A, A_osc depend only on Lemma 5's compact set and the masses
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L16, lpM:L16#mu0-choice, lpM:L16#half-gaps, lpM:L14#separation, lpM:T19#apply-L14
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L16 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | Lemma 16 (d = 3)
EDGE: lpM:L16#mu0-choice | docs/tracks/LP/source/MAIN.md#L16@L528-L528 | N10
EDGE: lpM:L16#half-gaps | docs/tracks/LP/source/MAIN.md#L16@L529-L529 | the osculating half gaps
EDGE: lpM:L14#separation | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the orbit stays in Lemma 5's compact set (m = δ/2)
EDGE: lpM:T19#apply-L14 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the solution on [-T_μ, T_μ]
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: AMENDED: N10 (AMENDMENTS.md L19)

NODE: lpM:T19#reconstruction
KIND: step
TITLE: Lemma 1 reconstructs the exact Newtonian solution (d = 3)
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L601-L601
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
CONTRACT_ID: lpM:T19#reconstruction
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:T19: the data of §1 with d = 3; 0 < μ ≤ μ_0; a spatial initial state with q_i ≠ 0, E_i < 0 and (6)
SOURCE_QUANTIFIERS: for every such μ and initial state (inherited from lpM:T19)
SOURCE_CONCLUSION: the solution reconstructs a Newtonian (1+n)-body solution with masses (1, μν_i); star and pair distances are ¦q_i¦, ¦q_i - q_j¦
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L1, lpM:T19#apply-L14
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L1 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | Lemma 1
EDGE: lpM:T19#apply-L14 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the collision-free solution
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -

NODE: lpM:T19#unrotate
KIND: step
TITLE: the inverse fixed rotation returns to the original frame without changing any inequality
STATEMENT_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L601-L601
PROOF_SOURCE: docs/tracks/LP/source/MAIN.md#T19@L603-L603
CONTRACT_ID: lpM:T19#unrotate
CONTRACT_VERSION: 1
SOURCE_HYPOTHESES: context of the proof of lpM:T19: the data of §1 with d = 3; 0 < μ ≤ μ_0; a spatial initial state with q_i ≠ 0, E_i < 0 and (6)
SOURCE_QUANTIFIERS: for every such μ and initial state (inherited from lpM:T19)
SOURCE_CONCLUSION: all the inequalities of the conclusion are invariant under the inverse fixed rotation
CONSTANT_SCOPE: none
FROZEN_FILE: -
FROZEN_DECL: -
FROZEN_ANCHOR_ID: -
FROZEN_ABI_SHA256: -
DEPS: lpM:L18#rotation-invariance, lpM:T19#apply-L14, lpM:T19#osculating
ROUTES: -
ROUTE_FOR: -
EDGE: lpM:L18#rotation-invariance | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | rotation invariance of lengths, H and C
EDGE: lpM:T19#apply-L14 | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the inequalities in the aligned frame
EDGE: lpM:T19#osculating | docs/tracks/LP/source/MAIN.md#T19@L603-L603 | the osculating inequalities in the aligned frame
TOPOLOGY_STATUS: PROPOSED
EXTRACTOR: kam-lp
REVIEWER: -
LEAN_STATUS: BYPASSED
LEAN_REF: -
LEAN_NOTE: D27 route substitution: the sealed root's Lean proof (provider -> implementation theorem) follows the implementation route; this source step is not separately formalized; confirmed by the D65 global review; previous status NOT_STARTED
NOTE: -
