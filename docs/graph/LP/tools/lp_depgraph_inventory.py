#!/usr/bin/env python3
"""Generate the pre-anchor coverage inventory of track LP (docs/graph/LP/draft/coverage-*.md) and slices.json.

Source-only: reads no Lean. Every record is COVERAGE_STATUS PROPOSED, EXTRACTOR lp-preanchor-inventory.
usage: python3 -I docs/graph/LP/tools/lp_depgraph_inventory.py REPO_ROOT   (pre-extraction only; overwrites draft/ and packets/slices.json)
"""
import json
import sys
from pathlib import Path

ROOT = Path(sys.argv[1])
OUT = ROOT / "docs/graph/LP"
MAIN = "docs/tracks/LP/source/MAIN.md"
AMD = "docs/tracks/LP/source/AMENDMENTS.md"
LP3 = "docs/tracks/LP/lp3/LP3-PLAN.md"
TAG = "lp-preanchor-inventory"

ALL = "LP0,LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2"
DYN = "LP1,LP1-H,LP2,LP2-H,LP3-1,LP3-2"
DIO = "LP1,LP1-H,LP2,LP2-H"
R12 = "LP1,LP1-H,LP2,LP2-H (route-L12 only)"
R13 = "LP1,LP1-H,LP2,LP2-H (route-L13 only, the Lean route)"
PL = "LP1,LP1-H,LP3-1"
SP = "LP2,LP2-H,LP3-2"
HALF = "LP1-H,LP2-H"
NONE = "none"

# MAIN slices (first line of the item decides; anchors are re-homed to LP-athm/LP-adef after freeze)
MAIN_SLICES = [("LP-m1", 1, 93), ("LP-m2a", 94, 160), ("LP-m2b", 161, 189), ("LP-m3", 190, 271),
               ("LP-m4a", 272, 379), ("LP-m4b", 380, 464), ("LP-m5", 465, 529), ("LP-m6", 530, 603),
               ("LP-m78", 604, 679)]
LP3_SLICES = [("LP3-a", 1, 258), ("LP3-b", 259, 506)]


def slice_of(path, first):
    table = MAIN_SLICES if path == MAIN else LP3_SLICES if path == LP3 else [("LP-amend", 1, 26)]
    for name, a, b in table:
        if a <= first <= b:
            return name
    raise ValueError((path, first))


# (item, kind, anchor-token, first, last, disposition, anchors, note)
M = [
    # preamble
    ("lpM:h:title", "heading", "title", 1, 3, None, NONE, "title and date"),
    ("lpM:intro#result", "claim", "intro", 5, 5, None, NONE,
     "summary of T15/T19 and of what is not claimed; the content is restated by §1 and the theorems"),
    ("lpM:intro#method", "claim", "intro", 7, 7, None, NONE,
     "method overview; the mathematics is in L9-L13; the L13 reuse remark is L13's own statement"),
    # §1
    ("lpM:h:s1", "heading", "s1", 9, 9, None, NONE, "section heading"),
    ("lpM:s1:data", "definition", "s1", 11, 15, "lpM:s1:data", ALL,
     "fixed data n>=2, nu>0 with max nu=1, compact ordered A, delta, gamma>0, tau>n-1, d in {2,3}, the two norms; "
     "LP0 uses only n, nu; LP3 drops gamma, tau; a result's SOURCE_HYPOTHESES name this package"),
    ("lpM:s1:model", "definition", "s1", 17, 24, "lpM:s1:model", DYN,
     "units G=1, star mass 1, masses mu*nu_i, iota_X Omega=-dH, exact Hamiltonian (1), physical domain, physical time"),
    ("lpM:eq1", "display", "s1", 18, 23, "lpM:s1:model", DYN, "display (1) maps to its enclosing definition"),
    ("lpM:s1:elements", "definition", "s1", 26, 37, "lpM:s1:elements", ALL,
     "v_i, E_i, eccentricity vector, a_i, I_i=Lambda_i, e_i, L_i, L, C; planar cross product; frozen element "
     "definitions (planar reused, spatial new) bind here after freeze; CHAR: sourceKepler_axis_pos, "
     "spatialSourceKeplerAxis_pos, spatialSourceKeplerAction_pos, spatialSourceKeplerAction_sq"),
    ("lpM:eq2", "display", "s1", 32, 36, "lpM:s1:elements", ALL,
     "C = sum I - |L| (orientation-free; amendment N8, ruling OD-1/D59)"),
    ("lpM:s1:elements#elliptic-remark", "claim", "s1", 37, 37, "lpM:L5#perihelion", ALL,
     "'our hypotheses imply e_i<1' is a forward remark; it is a consequence of L5 (16), not a premise"),
    ("lpM:s1:model#normalization", "claim", "s1", 39, 39, "lpM:s1:model", DYN,
     "physical L and AMD are mu*L, mu*C; delta is normalized; splitting (1) uses central Kepler parameter one"),
    ("lpM:s1:chamber", "definition", "s1", 41, 44, "lpM:s1:chamber", ALL,
     "action chamber Q; carrier of the thresholds (OrderedActions, OD-2/OD-11)"),
    ("lpM:s1:thresholds", "definition", "s1", 45, 55, "lpM:s1:thresholds", ALL,
     "a_i(I), D(u), B_ij, B_cross, B_star, B; attained minima by L4; on the chamber carrier; "
     "CHAR: orderedPairThreshold_isLeast, orderedPairThreshold_existsUnique_value, orderedCrossThreshold_isLeast, "
     "orderedStrongThreshold_isLeast"),
    ("lpM:eq3", "display", "s1", 46, 54, "lpM:s1:thresholds", ALL, "display (3) maps to its enclosing definition"),
    ("lpM:s1:fast", "definition", "s1", 57, 61, "lpM:s1:fast", DYN,
     "fast Hamiltonian h and radian frequencies omega (4); LP3 uses h for the Kepler data of the partial-convex input"),
    ("lpM:eq4", "display", "s1", 58, 61, "lpM:s1:fast", DYN, "display (4)"),
    ("lpM:s1:dioph", "definition", "s1", 62, 67, "lpM:s1:dioph", DIO,
     "Diophantine condition (5) at omega(I^0), angles of period 2pi (L13 converts to period one); LP3 has no "
     "arithmetic premise"),
    ("lpM:eq5", "display", "s1", 63, 66, "lpM:s1:dioph", DIO, "display (5)"),
    ("lpM:s1:conclusion", "claim", "s1", 69, 91, "lpM:T15,lpM:T19", DYN,
     "the common conclusion is the statement content of T15 (d=2) and T19 (d=3), i.e. of LP1/LP2; LP3-1/LP3-2 "
     "restate it with the changes of LP3-PLAN §1.2; includes 'initial pair collisions excluded' (L78) and the "
     "osculating sentence (L91, via L16, N10)"),
    ("lpM:eq6", "display", "s1", 71, 73, "lpM:T15,lpM:T19", DYN, "premises (6); LP3 drops (5)"),
    ("lpM:eq7", "display", "s1", 75, 77, "lpM:T15,lpM:T19", DIO,
     "horizon (7), a = 1/(2(tau+1)); LP3 replaces the exponent"),
    ("lpM:eq8", "display", "s1", 79, 86, "lpM:T15,lpM:T19", DYN, "drift and margin conclusions (8)"),
    ("lpM:eq9", "display", "s1", 87, 90, "lpM:T15,lpM:T19", DYN, "canonical annulus separation (9)"),
    ("lpM:s1:no-crossing", "definition", "s1", 93, 93, "lpM:T15,lpM:T19", DYN,
     "meaning of 'no orbit crossing' (strict ordering of the radial annuli; OD-5/OD-9); interpretive part of the "
     "conclusion"),
    ("lpM:s1:half-integer", "claim", "s1", 93, 93, "lpM:s1:half-integer", HALF,
     "tau = n - 1/2 is admissible and gives exponent 1/(2n+1); the arithmetic step of the corollary anchors"),
    # §2
    ("lpM:h:s2", "heading", "s2", 95, 95, None, NONE, "section heading"),
    ("lpM:L1", "lemma", "L1", 97, 108, "lpM:L1", DYN,
     "normalization and Newtonian reconstruction (frozen IsNewtonSolutionOn/barycentric maps); LP0 reaches it only "
     "through lpM:L3#conservation if L3 stays one node (SPEC Q3)"),
    ("lpM:L1#reduction", "proof-region", "L1", 101, 102, "lpM:L1#reduction", DYN,
     "translation reduction and division by mu give (1)"),
    ("lpM:L1#reconstruction", "proof-region", "L1", 104, 108, "lpM:L1#reconstruction", DYN,
     "explicit inverse, velocities (10), Newton's equations"),
    ("lpM:eq10", "display", "L1", 105, 107, "lpM:L1#reconstruction", DYN,
     "(10) is consumed by L3 (recoil) and L16 (V_i); extractor may refine it to a display node lpM:L1#eq10"),
    ("lpM:L2", "lemma", "L2", 110, 128, "lpM:L2", ALL,
     "orbital identities (11)-(12), including e=1; CHAR: sourceKepler_ecc_le_one, sourceKeplerPeri_le_planeLength, "
     "planeLength_le_sourceKeplerApo and the spatial ecc/angular-momentum/peri/apo characterizations"),
    ("lpM:eq11", "display", "L2", 113, 116, "lpM:L2", ALL, "display (11)"),
    ("lpM:eq12", "display", "L2", 118, 121, "lpM:L2", ALL, "display (12)"),
    ("lpM:L2#ecc-identity", "proof-region", "L2", 124, 124, "lpM:L2#ecc-identity", ALL,
     "expansion of |e|^2 and substitution 2E=-1/a give (11)"),
    ("lpM:L2#radial-bounds", "proof-region", "L2", 124, 128, "lpM:L2#radial-bounds", ALL,
     "radial/tangential decomposition, completing the square: (12)"),
    ("lpM:L3", "lemma", "L3", 130, 139, "lpM:L3", ALL,
     "L constant, C>=0, L!=0 and positive projections below B_star, identity and inequality (13), H_i>=m; "
     "CHAR: sourceStrongAMD_nonneg, sum_action_mul_eccDeficit_le_sourceStrongAMD and spatial twins"),
    ("lpM:eq13", "display", "L3", 133, 136, "lpM:L3", ALL,
     "(13): identity part is dynamic (DYN), inequality part is static (LP0); see SPEC Q3"),
    ("lpM:L3#planar-orientation", "claim", "L3", 137, 137, "lpM:L3#planar-orientation", PL,
     "planar orientation choice L>0; consumed by T15's reflection step (N8, OD-1)"),
    ("lpM:L3#conservation", "proof-region", "L3", 139, 139, "lpM:L3#conservation", DYN,
     "dL/dt=0: recoil term, central forces, pair torques; constancy by the fundamental theorem of calculus"),
    ("lpM:L3#amd-nonneg", "proof-region", "L3", 139, 139, "lpM:L3#amd-nonneg", ALL, "|L|<=sum|L_i|<=sum I_i by (11)"),
    ("lpM:L3#L-nonzero", "proof-region", "L3", 139, 139, "lpM:L3#L-nonzero", ALL, "L=0 would give C>=min I_i"),
    ("lpM:L3#projections", "proof-region", "L3", 139, 139, "lpM:L3#projections", ALL, "H_i>=I_i-C, hence H_i>=m"),
    ("lpM:L3#deficit", "proof-region", "L3", 139, 139, "lpM:L3#deficit", ALL,
     "H_i<=I_i sqrt(1-e_i^2) gives the inequality in (13); the identity from constant |L| (DYN only)"),
    ("lpM:L3#ext-ftc", "citation", "L3", 139, 139, "lpM:ext-ftc", DYN, "fundamental theorem of calculus (candidate external)"),
    ("lpM:L4", "lemma", "L4", 141, 160, "lpM:L4", ALL,
     "attained, positive, continuous thresholds, (14); the radial-contact/Laskar-Petit/sharpness clauses of the "
     "statement (L143, L147) have no consumer (SPEC Q4); CHAR: the four threshold characterizations"),
    ("lpM:eq14", "display", "L4", 144, 146, "lpM:L4", ALL, "display (14): B_ij<I_j, B=min(B_cross,I_1)"),
    ("lpM:L4#feasible-compact", "proof-region", "L4", 149, 149, "lpM:L4#feasible-compact", ALL,
     "feasible set closed and nonempty, (0,1-alpha) feasible; minimum attained"),
    ("lpM:L4#contact-reduction", "proof-region", "L4", 149, 149, "lpM:L4#contact-reduction", ALL,
     "scaling to contact does not increase the objective"),
    ("lpM:L4#contact-param", "proof-region", "L4", 149, 153, "lpM:L4#contact-param", ALL,
     "contact parameterized over [0,1], display (15)"),
    ("lpM:eq15", "display", "L4", 150, 153, "lpM:L4#contact-param", ALL, "display (15)"),
    ("lpM:L4#continuity", "proof-region", "L4", 154, 156, "lpM:L4#continuity", ALL,
     "joint continuity and uniform continuity on compact neighborhoods give continuity of B_ij and B"),
    ("lpM:L4#positivity", "proof-region", "L4", 156, 156, "lpM:L4#positivity", ALL, "a zero minimum cannot give contact"),
    ("lpM:L4#competitor", "proof-region", "L4", 156, 156, "lpM:L4#competitor", ALL,
     "competitor (0,1-alpha): B_ij<=I_j D(1-alpha)<I_j, proving (14)"),
    ("lpM:L4#sharpness", "proof-region", "L4", 158, 158, None, NONE,
     "amendment N9: interior minimizers and geometric realization are not used downstream; outside every root "
     "closure (to be confirmed by the slice reviewer and the global reviewer)"),
    ("lpM:L4#lp-identification", "proof-region", "L4", 160, 160, None, NONE,
     "identification with the Laskar-Petit relative critical AMD; comparison only, no proof consumes it"),
    ("lpM:L4#cite-laskar-petit", "citation", "L4", 160, 160, None, NONE,
     "provenance (arXiv:1703.07125v2 §3-3.2); MAIN: no optimizer formula from that source is needed"),
    ("lpM:L4#ext-extreme-value", "citation", "L4", 149, 149, "lpM:ext-compact-min", ALL,
     "continuous function on a nonempty compact set attains its minimum (candidate external)"),
    ("lpM:L4#ext-unif-cont", "citation", "L4", 154, 154, "lpM:ext-heine-cantor", ALL,
     "uniform continuity on compact sets (candidate external)"),
    ("lpM:L5", "lemma", "L5", 162, 175, "lpM:L5", ALL,
     "the uniform strong barrier; LP0 = full L5 (FREEZE-PROPOSAL draft 7 §3.1); proposed anchor node of LP0"),
    ("lpM:L5#gap-positive", "proof-region", "L5", 166, 166, "lpM:L5#gap-positive", ALL,
     "a nonpositive gap would be feasible, then L3 (13) gives C>=B_{i,i+1}>=B"),
    ("lpM:L5#Km-compact", "proof-region", "L5", 166, 170, "lpM:L5#Km-compact", ALL,
     "K_m compact by L4 continuity; d_pair = minimum of the gaps; display at L167-L169"),
    ("lpM:L5#empty-case", "proof-region", "L5", 170, 170, "lpM:L5#empty-case", ALL, "K_m empty: assertions vacuous"),
    ("lpM:L5#perihelion", "proof-region", "L5", 170, 175, "lpM:L5#perihelion", ALL,
     "(16): sqrt(1-e^2)>=m/I_max and a(1-e)>=d_star; amendment N11 (define d_star first)"),
    ("lpM:eq16", "display", "L5", 171, 174, "lpM:L5#perihelion", ALL, "display (16)"),
    ("lpM:L5#bounds", "proof-region", "L5", 175, 175, "lpM:L5#bounds", ALL, "|q_i|<=2a_max, |p_i|<=nu_i sqrt(2/d_star) by (12)"),
    ("lpM:L5#pair-distances", "proof-region", "L5", 175, 175, "lpM:L5#pair-distances", ALL,
     "ordered radial intervals give |q_j-q_i|>=d_pair for all i<j"),
    ("lpM:L5#compact-physical", "proof-region", "L5", 175, 175, "lpM:L5#compact-physical", ALL,
     "energy <= -1/(2a_max); compact nonsingular physical set"),
    ("lpM:L5#projection", "proof-region", "L5", 175, 175, "lpM:L5#projection", ALL, "H_i>=m by L3"),
    ("lpM:L5#ext-compact-min", "citation", "L5", 170, 170, "lpM:ext-compact-min", ALL,
     "minimum of finitely many positive continuous gaps over a compact set (candidate external)"),
    ("lpM:L6", "lemma", "L6", 177, 189, "lpM:L6", DYN, "moving threshold (17) and continuation, both time directions"),
    ("lpM:eq17", "display", "L6", 184, 186, "lpM:L6#moving-threshold", DYN, "display (17)"),
    ("lpM:L6#shared-U", "proof-region", "L6", 189, 189, "lpM:L6#shared-U", DYN,
     "compact neighborhood U and modulus Omega_B -> 0; amendment N2 makes U the one set shared with L8 and L14"),
    ("lpM:L6#moving-threshold", "proof-region", "L6", 189, 189, "lpM:L6#moving-threshold", DYN, "(17) from (13) and the modulus"),
    ("lpM:L6#local-existence", "proof-region", "L6", 189, 189, "lpM:L6#local-existence", DYN,
     "bounded field and derivative on a neighborhood of the L5 set; Picard contraction; uniqueness"),
    ("lpM:L6#continuation", "proof-region", "L6", 189, 189, "lpM:L6#continuation", DYN,
     "limit at a finite endpoint in the compact set, local solution there, gluing; ellipticity cannot be lost"),
    ("lpM:L6#backward", "proof-region", "L6", 189, 189, "lpM:L6#backward", DYN, "negated field gives the backward assertion"),
    ("lpM:L6#ext-picard", "citation", "L6", 189, 189, "lpM:ext-picard", DYN, "Picard iteration / contraction mapping (candidate external)"),
    ("lpM:L6#ext-gronwall", "citation", "L6", 189, 189, "lpM:ext-gronwall", DYN,
     "uniqueness by iterating the integral inequality (candidate external)"),
    # §3
    ("lpM:h:s3", "heading", "s3", 191, 191, None, NONE, "section heading"),
    ("lpM:L7", "lemma", "L7", 193, 242, "lpM:L7", DYN, "regular planar canonical chart; reused by L17 and L18"),
    ("lpM:eq18", "display", "L7", 208, 210, "lpM:L7#kepler-equation", DYN, "display (18)"),
    ("lpM:eq19", "display", "L7", 214, 220, "lpM:L7#chart-formula", DYN, "display (19); reused by L17 (46)"),
    ("lpM:eq20", "display", "L7", 222, 225, "lpM:L7#rotated-form", DYN, "display (20)"),
    ("lpM:L7#kepler-equation", "proof-region", "L7", 202, 211, "lpM:L7#kepler-equation", DYN,
     "data a, s, b_e, k, l; unique analytic solution F of (18)"),
    ("lpM:L7#chart-formula", "proof-region", "L7", 213, 220, "lpM:L7#chart-formula", DYN, "the chart (19)"),
    ("lpM:L7#rotated-form", "proof-region", "L7", 221, 226, "lpM:L7#rotated-form", DYN,
     "(20); energy, angular momentum, eccentricity vector; extension to e=0"),
    ("lpM:L7#symplectic", "proof-region", "L7", 228, 238, "lpM:L7#symplectic", DYN,
     "p.dq computation, exact differential; amendment N1 (fixed in place at L238)"),
    ("lpM:L7#inverse", "proof-region", "L7", 240, 242, "lpM:L7#inverse", DYN, "analytic inverse on the region"),
    ("lpM:L7#ext-holomorphic-limit", "citation", "L7", 211, 211, "lpM:ext-holomorphic-limit", DYN,
     "uniform limits of holomorphic iterates are holomorphic (candidate external)"),
    ("lpM:L7#ext-identity", "citation", "L7", 238, 238, "lpM:ext-identity-theorem", DYN,
     "analytic identity extends from e>0 across e=0 (candidate external)"),
    ("lpM:L8", "lemma", "L8", 244, 271, "lpM:L8", DYN,
     "whole-sublevel planar analytic neighborhood; LP2 through L18#extension; LP3 through F1/F2"),
    ("lpM:eq21", "display", "L8", 247, 249, "lpM:L8", DYN, "display (21)"),
    ("lpM:eq22", "display", "L8", 251, 254, "lpM:L8", DYN, "display (22)"),
    ("lpM:L8#empty-case", "proof-region", "L8", 257, 257, "lpM:L8#empty-case", DYN, "L_delta empty: no initial state"),
    ("lpM:L8#shared-tube", "proof-region", "L8", 257, 257, "lpM:L8#shared-tube", DYN,
     "U and r_g with Omega_B(4r_g)<=delta/16; amendment N2"),
    ("lpM:L8#real-margin", "proof-region", "L8", 258, 261, "lpM:L8#real-margin", DYN,
     "sum Gamma_i <= B(I)-3delta/16; all phases safe by L5; e<=e_*<1"),
    ("lpM:L8#compact-real-set", "proof-region", "L8", 261, 261, "lpM:L8#compact-real-set", DYN,
     "compact set of (I^0,I,z,lambda); amendment N3 (projection K')"),
    ("lpM:L8#newton-extension", "proof-region", "L8", 263, 263, "lpM:L8#newton-extension", DYN,
     "uniform complex extension of the Kepler-equation solution; bilinear complexification"),
    ("lpM:L8#gluing", "proof-region", "L8", 265, 265, "lpM:L8#gluing", DYN,
     "gluing on complex balls, identity theorem, finite subcover, periodicity"),
    ("lpM:L8#denominators", "proof-region", "L8", 267, 271, "lpM:L8#denominators", DYN,
     "Re(w.w)>=d^2/2 for every star and pair denominator"),
    ("lpM:L8#widths", "proof-region", "L8", 271, 271, "lpM:L8#widths", DYN,
     "Cauchy bounds and the choice of r_*, s, b; amendment N3 (r_*<=4r_g)"),
    ("lpM:L8#exact-split", "proof-region", "L8", 271, 271, "lpM:L8#exact-split", DYN, "the product chart gives (4): exact split h + mu f"),
    ("lpM:L8#ext-identity", "citation", "L8", 265, 265, "lpM:ext-identity-theorem", DYN, "identity theorem (candidate external)"),
    ("lpM:L8#ext-compact-cover", "citation", "L8", 265, 265, "lpM:ext-compact-cover", DYN, "finite subcover (candidate external)"),
    ("lpM:L8#ext-cauchy", "citation", "L8", 271, 271, "lpM:ext-cauchy-estimates", DYN,
     "Cauchy's one-variable estimates; holomorphic square root with positive real part (candidate external)"),
    # §4
    ("lpM:h:s4", "heading", "s4", 273, 273, None, NONE, "section heading"),
    ("lpM:s4:intro", "claim", "s4", 275, 275, None, NONE, "overview; 'any fixed number of slow pairs' is part of the L9-L11 statements"),
    ("lpM:L9", "lemma", "L9", 277, 304, "lpM:L9", R12, "Fourier, Cauchy and commutator estimates"),
    ("lpM:L9#domains", "definition", "L9", 279, 284, "lpM:L9#domains", R12, "domains D_rho (23)"),
    ("lpM:eq23", "display", "L9", 280, 284, "lpM:L9#domains", R12, "display (23)"),
    ("lpM:L9#norm", "definition", "L9", 285, 291, "lpM:L9#norm", R12, "scaled components and the weighted norm (24)"),
    ("lpM:eq24", "display", "L9", 287, 291, "lpM:L9#norm", R12, "display (24)"),
    ("lpM:eq25", "display", "L9", 293, 295, "lpM:L9#commutator", R12, "display (25)"),
    ("lpM:L9#sup-to-fourier", "proof-region", "L9", 298, 299, "lpM:L9#sup-to-fourier", R12, "contour shift; sup bound to Fourier norm"),
    ("lpM:L9#banach-algebra", "proof-region", "L9", 300, 300, "lpM:L9#banach-algebra", R12, "convolution estimate"),
    ("lpM:L9#cauchy-derivative", "proof-region", "L9", 302, 303, "lpM:L9#cauchy-derivative", R12, "Cauchy 1/sigma; angle factor 1/(e sigma)"),
    ("lpM:L9#commutator", "proof-region", "L9", 304, 304, "lpM:L9#commutator", R12, "(25)"),
    ("lpM:L9#projections-tail", "proof-region", "L9", 304, 304, "lpM:L9#projections-tail", R12, "projections and Fourier tail"),
    ("lpM:L9#ext-fourier-contour", "citation", "L9", 298, 298, "lpM:ext-fourier-contour", R12,
     "Fourier coefficients of periodic holomorphic functions and contour shift (candidate external)"),
    ("lpM:L9#ext-cauchy", "citation", "L9", 302, 302, "lpM:ext-cauchy-estimates", R12, "Cauchy's formula (candidate external)"),
    ("lpM:L10", "lemma", "L10", 306, 349, "lpM:L10", R12, "cohomology and a controlled Lie step"),
    ("lpM:eq26", "display", "L10", 309, 314, "lpM:L10#homological", R12, "display (26)"),
    ("lpM:eq27", "display", "L10", 316, 320, "lpM:L10#remainder", R12, "display (27)"),
    ("lpM:eq28", "display", "L10", 331, 335, "lpM:L10#lie-series-bound", R12, "display (28)"),
    ("lpM:eq29", "display", "L10", 343, 346, "lpM:L10#remainder", R12, "display (29)"),
    ("lpM:L10#homological", "proof-region", "L10", 323, 328, "lpM:L10#homological", R12, "chi_k = f_k/(i k.omega); (26); reality"),
    ("lpM:L10#lie-series-bound", "proof-region", "L10", 330, 336, "lpM:L10#lie-series-bound", R12, "(28) and j! >= (j/e)^j"),
    ("lpM:L10#lie-flow-identification", "proof-region", "L10", 336, 338, "lpM:L10#lie-flow-identification", R12,
     "Lie series equals pullback by the flow; scalar series; amendment N5 (sketched): candidate SOURCE_GAP"),
    ("lpM:L10#flow-existence", "proof-region", "L10", 340, 340, "lpM:L10#flow-existence", R12,
     "flow existence, holomorphy, inverse, symplecticity; amendment N5 (sketched): candidate SOURCE_GAP"),
    ("lpM:L10#remainder", "proof-region", "L10", 342, 349, "lpM:L10#remainder", R12,
     "(29), B_D = 16eD; c_D implicit (amendment N5)"),
    ("lpM:L10#ext-picard", "citation", "L10", 340, 340, "lpM:ext-picard", R12, "contraction on continuous paths (candidate external)"),
    ("lpM:L11", "lemma", "L11", 351, 379, "lpM:L11", R12, "exponential normal form on the full slow set"),
    ("lpM:eq30", "display", "L11", 355, 357, "lpM:L11", R12, "display (30)"),
    ("lpM:eq31", "display", "L11", 359, 362, "lpM:L11", R12, "display (31)"),
    ("lpM:L11#step-estimate", "proof-region", "L11", 365, 370, "lpM:L11#step-estimate", R12, "one step with loss 1/N"),
    ("lpM:L11#qD-choice", "proof-region", "L11", 371, 374, "lpM:L11#qD-choice", R12, "q_D = min(c_D, 1/(6B_D), 1/64)"),
    ("lpM:L11#induction", "proof-region", "L11", 375, 375, "lpM:L11#induction", R12, "E_{j+1}<=E_j/2, |X_g|<=2 eps"),
    ("lpM:L11#composition", "proof-region", "L11", 375, 379, "lpM:L11#composition", R12, "composition, displacement <= 1/32, domains"),
    ("lpM:L11#inverse", "proof-region", "L11", 379, 379, "lpM:L11#inverse", R12, "inverse by negative-time flows on D_{3/2}"),
    ("lpM:L11#derivative-bounds", "proof-region", "L11", 379, 379, "lpM:L11#derivative-bounds", R12, "Cauchy bounds on D Phi"),
    ("lpM:L12", "lemma", "L12", 381, 427, "lpM:L12", R12,
     "scaling r = sqrt(mu), N, eps; drift (34); (35) unused (amendment N4); conditional on the L8/L18 domain statement"),
    ("lpM:eq32", "display", "L12", 384, 389, "lpM:L12", R12, "display (32)"),
    ("lpM:eq33", "display", "L12", 391, 395, "lpM:L12", R12, "display (33)"),
    ("lpM:eq34", "display", "L12", 397, 399, "lpM:L12#drift", R12, "display (34)"),
    ("lpM:eq35", "display", "L12", 401, 403, "lpM:L12#finite-divisors", NONE,
     "display (35): amendment N4, a remark with no consumer (SPEC Q5)"),
    ("lpM:L12#perturbation-size", "proof-region", "L12", 405, 405, "lpM:L12#perturbation-size", R12, "|X_{H-h_0}|_3 <= M_1 sqrt(mu)"),
    ("lpM:L12#kappa-choice", "proof-region", "L12", 407, 412, "lpM:L12#kappa-choice", R12, "(36) implies (30)"),
    ("lpM:eq36", "display", "L12", 408, 411, "lpM:L12#kappa-choice", R12, "display (36)"),
    ("lpM:L12#time-choice", "proof-region", "L12", 414, 414, "lpM:L12#time-choice", R12, "c = kappa log2 / 4, T_mu <= 2^{N/2}"),
    ("lpM:L12#drift", "proof-region", "L12", 414, 420, "lpM:L12#drift", R12, "transformed solutions; (34) both time signs"),
    ("lpM:L12#finite-divisors", "proof-region", "L12", 420, 425, "lpM:L12#finite-divisors", NONE,
     "(35); amendment N4: not a formal dependency; extractor decides node-without-consumer vs exclusion (SPEC Q5)"),
    ("lpM:L12#remark", "claim", "L12", 427, 427, None, NONE, "commentary on what is inverted; no new obligation"),
    ("lpM:L13", "lemma", "L13", 429, 464, "lpM:L13", R13,
     "checked specialization of the Track N finite-cutoff theorem; Lean route of LP1/LP2 (N7)"),
    ("lpM:L13#interface", "proof-region", "L13", 433, 433, "lpM:L13#interface", R13,
     "interface check against named repository declarations; consumed through IMPORTED graph-N nodes, never by "
     "reading implementation Lean"),
    ("lpM:L13#cite-repository", "citation", "L13", 433, 433, "N:bpN:p11:nonresonant", R13,
     "KAM.Nekhoroshev.nonresonant / ExtNFHyp / nf / preimage at f5625f19: candidate IMPORT N:bpN:p11:nonresonant "
     "(plus N:bpN:p11:s-nf#data if the NF hypothesis package is consumed separately); confirm in LP-imports"),
    ("lpM:L13#period-one", "proof-region", "L13", 435, 440, "lpM:L13#period-one", R13,
     "theta = lambda/(2pi), rescaled slow variables, weighted bracket c_s, sign conventions"),
    ("lpM:L13#numeric-hypotheses", "proof-region", "L13", 442, 457, "lpM:L13#numeric-hypotheses", R13,
     "(37) and the choices of kappa_1, D_0; amendment N6 (widths)"),
    ("lpM:eq37", "display", "L13", 448, 452, "lpM:L13#numeric-hypotheses", R13, "display (37)"),
    ("lpM:L13#structural-hypotheses", "proof-region", "L13", 458, 458, "lpM:L13#structural-hypotheses", R13,
     "holomorphy, reality, periodicity, module {0}, slow tube width, from L8"),
    ("lpM:L13#conclusion", "proof-region", "L13", 460, 464, "lpM:L13#conclusion", R13,
     "(38): drift <= r/2 through exp(c_1 mu^{-a}) under stopped membership; slow displacement (nnf_disp_radius)"),
    ("lpM:eq38", "display", "L13", 461, 463, "lpM:L13#conclusion", R13, "display (38)"),
    # §5
    ("lpM:h:s5", "heading", "s5", 466, 466, None, NONE, "section heading"),
    ("lpM:L14", "lemma", "L14", 468, 500, "lpM:L14", DYN,
     "first exit on the whole ball; conditional on chart premises discharged by T15/T19; LP3 reuses it with the "
     "partial-convex drift supplier; routes route-L12/route-L13 (N7)"),
    ("lpM:L14#centers", "proof-region", "L14", 472, 472, "lpM:L14#centers", DYN, "admissible centres lie in L_delta"),
    ("lpM:L14#choices", "proof-region", "L14", 472, 476, "lpM:L14#choices", DYN, "U, mu_0 and (39); amendment N2"),
    ("lpM:eq39", "display", "L14", 473, 475, "lpM:L14#choices", DYN, "display (39)"),
    ("lpM:L14#stopped-membership", "proof-region", "L14", 478, 487, "lpM:L14#stopped-membership", DYN,
     "stopped interval (40), whole-ball membership in D_1"),
    ("lpM:eq40", "display", "L14", 479, 481, "lpM:L14#stopped-membership", DYN, "display (40)"),
    ("lpM:L14#improvement", "proof-region", "L14", 487, 487, "lpM:L14#improvement", DYN,
     "action bound improved (r/4 via L12, r/2 via L13), AMD margin to 3delta/4 by (13), (17), (39)"),
    ("lpM:L14#route-L12", "proof-region", "L14", 487, 487, "lpM:L14#route-L12", R12, "route node: drift supplier L12 (N7)"),
    ("lpM:L14#route-L13", "proof-region", "L14", 500, 500, "lpM:L14#route-L13", R13,
     "route node: drift supplier L13 with r = D_0 sqrt(mu) and improvement r/2 (N6, N7)"),
    ("lpM:L14#no-exit", "proof-region", "L14", 489, 489, "lpM:L14#no-exit", DYN,
     "finite forward end contradicts L5/L6 continuation and the persisting improved bounds"),
    ("lpM:L14#backward", "proof-region", "L14", 489, 489, "lpM:L14#backward", DYN, "backward time by the same argument"),
    ("lpM:L14#separation", "proof-region", "L14", 491, 495, "lpM:L14#separation", DYN, "L5 with m = delta/2; d_star (41)"),
    ("lpM:eq41", "display", "L14", 492, 494, "lpM:L14#separation", DYN, "display (41)"),
    ("lpM:L14#axis-drift", "proof-region", "L14", 495, 500, "lpM:L14#axis-drift", DYN, "action-to-axis estimate; A_I, A_a, T_0"),
    ("lpM:T15", "theorem", "T15", 502, 506, "lpM:T15", PL,
     "planar theorem; proposed anchor node of LP1; LP1-H is its tau = n-1/2 corollary; LP3-1 reuses its reduction steps"),
    ("lpM:T15#orientation", "proof-region", "T15", 506, 506, "lpM:T15#orientation", PL,
     "L3 sign, reflection of the plane, invariance of H and constants (N8, OD-1)"),
    ("lpM:T15#chart-cover", "proof-region", "T15", 506, 506, "lpM:T15#chart-cover", PL,
     "product of L7 charts covers; C = |z|^2/2 in the prograde region; reference orientation fixed by L3"),
    ("lpM:T15#apply-L14", "proof-region", "T15", 506, 506, "lpM:T15#apply-L14", "LP1,LP1-H",
     "discharges L14's chart premises with L7/L8 (m = n) and the drift supplier (routes, N7)"),
    ("lpM:T15#reconstruction", "proof-region", "T15", 506, 506, "lpM:T15#reconstruction", PL, "L1 reconstructs the Newtonian motion"),
    ("lpM:T15#osculating", "proof-region", "T15", 506, 506, "lpM:T15#osculating", PL, "L16 osculating conclusion"),
    ("lpM:L16", "lemma", "L16", 508, 529, "lpM:L16", DYN,
     "actual-velocity osculating ellipses (43); CHAR: osculating axis/peri/apo/ecc/energy characterizations"),
    ("lpM:L16:defs", "definition", "L16", 510, 519, "lpM:L16:defs", DYN,
     "V_i, k_i, E^osc, a^osc, e^osc vector, e^osc (42); frozen osculating definitions bind here after freeze"),
    ("lpM:eq42", "display", "L16", 511, 519, "lpM:L16:defs", DYN, "display (42)"),
    ("lpM:eq43", "display", "L16", 521, 524, "lpM:L16", DYN, "display (43)"),
    ("lpM:L16#element-error", "proof-region", "L16", 527, 527, "lpM:L16#element-error", DYN,
     "|V-v|<=nP mu, |k-1|<=mu, energy and eccentricity-vector errors A_0 mu"),
    ("lpM:L16#elliptic", "proof-region", "L16", 527, 527, "lpM:L16#elliptic", DYN, "E^osc <= -1/(4a_max), axis estimate, e^osc < 1"),
    ("lpM:L16#endpoint-estimate", "proof-region", "L16", 527, 527, "lpM:L16#endpoint-estimate", DYN, "second estimate of (43)"),
    ("lpM:L16#tangent-ellipse", "proof-region", "L16", 527, 527, "lpM:L16#tangent-ellipse", DYN,
     "two-body ellipse through q_i tangent to V_i; L2 with parameter k_i"),
    ("lpM:L16#mu0-choice", "proof-region", "L16", 528, 528, "lpM:L16#mu0-choice", DYN, "A_osc mu_0 <= d_star/2, 2A_osc mu_0 <= d_pair/2 (N10, OD-9)"),
    ("lpM:L16#half-gaps", "proof-region", "L16", 529, 529, "lpM:L16#half-gaps", DYN, "osculating half gaps"),
    ("lpM:L16#convention-remark", "claim", "L16", 529, 529, None, NONE, "gravitational-parameter-one convention is a separately named variant; not used"),
    # §6
    ("lpM:h:s6", "heading", "s6", 531, 531, None, NONE, "section heading"),
    ("lpM:L17", "lemma", "L17", 533, 578, "lpM:L17", SP, "regular spatial Poincare chart; fixed-plane deficit identity"),
    ("lpM:eq44", "display", "L17", 536, 540, "lpM:L17", SP, "display (44)"),
    ("lpM:eq45", "display", "L17", 542, 544, "lpM:L17", SP, "display (45)"),
    ("lpM:L17#deficit-identity", "claim", "L17", 545, 546, "lpM:L17#deficit-identity", SP, "C_{e3} = |z|^2/2; proved by summing (45) at L578"),
    ("lpM:L17#rotation", "proof-region", "L17", 548, 558, "lpM:L17#rotation", SP, "rotation R (46), orthogonality, q x p = G R e_3"),
    ("lpM:eq46", "display", "L17", 549, 553, "lpM:L17#rotation", SP, "display (46)"),
    ("lpM:L17#symplectic", "proof-region", "L17", 560, 571, "lpM:L17#symplectic", SP, "rotation terms G dg + H dh_n; density extension"),
    ("lpM:L17#inverse", "proof-region", "L17", 573, 578, "lpM:L17#inverse", SP, "inverse, onto the prograde region"),
    ("lpM:L17#ext-identity", "citation", "L17", 571, 571, "lpM:ext-identity-theorem", SP, "dense set plus analyticity (candidate external)"),
    ("lpM:L18", "lemma", "L18", 580, 597, "lpM:L18", SP, "spatial whole-sublevel domain"),
    ("lpM:eq47", "display", "L18", 583, 585, "lpM:L18", SP, "display (47)"),
    ("lpM:L18#margins", "proof-region", "L18", 588, 593, "lpM:L18#margins", SP, "G_i, H_i >= 3delta/16, c_i^2 > 1/2"),
    ("lpM:L18#whole-ball-safe", "proof-region", "L18", 593, 593, "lpM:L18#whole-ball-safe", SP, "fixed-plane deficit bounds eccentricity AMD; L5 on the whole ball"),
    ("lpM:L18#extension", "proof-region", "L18", 595, 595, "lpM:L18#extension", SP, "L8's extension argument verbatim in 6n coordinates"),
    ("lpM:L18#rotation-invariance", "proof-region", "L18", 595, 595, "lpM:L18#rotation-invariance", SP, "rotation invariance of the bounds"),
    ("lpM:L18#alignment", "proof-region", "L18", 597, 597, "lpM:L18#alignment", SP, "one fixed rotation per solution, C_{e3} = C, L17 covers"),
    ("lpM:T19", "theorem", "T19", 599, 603, "lpM:T19", SP,
     "spatial theorem; proposed anchor node of LP2; LP2-H is its tau = n-1/2 corollary; LP3-2 reuses its reduction steps"),
    ("lpM:T19#align", "proof-region", "T19", 603, 603, "lpM:T19#align", SP, "L18 alignment; ball (47); L17 symplectic"),
    ("lpM:T19#apply-L14", "proof-region", "T19", 603, 603, "lpM:T19#apply-L14", "LP2,LP2-H",
     "m = 2n slow pairs; L9-L12 dimension constants; discharges L14 (routes, N7)"),
    ("lpM:T19#osculating", "proof-region", "T19", 603, 603, "lpM:T19#osculating", SP, "L16 in dimension three"),
    ("lpM:T19#reconstruction", "proof-region", "T19", 603, 603, "lpM:T19#reconstruction", SP, "L1"),
    ("lpM:T19#unrotate", "proof-region", "T19", 603, 603, "lpM:T19#unrotate", SP, "inverse fixed rotation leaves the inequalities unchanged"),
    # §7-§8
    ("lpM:h:s7", "heading", "s7", 605, 605, None, NONE, "section heading"),
    ("lpM:s7#intro", "claim", "s7", 607, 607, None, NONE, "literature-check statement; no obligation"),
    ("lpM:s7#cite-lp-aa", "citation", "s7", 611, 611, None, NONE, "Laskar-Petit A&A 2017: interpretation; geometry proved in L2-L5"),
    ("lpM:s7#cite-lp-arxiv", "citation", "s7", 612, 612, None, NONE, "Laskar-Petit arXiv v2 page pins: provenance"),
    ("lpM:s7#cite-bmm", "citation", "s7", 613, 613, None, NONE, "Barbieri-Marco-Massetti Lemma B.1: not used as a supplier"),
    ("lpM:s7#cite-pinzari-liu", "citation", "s7", 614, 614, None, NONE, "Pinzari-Liu Prop. 3.2: comparison only"),
    ("lpM:s7#repository-baseline", "claim", "s7", 616, 616, None, NONE,
     "comparison with planetaryExponentialSafety and partialConvex_nekhoroshev; LP3's use of the latter is sourced "
     "in LP3-PLAN, not here"),
    ("lpM:s7#research-notes", "claim", "s7", 618, 618, None, NONE, "provenance of research notes; 'not used as an analytic axiom'"),
    ("lpM:s7#self-refutation", "proof-region", "s7", 620, 644, None, NONE,
     "self-review table; every resolution points to a lemma; reviewers confirm that no row adds an obligation "
     "absent from L1-T19"),
    ("lpM:h:s8", "heading", "s8", 646, 646, None, NONE, "section heading"),
    ("lpM:s8#status", "claim", "s8", 648, 661, None, NONE, "status table"),
    ("lpM:s8#input-hashes", "citation", "s8", 663, 678, None, NONE, "input hashes and process record"),
]

A = [
    ("lpA:precedence", "heading", "header", 1, 6, None, NONE,
     "the precedence rule (N1 in place; N2-N12 override the cited MAIN lines); recorded in SPEC §Corpus and applied "
     "to every node"),
    ("lpA:N1", "claim", "N1", 10, 10, "lpM:L7#symplectic", DYN, "typo fixed in place at MAIN L238; no locator change"),
    ("lpA:N2", "claim", "N2", 11, 11, "lpM:L6#shared-U,lpM:L8#shared-tube,lpM:L14#choices", DYN,
     "one shared compact U with the 4r_g tube, its modulus in (17), L8 and (39); r <= r_g"),
    ("lpA:N3", "claim", "N3", 12, 12, "lpM:L8#widths", DYN, "r_* <= 4r_g stated; sup-distance tube about K'"),
    ("lpA:N4", "claim", "N4", 13, 13, "lpM:L12#finite-divisors", NONE, "(35) is a remark, not a formal dependency"),
    ("lpA:N5", "claim", "N5", 14, 14, "lpM:L10#lie-flow-identification,lpM:L10#flow-existence,lpM:L10#remainder", R12,
     "sketched flow existence, Lie-series identification and c_D: candidate SOURCE_GAP steps on route-L12"),
    ("lpA:N6", "claim", "N6", 15, 15, "lpM:L13#numeric-hypotheses,lpM:L14#route-L13", R13,
     "widths of the L13 specialization; radius D_0 sqrt(mu), improvement r/2"),
    ("lpA:N7", "claim", "N7", 16, 16, "lpM:L14#route-L12,lpM:L14#route-L13", DIO,
     "L12 and L13 are alternative suppliers of the stopped drift: route nodes, never a conjunction"),
    ("lpA:N8", "claim", "N8", 17, 17, "lpM:s1:elements,lpM:T15#orientation", ALL,
     "AMD convention; ruled OD-1 (D59): C = sum Lambda - |L|, no prograde premise"),
    ("lpA:N9", "claim", "N9", 18, 18, None, NONE, "confirms the exclusion of lpM:L4#sharpness (MAIN L158)"),
    ("lpA:N10", "claim", "N10", 19, 19, "lpM:L16#mu0-choice", DYN, "final mu_0 constraints recorded in the constant list (OD-9)"),
    ("lpA:N11", "claim", "N11", 20, 20, "lpM:L5#perihelion", ALL, "define d_star before bounding |p_i|"),
    ("lpA:N12", "claim", "N12", 21, 21, None, NONE, "engineering note on the roadmap's Lean typing; no MAIN line, no obligation"),
    ("lpA:order", "claim", "order", 23, 26, None, NONE, "recommended formalization order; administrative"),
]

L3 = "LP3-1,LP3-2"
P3 = "LP3-1"
S3 = "LP3-2"
Q = [
    ("lp3:h:status", "heading", "status", 1, 16, None, NONE, "status, source and label legend; administrative"),
    ("lp3:review-note", "claim", "review-note", 20, 25, "lp3:s3#assembly", L3,
     "review-1 notes; C5 fixes the headline mu_0 as a minimum with the LP1/LP2 osculating and separation limits"),
    ("lp3:s0", "claim", "s0", 27, 59, None, NONE, "summary of §2-§5"),
    ("lp3:s1.1#exponents", "definition", "s1.1", 63, 83, "lp3:s1.1#exponents", L3,
     "a_n, b_n: already-frozen track-P/N exponent definitions; bind after the draft-8 freeze"),
    ("lp3:LP3-1", "theorem", "s1.2", 85, 126, "lp3:LP3-1", P3, "planar target; proposed anchor node of LP3-1 (draft 8)"),
    ("lp3:LP3-2", "theorem", "s1.3", 128, 134, "lp3:LP3-2", S3, "spatial target; proposed anchor node of LP3-2 (draft 8)"),
    ("lp3:s1.4", "claim", "s1.4", 136, 150, None, NONE, "comparison table; no obligation"),
    ("lp3:s2.1", "citation", "s2.1", 154, 175, "N:bpN:p0:partial", L3,
     "the sealed partialConvex_nekhoroshev read exactly: candidate IMPORT N:bpN:p0:partial (and the N definition "
     "anchors it uses, if a step consumes them separately)"),
    ("lp3:s2.2#F1", "proof-region", "F1", 181, 183, "lp3:s2.2#F1", L3, "shared tube r_g, U, Omega_B(4r_g) <= delta/16 (MAIN L8, N2)"),
    ("lp3:s2.2#F2", "proof-region", "F2", 184, 187, "lp3:s2.2#F2", L3, "uniform holomorphic extension fc, bound M, B_0 (MAIN L8)"),
    ("lp3:s2.2#F3", "proof-region", "F3", 188, 189, "lp3:s2.2#F3", L3, "widths rs, s, b, eta, rho"),
    ("lp3:s2.2#F4", "proof-region", "F4", 190, 193, "lp3:s2.2#F4", L3, "finite cover of L_delta by centres in L_delta; empty case"),
    ("lp3:s2.2#F5", "proof-region", "F5", 194, 197, "lp3:s2.2#F5", L3, "cells G_j, G'_j, A_j, D_j"),
    ("lp3:s2.2#F6", "proof-region", "F6", 198, 199, "lp3:s2.2#F6", L3, "Kepler constants a_min, I_max, g, m, Mc"),
    ("lp3:s2.2#F7", "proof-region", "F7", 200, 201, "lp3:s2.2#F7", L3, "slow erosion gap eps_D > 0"),
    ("lp3:s2.3#collar", "proof-region", "s2.3", 207, 207, "lp3:s2.3#collar", L3, "collar premise"),
    ("lp3:s2.3#kepler-data", "proof-region", "s2.3", 208, 214, "lp3:s2.3#kepler-data", L3,
     "holomorphy, C^2, reality, Hessian bound on the cell; adapted from track P (candidate IMPORT P:bpP:p14:h-data)"),
    ("lp3:s2.3#definiteness", "proof-region", "s2.3", 215, 218, "lp3:s2.3#definiteness", L3, "HasDefiniteFastPart with sigma = -1; negation for -h"),
    ("lp3:s2.3#perturbation", "proof-region", "s2.3", 219, 235, "lp3:s2.3#perturbation", L3,
     "P = fc/B_0, cell containment, the four perturbation clauses (candidate IMPORT P:bpP:p14:perturbation)"),
    ("lp3:s2.3#hamiltonian-identity", "proof-region", "s2.3", 236, 246, "lp3:s2.3#hamiltonian-identity", L3,
     "N-Hamiltonian equals the chart Hamiltonian on the open set V_j; equal fields"),
    ("lp3:s2.3#thresholds", "proof-region", "s2.3", 248, 255, "lp3:s2.3#thresholds", L3, "nu_0, mu_0, r(mu), T(mu), c, T_0 over the finite cover"),
    ("lp3:s2.3#time-check", "proof-region", "s2.3", 257, 257, "lp3:s2.3#time-check", L3, "T(mu) <= the frozen horizon"),
    ("lp3:s2.4", "lemma", "s2.4", 259, 265, "lp3:s2.4", P3, "the drift supplier in the exact stopped (hstop) shape, planar"),
    ("lp3:s2.4#lift", "proof-region", "s2.4", 269, 274, "lp3:s2.4#lift", P3, "chart lift of the stopped orbit (MAIN L7/L14 dictionary)"),
    ("lp3:s2.4#cell", "proof-region", "s2.4", 275, 275, "lp3:s2.4#cell", P3, "choice of the cell of I^0"),
    ("lp3:s2.4#fast-premises", "proof-region", "s2.4", 276, 277, "lp3:s2.4#fast-premises", P3, "innerCore and G_j membership"),
    ("lp3:s2.4#sharp-slow-bound", "proof-region", "s2.4", 278, 287, "lp3:s2.4#sharp-slow-bound", P3,
     "C < B(c_j) - 3delta/8 (the curvature step; uses the L6 modulus twice)"),
    ("lp3:s2.4#slow-premise", "proof-region", "s2.4", 288, 289, "lp3:s2.4#slow-premise", P3, "slow erosion"),
    ("lp3:s2.4#solution-premise", "proof-region", "s2.4", 290, 293, "lp3:s2.4#solution-premise", P3, "the lift solves the N-field on [0,t]"),
    ("lp3:s2.4#forward", "proof-region", "s2.4", 294, 295, "lp3:s2.4#forward", P3, "apply the imported theorem: drift <= r/2"),
    ("lp3:s2.4#backward", "proof-region", "s2.4", 296, 300, "lp3:s2.4#backward", P3, "reversed curve with (-h, -P)"),
    ("lp3:s2.4#uniformity", "proof-region", "s2.4", 302, 303, "lp3:s2.4#uniformity", P3, "constants depend only on (n, nu, A, delta)"),
    ("lp3:s2.5", "proof-region", "s2.5", 305, 328, "lp3:s2.5", S3,
     "spatial version (k = 2n): slow ball, extension, chart Hamiltonian, lift, erosion constant; MAIN L17/L18"),
    ("lp3:s3#sublevel", "proof-region", "s3", 333, 351, "lp3:s3#sublevel", L3,
     "no AMDBox; why D may be the sharp ball; ordered levels with fixed gaps (MAIN L5, L8)"),
    ("lp3:s3#first-exit", "proof-region", "s3", 352, 362, "lp3:s3#first-exit", L3,
     "application of MAIN L14 with r = (B_0 mu)^{b_n} and hstop from §2.4"),
    ("lp3:s3#assembly", "proof-region", "s3", 363, 370, "lp3:s3#assembly", L3,
     "assembly as in T15/T19 with the drift supplier swapped; A_Lambda = B_0^{b_n}/2"),
    ("lp3:s4", "claim", "s4", 373, 422, None, NONE, "provider chain and import policy (D58, OD-13); governance"),
    ("lp3:s5", "claim", "s5", 424, 462, None, NONE, "Lean package list; planning"),
    ("lp3:s6", "claim", "s6", 464, 489, None, NONE, "risk register; its mathematical content is in §2-§3"),
    ("lp3:s7", "claim", "s7", 491, 506, None, NONE, "sketch remarks and errata candidates (A4); errata ledger, not graph"),
]


def render(items, path, header):
    out = [header, ""]
    per_slice = {}
    for item, kind, anchor, a, b, disp, anchors, note in items:
        sl = slice_of(path, a)
        per_slice[sl] = per_slice.get(sl, 0) + 1
        out += [
            f"ITEM: {item}",
            f"KIND: {kind}",
            f"SOURCE: {path}#{anchor}@L{a}-L{b}",
            f"DISPOSITION: NODE {disp}" if disp else "DISPOSITION: EXCLUDED",
            f"REASON: ANCHORS: {anchors}; SLICE: {sl}; {note}",
            "COVERAGE_STATUS: PROPOSED",
            f"EXTRACTOR: {TAG}",
            "REVIEWER: -",
            "",
        ]
    return "\n".join(out), per_slice


def main():
    (OUT / "draft").mkdir(parents=True, exist_ok=True)
    (OUT / "packets").mkdir(parents=True, exist_ok=True)
    common = ("Pre-anchor coverage inventory (skill build-proof-dependency-graph, Phase 2), written before the LP "
              "anchors are frozen. Every disposition is PROPOSED; node IDs are planned IDs (SPEC.md, node "
              "scheme). The ANCHORS list in REASON names the anchors whose proof the item supports. Regenerate "
              "only before extraction starts; afterwards the slice packets are the source of truth.")
    files = [
        ("coverage-main.md", M, MAIN, "MAIN.md (sha256 68e9167f...48c1b, 679 lines)"),
        ("coverage-amendments.md", A, AMD, "AMENDMENTS.md (sha256 c887d1e2...51881, 26 lines)"),
        ("coverage-lp3plan.md", Q, LP3,
         "LP3-PLAN.md (sha256 1b58b704...6ba, 506 lines; CANDIDATE corpus, pending SPEC Q1 and the draft-8 freeze)"),
    ]
    totals = {}
    stats = {}
    for name, items, path, desc in files:
        header = (f"# Track LP coverage inventory (draft): {desc}\n\n"
                  f"CORPUS: docs/graph/LP/CORPUS.sha256 (MAIN.md, AMENDMENTS.md); LP3-PLAN.md candidate (SPEC Q1)\n\n"
                  f"{common}\n")
        text, per = render(items, path, header)
        (OUT / "draft" / name).write_text(text)
        for k, v in per.items():
            totals[k] = totals.get(k, 0) + v
        n_ex = sum(1 for it in items if it[5] is None)
        kinds = {}
        for it in items:
            kinds[it[1]] = kinds.get(it[1], 0) + 1
        stats[name] = {"items": len(items), "excluded": n_ex, "mapped": len(items) - n_ex, "kinds": kinds}
    # planned node estimates per slice (from the distinct planned node IDs whose item starts in the slice)
    nodes = {}
    home = {}
    for items, path in ((M, MAIN), (A, AMD), (Q, LP3)):
        for item, kind, anchor, a, b, disp, anchors, note in items:
            home.setdefault(item, slice_of(path, a))
    seen = set()
    for items, path in ((M, MAIN), (A, AMD), (Q, LP3)):
        for item, kind, anchor, a, b, disp, anchors, note in items:
            if not disp:
                continue
            for nid in disp.split(","):
                if nid.startswith(("N:", "P:")) or nid.startswith("lpM:ext-") or nid in seen:
                    continue
                seen.add(nid)
                sl = home.get(nid, slice_of(path, a))
                nodes[sl] = nodes.get(sl, 0) + 1
    exts = sorted({d for it in M for d in (it[5] or "").split(",") if d.startswith("lpM:ext-")})
    imports = sorted({d for items in (M, Q) for it in items for d in (it[5] or "").split(",") if d.startswith(("N:", "P:"))}
                     | {"N:bpN:p11:s-nf#data", "P:bpP:p14:h-data", "P:bpP:p14:perturbation"})
    slices = {}
    spec = [("LP-adef-pl", "anchors", [1, 1000000000], 56,
             "frozen definition anchors: draft-7 new definitions 1-37 (planar, dimension-free) plus reused frozen "
             "definitions (19 direct, 21 in closure); estimate, re-read from the manifest at freeze"),
            ("LP-adef-sp", "anchors", [1, 1000000000], 51,
             "frozen definition anchors: draft-7 new definitions 38-88 (spatial); estimate"),
            ("LP-athm", "anchors", [1, 1000000000], 41,
             "frozen theorem anchors: LP0, LP1, LP1-H, LP2, LP2-H (+ LP3-1, LP3-2 if draft 8 is frozen) and the 34 "
             "characterization theorems; estimate")]
    for name, a, b in MAIN_SLICES:
        slices[name] = {"part": "MAIN", "lines": [a, b], "nodes": nodes.get(name, 0), "coverage": totals.get(name, 0)}
    slices["LP-amend"] = {"part": "AMENDMENTS", "lines": [1, 26], "nodes": 0, "coverage": totals.get("LP-amend", 0)}
    slices["LP-imports"] = {"part": "imports", "lines": [1, 1000000000], "nodes": len(imports), "coverage": 0}
    for name, a, b in LP3_SLICES:
        slices[name] = {"part": "LP3-PLAN", "lines": [a, b], "nodes": nodes.get(name, 0), "coverage": totals.get(name, 0)}
    out = {"_note": ("PLANNED slices (pre-anchor). nodes/coverage are estimates from docs/graph/LP/draft/coverage-*.md "
                     "(planned node IDs, excluding externals and imports); LP-adef-*/LP-athm sizes are "
                     "draft-7 estimates, re-read from the frozen manifest after freeze. 'part' names the source file stem; LP3 slices are conditional "
                     "on the draft-8 freeze and SPEC Q1.")}
    for name, part, lines, est, what in spec:
        out[name] = {"part": part, "lines": lines, "nodes": est, "coverage": est, "what": what}
    out.update(slices)
    out["LP-ext"] = {"part": "externals", "lines": [1, 1000000000], "nodes": len(exts), "coverage": 0,
                     "what": "writer-owned candidate external leaves: " + ", ".join(exts)}
    out["LP-imports"]["what"] = "writer-owned candidate imported nodes: " + ", ".join(imports)
    (OUT / "packets" / "slices.json").write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
    print(json.dumps({"stats": stats, "slices": {k: (v["nodes"], v["coverage"]) for k, v in slices.items()},
                      "exts": exts, "imports": imports}, indent=1))


main()
