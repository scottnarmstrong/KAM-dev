# LP-W4C independent package audit 1

Audit date: 2026-11-01. Scope: ordinary non-frozen package statements, not a frozen-anchor seal.
Reviewed HEAD `209cb9765cb09867b2fa5d082adb253aefca2d68`; `inp` is
`51be245691bc21c0cf789b0c5b6bb9a4d3a7972a`; `inp-lp` is
`ab2f9993b260c7447f225a3dd9363bc42dd56c2f`.
Both `git diff inp...HEAD` and the controlling `git diff inp-lp...HEAD -- KAM` were inspected.
The latter adds 15 spatial modules (2,354 lines) and 15 generated root-import lines.
Initial tracked/untracked status was clean. Only this report is retained from the audit; the temporary axiom probe, inventory and logs were removed.

Read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the independent package-audit brief,
LP-W4C AUDIT FOCUS, SPEC, MAIN as amended by AMENDMENTS, and both component briefs/handoffs.
**N1 (input-path note):** `/root/code/KAM-inp-lp/docs/tracks/LP/packages/LP-W4C.md` does not exist.
The combined handoff explicitly names `LP-SP-CHART.md` and `LP-SP-PROD.md`; those existing briefs
at that same package directory provide the bounded intended statements used here. No substitute
mathematical target or hypothesis has been invented. No frozen/provider type-equality probe applies.

All declaration names below have prefix `KAM.Planetary.Spatial.`; locations are relative to
`KAM/Planetary/Spatial/`. Rows cover all 196 new public declarations (50 definitions and 146
lemmas/theorems). Private analytic projection helpers were also inspected. The facades add imports only.

## LP-SP-CHART

**Verdict: PASS WITH NOTES.** MAIN L17 (533–578), (44)–(46), is implemented with the documented
planar sign dictionary and an explicit real lift of the fast angle. No blocking statement, carrier,
or proof defect found. N1 is administrative; N2 records the inverse representation.

The actual coordinate dictionary is `w.1=(λ,ξ,v)`, `w.2=(I,η,u)`, with MAIN `(x,y)=(ξ,−η)`.
Thus MAIN `dx∧dy` is `dη∧dξ`, while `u,v` in (46) are used literally, giving
`dI∧dλ+dη∧dξ+du∧dv`. The planar eccentricity vector is proportional to `(ξ,η)=(x,−y)`,
exactly MAIN's `(k,l)` in (18). This is a sign convention, not a changed physical rotation.
`spatialPoincareDom` is exactly I>0 and Γ+Z<I, implying G=I−Γ>0 and Z<G.
The chart is literally R applied to both embedded planar vectors, with tilt `(u,−v,0)/(2√G)`.
Energy is total Kepler energy `−ν³/(2I²)`, not specific energy; both angular momentum identities
and the eccentricity vector have the source normalizations.

For symplecticity the polynomial `rot3Deriv` is proved to be the actual entrywise derivative
along every line. The sphere and tangent relations used in `rot3_deriv_eq` are proved from the
positive-root formulas on (44). `spatialPoincare_fderiv_fst/snd` identify the actual Jacobian,
`planarDeriv_cross` differentiates the locally valid identity Q×P=G e₃, and
`symplectic_form_alg` plus `rot3_form_identity` produce the missing du∧dv block. The final
identity quantifies over arbitrary tangent vectors. No conclusion-shaped Jacobian premise,
nonzero eccentricity/inclination assumption, or density argument is used.

The inverse uses zero-based indices 1 and 0 for MAIN's second and first direction components.
On the image, G>0, the direction is unit with positive third component, the recovered tilt has
Z<G, and Rᵀq,Rᵀp have zero third coordinates and positive planar cross product. This supplies
all planar-inverse premises; the image is an actual set equality. Negative energy at positive ν
excludes q=0 despite Lean's total division (also positive cross projection excludes q=0).
Circular Γ=0 and coplanar Z=0 points stay in the domain; the inverse recovers u=v=0 at direction e₃.
The boundaries I=0, Γ+Z=I and zero projection are properly excluded.

**N2 (representation deviation, already disclosed):** `spatialPoincareInv` selects a real angle
through the reused planar `Complex.arg`; it is not a globally analytic real-valued inverse and
can be discontinuous at an argument branch cut. The proved surface instead consists of a right
inverse on the whole region, a left inverse modulo 2π, exact lattice injectivity, and local
analytic inverses at every domain point. These faithfully express the source's angle read
modulo 2π and local analytic invertibility. No quotient analytic-manifold object is constructed
in this package. Do not describe the chosen global representative itself as globally analytic.

### Definition classification

Every row is PASS on the stated mathematical carrier. Total algebraic formulas outside that
carrier are explicitly distinguished from physical chart/derivative meanings; no theorem relies
on an invalid fallback. All definitions are in exposed public sections.

| Definition and location | Whole-carrier classification / edge behavior |
|---|---|
| `spatialShift` (Chart/Analytic.lean:86) | Total literal 2π integer shift of λ; all other slots fixed. |
| `spatialGamma` (Chart/Defs.lean:40) | Total nonnegative polynomial (ξ² + η²)/2; equals MAIN Γ under ξ=x, η=−y. |
| `spatialZ` (Chart/Defs.lean:43) | Total nonnegative polynomial (u² + v²)/2; no node angle. |
| `spatialAngMom` (Chart/Defs.lean:46) | Total polynomial I−Γ; positive on (44), not claimed a magnitude off it. |
| `spatialPlanar` (Chart/Defs.lean:49) | Total linear projection to ((λ,ξ),(I,η)); exactly the reused planar coordinates. |
| `spatialPlanarCLM` (Chart/Defs.lean:52) | Continuous linear packaging of that projection, with application equality. |
| `spatialPoincareDom` (Chart/Defs.lean:65) | Literal open domain I>0 and Γ+Z<I; includes Γ=0 and Z=0. |
| `spatialRot` (Chart/Defs.lean:69) | Literal incRotation u v (I−Γ), with u=w.2 2, v=w.1 2. Rotation guarantees require (44). |
| `spatialPoincare` (Chart/Defs.lean:74) | Literal R times embedded planar position and momentum, no conditional/fallback. Physical chart claims require ν>0 and (44). |
| `spatialEnergy` (Chart/Defs.lean:80) | Literal total Kepler energy; Lean division at ν=0 or q=0 is totalized. Physical use has ν>0, q≠0. |
| `spatialRegion` (Chart/Defs.lean:84) | Literal negative-energy/prograde predicate. For ν>0, q=0 cannot have negative energy; positive cross projection also excludes radial/zero angular momentum. |
| `spatialEccVector` (Chart/Elements.lean:34) | Literal eccentricity vector using p/ν and Euclidean dot products. Physical use requires ν>0 and q≠0; no off-carrier orbital claim. |
| `spatialRecU` (Chart/Inverse.lean:37) | Literal −√G x₂/√((1+x₃)/2); recovery uses G>0, unit x, x₃>0. Denominator strictly positive there. |
| `spatialRecV` (Chart/Inverse.lean:41) | Literal −√G x₁/√((1+x₃)/2), with correct zero-based index. Same recovery guards. |
| `spatialStateG` (Chart/Inverse.lean:45) | Euclidean magnitude of q×p on every state; positive on the prograde region. |
| `spatialStateDir` (Chart/Inverse.lean:48) | Normalized cross product; at G=0 Lean inverse gives zero. Unit-direction claims explicitly require positive projection. |
| `spatialStateRot` (Chart/Inverse.lean:51) | Literal recovered rotation. It has the physical reconstruction meaning on the prograde region, not on zero angular momentum states. |
| `spatialStatePlanar` (Chart/Inverse.lean:56) | Literal first two components of Rᵀq,Rᵀp. Omitted third components are proved zero on the region. |
| `spatialPoincareInv` (Chart/Inverse.lean:61) | Explicit reconstruction plus planar Complex.arg representative. Right inverse on the region; left inverse only modulo 2π. No globally analytic real-angle inverse is asserted (N2). |
| `spatialS` (Chart/LineDeriv.lean:68) | √G; strictly positive on (44). For G≤0 Real.sqrt totalization is not used as a positive square root. |
| `spatialA` (Chart/LineDeriv.lean:71) | u/(2√G), literal tilt component; denominator nonzero on (44). |
| `spatialB` (Chart/LineDeriv.lean:74) | −v/(2√G), literal signed tilt component; denominator nonzero on (44). |
| `spatialC` (Chart/LineDeriv.lean:77) | incCos u v G = √(1−a²−b²); positive on (44), including zero inclination. |
| `spatialDG` (Chart/LineDeriv.lean:80) | Total polynomial differential dG(h)=hI−ξ hξ−η hη, valid everywhere. |
| `spatialDS` (Chart/LineDeriv.lean:83) | Literal dG/(2√G); derivative meaning guarded by (44). |
| `spatialDA` (Chart/LineDeriv.lean:86) | Quotient-rule expression for da(h); derivative meaning guarded by (44). |
| `spatialDB` (Chart/LineDeriv.lean:90) | Quotient-rule expression for db(h), including the minus sign on v; guarded by (44). |
| `spatialDC` (Chart/LineDeriv.lean:94) | Literal −(a da+b db)/c; derivative meaning guarded by (44), where c>0. |
| `rot3` (Chart/RotAlgebra.lean:35) | Total polynomial matrix for tilt (a,b,0). Orthogonality/rotation meaning uses c²+a²+b²=1. |
| `rot3Deriv` (Chart/RotAlgebra.lean:41) | Total polynomial directional derivative of rot3; no carrier restriction needed for differentiation. |
| `rot3Omega` (Chart/RotAlgebra.lean:47) | Total polynomial infinitesimal-rotation vector. dR=R[ω] uses sphere and tangent identities, subsequently proved for actual chart derivatives. |
| `planarDeriv` (Chart/Symplectic.lean:64) | Actual fderiv of the reused planar chart at spatialPlanar w in direction spatialPlanar h. Physical differential claims require ν>0 and (44). |
| `spatialRotDeriv` (Chart/Symplectic.lean:139) | Explicit derivative matrix; equality with the actual line derivatives is proved on (44). |
| `spatialOmega` (Chart/Symplectic.lean:144) | rot3Omega evaluated at actual tilt and derivative data. All sphere/tangent constraints are discharged on (44). |

### Declaration-by-declaration statement review

| Source/node and location | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| Chart/Analytic.lean:40 | `analyticAt_spatialAngMom` | PASS | L17: analytic composition/periodicity on (44). |
| Chart/Analytic.lean:44 | `analyticAt_spatialPlanar` | PASS | L17: analytic composition/periodicity on (44). |
| Chart/Analytic.lean:48 | `analyticAt_spatialRot_apply` | PASS | L17: analytic composition/periodicity on (44). |
| Chart/Analytic.lean:68 | `analyticAt_poincare_spatialPlanar` | PASS | L17: analytic composition/periodicity on (44). |
| Chart/Analytic.lean:74 | `analyticOnNhd_spatialPoincare` | PASS | L17: analytic composition/periodicity on (44). |
| Chart/Analytic.lean:90 | `spatialPoincare_periodic` | PASS | L17: analytic composition/periodicity on (44). |
| Chart/Analytic.lean:103 | `spatialShift_mem` | PASS | L17: analytic composition/periodicity on (44). |
| Chart/Defs.lean:61 | `spatialPlanarCLM_apply` | PASS | L17 (44): explicit carrier/projection/domain fact. |
| Chart/Defs.lean:91 | `spatialGamma_nonneg` | PASS | L17 (44): explicit carrier/projection/domain fact. |
| Chart/Defs.lean:94 | `spatialZ_nonneg` | PASS | L17 (44): explicit carrier/projection/domain fact. |
| Chart/Defs.lean:98 | `spatialAngMom_pos` | PASS | L17 (44): explicit carrier/projection/domain fact. |
| Chart/Defs.lean:104 | `spatialZ_lt_angMom` | PASS | L17 (44): explicit carrier/projection/domain fact. |
| Chart/Defs.lean:109 | `spatial_carrier` | PASS | L17 (44): explicit carrier/projection/domain fact. |
| Chart/Defs.lean:114 | `spatial_mem_incCarrier` | PASS | L17 (44): explicit carrier/projection/domain fact. |
| Chart/Defs.lean:119 | `spatialPlanar_mem` | PASS | L17 (44): explicit carrier/projection/domain fact. |
| Chart/Defs.lean:127 | `spatialPlanar_gamma` | PASS | L17 (44): explicit carrier/projection/domain fact. |
| Chart/Defs.lean:130 | `isOpen_spatialPoincareDom` | PASS | L17 (44): explicit carrier/projection/domain fact. |
| Chart/Diffeo.lean:34 | `eq_zero_of_symplecticForm_eq_zero` | PASS | L17: nondegeneracy and analytic inverse-function theorem. |
| Chart/Diffeo.lean:43 | `spatialPoincare_fderiv_equiv` | PASS | L17: nondegeneracy and analytic inverse-function theorem. |
| Chart/Diffeo.lean:64 | `spatialPoincare_localDiffeo` | PASS WITH NOTES | N2: local analytic inverses, no global analytic Complex.arg representative. |
| Chart/Elements.lean:38 | `dotProduct_mulVec_mulVec_of_orth` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:43 | `planarEmbed_dot` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:46 | `planarEmbed_smul` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:49 | `planarEmbed_sub` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:52 | `planarEmbed_dot_self` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:59 | `spatialRot_transpose_mul` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:63 | `spatialRot_det` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:66 | `spatialPlanar_snd_zero` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:70 | `spatialPoincare_fst` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:73 | `spatialPoincare_snd` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:77 | `spatialEnergy_rot` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:84 | `spatialPoincare_energy` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:94 | `spatialPlanar_cross` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:103 | `spatialPoincare_cross` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:112 | `spatialPoincare_cross_dot_e₃` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:124 | `e₃_dot_self` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:127 | `spatialPoincare_cross_dot_self` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:135 | `spatialPoincare_cross_norm` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Elements.lean:142 | `spatialPoincare_eccVector` | PASS | L17 (45): Euclidean rotation invariance and planar elements. |
| Chart/Image.lean:33 | `spatialEnergy_mulVec` | PASS | L17: exact image/reconstruction or supporting algebra. |
| Chart/Image.lean:39 | `spatialPoincare_mem_region` | PASS | L17: exact image/reconstruction or supporting algebra. |
| Chart/Image.lean:51 | `dotProduct_e₃_eq` | PASS | L17: exact image/reconstruction or supporting algebra. |
| Chart/Image.lean:54 | `spatial_planeSq_nonneg` | PASS | L17: exact image/reconstruction or supporting algebra. |
| Chart/Image.lean:57 | `spatial_planeLength_nonneg` | PASS | L17: exact image/reconstruction or supporting algebra. |
| Chart/Image.lean:64 | `spatialPoincareInv_chart` | PASS | L17: exact image/reconstruction or supporting algebra. |
| Chart/Image.lean:180 | `spatialPoincare_image` | PASS | Set equality onto precisely negative energy and positive cross projection, ν>0. |
| Chart/Image.lean:190 | `spatialPoincare_eq_iff` | PASS | Equality iff a single integer λ shift; all slow and action slots fixed. |
| Chart/Inverse.lean:71 | `spatialRec_cc_pos` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:75 | `spatialRec_Z` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:88 | `spatialRec_lt` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:92 | `spatialRec_incCos` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:101 | `spatialRec_rot_e₃` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:118 | `spatialState_cross_apply_two` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:122 | `spatialState_dot_self` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:127 | `spatialStateG_pos` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:133 | `spatialStateG_sq` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:139 | `spatialStateDir_apply` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:143 | `spatialStateDir_sq` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:152 | `spatialStateDir_two_pos` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:164 | `spatialStateG_chart` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:168 | `spatialStateDir_chart` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:175 | `spatialStateRot_chart` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:190 | `spatialStatePlanar_chart` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/Inverse.lean:204 | `spatialPoincareInv_spatialPoincare` | PASS | L17 inverse: positive G, unit direction and positive third component where required. |
| Chart/LineDeriv.lean:33 | `hasDerivAt_fderiv_spatialLine` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:42 | `hasDerivAt_affine` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:46 | `rot3_hasDerivAt` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:99 | `spatialS_pos` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:102 | `spatialS_sq` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:105 | `spatialRot_eq_rot3` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:111 | `incCos_eq_sqrt_ab` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:117 | `spatialC_sq` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:129 | `spatialC_pos` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:132 | `spatial_rel_d` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:139 | `spatial_rel_u` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:146 | `spatial_rel_v` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:153 | `spatial_rel_G` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:159 | `hasDerivAt_line_angMom` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:169 | `hasDerivAt_line_S` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:174 | `hasDerivAt_line_u` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:179 | `hasDerivAt_line_v` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:184 | `hasDerivAt_line_A` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:194 | `hasDerivAt_line_B` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:204 | `hasDerivAt_line_C` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:230 | `spatialRot_line_eq` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/LineDeriv.lean:238 | `spatialRot_line_hasDerivAt` | PASS | L17 symplectic computation: genuine derivatives; square-root/quotient guards from (44). |
| Chart/RotAlgebra.lean:50 | `incRotation_eq_rot3` | PASS | L17 (46): polynomial identity; sphere/tangent constraints explicit and later discharged. |
| Chart/RotAlgebra.lean:58 | `rot3_transpose_mul_deriv` | PASS | L17 (46): polynomial identity; sphere/tangent constraints explicit and later discharged. |
| Chart/RotAlgebra.lean:75 | `rot3_deriv_eq` | PASS | L17 (46): polynomial identity; sphere/tangent constraints explicit and later discharged. |
| Chart/RotAlgebra.lean:90 | `rot3_form_identity` | PASS | Generic algebraic helper; sphere/tangent identities are verified for actual chart data. |
| Chart/Symplectic.lean:43 | `symplectic_form_alg` | PASS | Conditional algebraic helper; orthogonality and dR=R[ω] are proved before use. |
| Chart/Symplectic.lean:67 | `spatialPlanar_line` | PASS | L17: actual Jacobian algebra; carrier/analyticity supplied, no density premise. |
| Chart/Symplectic.lean:72 | `hasDerivAt_planar_line` | PASS | L17: actual Jacobian algebra; carrier/analyticity supplied, no density premise. |
| Chart/Symplectic.lean:80 | `hasDerivAt_planar_fst` | PASS | L17: actual Jacobian algebra; carrier/analyticity supplied, no density premise. |
| Chart/Symplectic.lean:89 | `hasDerivAt_planar_snd` | PASS | L17: actual Jacobian algebra; carrier/analyticity supplied, no density premise. |
| Chart/Symplectic.lean:98 | `eventually_line_mem` | PASS | L17: actual Jacobian algebra; carrier/analyticity supplied, no density premise. |
| Chart/Symplectic.lean:105 | `planarDeriv_cross` | PASS | L17: actual Jacobian algebra; carrier/analyticity supplied, no density premise. |
| Chart/Symplectic.lean:124 | `hasDerivAt_rot_embed` | PASS | Ordinary product-rule helper; derivative premises proved at its calls. |
| Chart/Symplectic.lean:148 | `spatialRotDeriv_eq` | PASS | L17: actual Jacobian algebra; carrier/analyticity supplied, no density premise. |
| Chart/Symplectic.lean:153 | `spatialPoincare_fderiv_fst` | PASS | L17: actual Jacobian algebra; carrier/analyticity supplied, no density premise. |
| Chart/Symplectic.lean:171 | `spatialPoincare_fderiv_snd` | PASS | L17: actual Jacobian algebra; carrier/analyticity supplied, no density premise. |
| Chart/Symplectic.lean:195 | `dotProduct_e₃` | PASS | L17: actual Jacobian algebra; carrier/analyticity supplied, no density premise. |
| Chart/Symplectic.lean:199 | `spatialPoincare_symplectic_at` | PASS | Exact full-domain Jacobian identity, including Γ=0 and Z=0. |
| Chart/Symplectic.lean:256 | `spatialPoincare_symplectic` | PASS | Exact IsSymplecticOn 1 on all (44); arbitrary tangent vectors and actual fderiv. |

## LP-SP-PROD

**Verdict: PASS.** The component brief's four items are supplied literally. N12 is respected by
`Phase (n+(n+n))`, with n fast and 2n slow pairs, and `Phase (n*3)` Cartesian output. The exact
Fin block maps and their inverse/application identities account for all coordinates. Derivative
assembly is proved, and product symplecticity sums the one-body Jacobian identities on both sides.
There is no dimension coercion hiding a change of symplectic form. Fast lattice periodicity
preserves the domain and fixes every slow/action coordinate; image and injectivity use the exact
per-body prograde/negative-energy predicates. Local analytic diffeomorphism is established
between the two equal finite dimensions.

The energy and cross-product bridge lemmas identify the existing spatial model with the one-body
chart. The fixed-plane deficit is literally ΣΛ_i−L·e₃, not the strong AMD. Its chart value is
Σ(Γ_i+Z_i) and exactly half the sum of squared slow coordinates (Euclidean square sum, not the
ambient Pi sup norm). The all-state inequality C≤C_e₃ follows from L·e₃≤|L| and uses no elliptic
or alignment premise. Equality with C under L=|L|e₃ is the source's explicitly conditional
geometric statement; no conservation or automatic alignment theorem is claimed here.

`fSpatial` counts i<j pairs once and uses |Σp_i|²/2 for recoil. The exact split holds for every
μ on the chart domain; it is stronger than requiring small positive μ. Product charts may contain
cross-body collisions, correctly: the split remains a total algebraic identity there, while all
analyticity claims for the Newtonian perturbation/composed Hamiltonian are on the collision-free
part. The carrier excludes star and mutual collisions; the perturbation itself needs only the
latter exclusion, so the physical carrier used is sufficient. At n=0 finite sums are zero,
all phase spaces are singletons, domains/regions are universal, the lattice is trivial, and
the derivative/diffeomorphism claims remain valid. At n=1 there are no pair potentials. No n≥2,
mass normalization max ν=1, or action ordering is needed for these local chart identities;
omitting those global source standing assumptions is a valid strengthening.

### Definition classification

| Definition and location | Whole-carrier classification / edge behavior |
|---|---|
| `spatialFixedPlaneDeficit` (Product/Deficit.lean:41) | Literal ΣΛ_i−L·e₃. Off negative energy, Λ_i retains its existing totalized algebraic value; all orbital identities use the chart carrier. The all-state comparison remains valid algebraically. |
| `spatialBlock` (Product/Defs.lean:52) | Total linear block extraction: ((λ_i,ξ_i,v_i),(I_i,η_i,u_i)); all three index blocks are disjoint. |
| `ofSpatialBodies` (Product/Defs.lean:57) | Total body-major assembly into Phase (n*3); bodyVector3 gives exact component recovery. |
| `unblockSpatial` (Product/Defs.lean:61) | Total inverse block assembly into Phase (n+(n+n)); spatialBlock_unblockSpatial verifies every slot. |
| `spatialPoincareProd` (Product/Defs.lean:66) | Literal bodywise one-body charts followed by Cartesian assembly; source meaning under positive masses and product domain. |
| `spatialPoincareProdDom` (Product/Defs.lean:70) | Literal universal product of (44); no extra cross-body or alignment constraint. At n=0 it is the whole singleton phase. |
| `spatialRegionProd` (Product/Defs.lean:74) | Literal bodywise negative-energy/prograde region; does not impose mutual collision exclusion. At n=0 the predicate is vacuous. |
| `spatialActions` (Product/Defs.lean:78) | Total fast action projection w↦fast w.2; no mass dependence. |
| `spatialGammaBody` (Product/Defs.lean:81) | Literal Γ of each extracted body; nonnegative on the entire phase. |
| `spatialZBody` (Product/Defs.lean:84) | Literal Z of each extracted body; nonnegative on the entire phase. |
| `ofSpatialBodiesCLM` (Product/Defs.lean:125) | Continuous linear packaging of Cartesian assembly; exact application theorem. |
| `blockSlots` (Product/Defs.lean:141) | Exact three slots i, n+i, 2n+i via Fin.castAdd/natAdd; no fallback indexing. |
| `spatialBlockCLM` (Product/Defs.lean:145) | Continuous linear packaging of block extraction, with application equality. |
| `spatialProdShift` (Product/Defs.lean:186) | Total w+fastShift with a=n,b=n+n; only λ shifts by 2πk, including the empty lattice at n=0. |
| `fSpatial` (Product/Split.lean:40) | Literal MAIN (1): half Euclidean squared total momentum minus each pair potential once (i<j). At collisions division is totalized; analyticity claims are collision guarded. |
| `spatialHProd` (Product/Split.lean:46) | Literal −Σν_i³/(2I_i²); physical Kepler identification uses I_i>0 from the product domain. At n=0 the empty sum is zero. |

### Declaration-by-declaration statement review

| Source/node and location | Lean declaration | Verdict | Reason / note |
|---|---|---|---|
| Product/Chart.lean:47 | `analyticOnNhd_spatialPoincareProd` | PASS | L17 product: blockwise derivative/chart fact; positive masses and product domain where needed. |
| Product/Chart.lean:60 | `hasFDerivAt_spatialPoincareProd` | PASS | L17 product: blockwise derivative/chart fact; positive masses and product domain where needed. |
| Product/Chart.lean:81 | `fderiv_spatialPoincareProd_apply` | PASS | L17 product: blockwise derivative/chart fact; positive masses and product domain where needed. |
| Product/Chart.lean:92 | `spatialPoincareProd_symplectic` | PASS | Heterogeneous dimensions n+(n+n) and n*3 handled by exact block sums. |
| Product/Chart.lean:103 | `spatialPoincareProd_lattice` | PASS | L17 product: blockwise derivative/chart fact; positive masses and product domain where needed. |
| Product/Chart.lean:118 | `spatialPoincareProd_mem_region` | PASS | L17 product: blockwise derivative/chart fact; positive masses and product domain where needed. |
| Product/Chart.lean:127 | `spatialPoincareProd_image` | PASS | Exact product image; cross-body collisions correctly remain possible. |
| Product/Chart.lean:148 | `spatialPoincareProd_eq_iff` | PASS | Equality iff independent fast integer shifts; no slow shifts. |
| Product/Chart.lean:187 | `spatialPoincareProd_fderiv_equiv` | PASS | L17 product: blockwise derivative/chart fact; positive masses and product domain where needed. |
| Product/Chart.lean:215 | `spatialPoincareProd_localDiffeo` | PASS WITH NOTES | N2: local analytic inverse, together with exact image and lattice theorem. |
| Product/Deficit.lean:47 | `spatialKeplerEnergy_eq_spatialEnergy` | PASS | L17/L18: literal model bridge or fixed-plane sum identity. |
| Product/Deficit.lean:53 | `planetAngularMomentum3_eq_cross` | PASS | L17/L18: literal model bridge or fixed-plane sum identity. |
| Product/Deficit.lean:60 | `spatialKeplerEnergy_spatialPoincareProd` | PASS | L17/L18: literal model bridge or fixed-plane sum identity. |
| Product/Deficit.lean:68 | `spatialBlock_snd_zero` | PASS | L17/L18: literal model bridge or fixed-plane sum identity. |
| Product/Deficit.lean:73 | `spatialKeplerAction_spatialPoincareProd` | PASS | L17/L18: literal model bridge or fixed-plane sum identity. |
| Product/Deficit.lean:87 | `planetAngularMomentum3_dot_e₃` | PASS | L17/L18: literal model bridge or fixed-plane sum identity. |
| Product/Deficit.lean:98 | `angularMomentum3_dot_e₃_spatialPoincareProd` | PASS | L17/L18: literal model bridge or fixed-plane sum identity. |
| Product/Deficit.lean:110 | `spatialFixedPlaneDeficit_spatialPoincareProd` | PASS | L17/L18: literal model bridge or fixed-plane sum identity. |
| Product/Deficit.lean:123 | `sum_gamma_add_z_eq_half_slow_sq` | PASS | L17/L18: literal model bridge or fixed-plane sum identity. |
| Product/Deficit.lean:143 | `spatialFixedPlaneDeficit_eq_half_slow_sq` | PASS | L17/L18: literal model bridge or fixed-plane sum identity. |
| Product/Deficit.lean:149 | `e₃_spaceLength` | PASS | L17/L18: literal model bridge or fixed-plane sum identity. |
| Product/Deficit.lean:153 | `spatialStrongAMD_le_spatialFixedPlaneDeficit` | PASS | Stronger: all ν and all z; Cauchy–Schwarz with unit e₃, no elliptic/alignment premise. |
| Product/Deficit.lean:162 | `spatialStrongAMD_spatialPoincareProd_of_aligned` | PASS | Source alignment L=|L|e₃ is a geometric premise; deficit equality is proved, not assumed. |
| Product/Defs.lean:88 | `spatialPoincareProd_eq` | PASS | L17/N12: exact finite block/layout/shift identity. |
| Product/Defs.lean:92 | `bodyVector3_ofSpatialBodies_fst` | PASS | L17/N12: exact finite block/layout/shift identity. |
| Product/Defs.lean:97 | `bodyVector3_ofSpatialBodies_snd` | PASS | L17/N12: exact finite block/layout/shift identity. |
| Product/Defs.lean:102 | `ofSpatialBodies_injective` | PASS | L17/N12: exact finite block/layout/shift identity. |
| Product/Defs.lean:109 | `ofSpatialBodies_bodyVector3` | PASS | L17/N12: exact finite block/layout/shift identity. |
| Product/Defs.lean:114 | `spatialBlock_unblockSpatial` | PASS | L17/N12: exact finite block/layout/shift identity. |
| Product/Defs.lean:119 | `spatialPoincareProd_block` | PASS | L17/N12: exact finite block/layout/shift identity. |
| Product/Defs.lean:137 | `ofSpatialBodiesCLM_apply` | PASS | L17/N12: exact finite block/layout/shift identity. |
| Product/Defs.lean:155 | `spatialBlockCLM_apply` | PASS | L17/N12: exact finite block/layout/shift identity. |
| Product/Defs.lean:160 | `isOpen_spatialPoincareProdDom` | PASS | L17/N12: exact finite block/layout/shift identity. |
| Product/Defs.lean:169 | `symplecticForm_ofSpatialBodies` | PASS | L17/N12: exact finite block/layout/shift identity. |
| Product/Defs.lean:175 | `symplecticForm_spatialBlocks` | PASS | L17/N12: exact finite block/layout/shift identity. |
| Product/Defs.lean:189 | `spatialBlock_shift` | PASS | L17/N12: exact finite block/layout/shift identity. |
| Product/Split.lean:50 | `spatialHamiltonian_split` | PASS | MAIN (1), L17: literal split; analyticity collision guarded. |
| Product/Split.lean:54 | `spatialHamiltonian_spatialPoincareProd` | PASS | Exact −Σν³/(2I²)+μ fSpatial; μ arbitrary, no smallness or collision premise for the algebraic equality. |
| Product/Split.lean:66 | `analyticOnNhd_fSpatial` | PASS | MAIN (1), L17: literal split; analyticity collision guarded. |
| Product/Split.lean:94 | `analyticOnNhd_fSpatial_spatialPoincareProd` | PASS | MAIN (1), L17: literal split; analyticity collision guarded. |
| Product/Split.lean:101 | `isOpen_spatialPoincareProd_preimage` | PASS | MAIN (1), L17: literal split; analyticity collision guarded. |
| Product/Split.lean:107 | `analyticOnNhd_spatialHamiltonian_spatialPoincareProd` | PASS | MAIN (1), L17: literal split; analyticity collision guarded. |

## Combined verdict

**LP-W4C: PASS WITH NOTES (N1, N2).** No mathematical correction is requested for the reviewed
package statements. This is a package/source audit, not a frozen-anchor seal or a proof of any
later complex-tube, confinement, conservation/alignment, or exponential-safety consumer.
N2 is an explicit implementation representation boundary, not a missing chart hypothesis.

No conclusion-shaped hypotheses were found. Generic helpers assume sphere/tangent identities,
orthogonal matrices, or derivative data appropriate to their algebra/calculus statements; every
actual-chart call supplies independent proofs of these facts. The aligned deficit theorem takes
exactly the geometric alignment premise required by the source. There is no provider or
DRAFT_SORRY import in the new modules. Standard axiom checks below also exclude a hidden sorry
or nonstandard assumption in the imported proof dependencies of every new public theorem.

### Hygiene and validation

All audit Lean/Lake execution was serialized. Builds used the LP driver, whose one-target calls
hold the compile gate and execute the exact D53 wrapper:

```text
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

Targeted builds (one module per lake invocation):

```text
/root/code/KAM-inp/.drafts/LP/lp_build.sh /root/code/KAM-inp-lp-w4c KAM.Planetary.Spatial.Chart KAM.Planetary.Spatial.Product
[lp_build] slot 2: KAM.Planetary.Spatial.Chart (07:39:47)
Build completed successfully (9113 jobs).
[lp_build] slot 2: KAM.Planetary.Spatial.Product (07:39:58)
Build completed successfully (9126 jobs).
exit 0
```

These are targeted dependency-closure builds, not a clean/rebuild-from-scratch or an application
build. Output also replays upstream unused-variable warnings in Kepler/Energy, Kepler/Mass and
Poincare/Chart; the package has two unused-simp-argument warnings at
Chart/Symplectic.lean:248 (`Matrix.cons_val_zero`, `Matrix.cons_val_one`). No elaboration failure,
resource-budget override or memory-cap failure occurred.

Axiom probe: temporary `.lake/abi-scratch/LPW4CAuditAxioms.lean`, importing both facades and
issuing `#print axioms KAM.Planetary.Spatial.<name>` once for each of the 146 public lemmas/theorems
listed above. Exact command:

```text
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/LPW4CAuditAxioms.lean
exit 0
```

All 146 names returned exactly `[propext, Classical.choice, Quot.sound]`; none returned another
axiom or an error. Complete literal output (including wrapped lines):

```text
'KAM.Planetary.Spatial.analyticAt_spatialAngMom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.analyticAt_spatialPlanar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.analyticAt_spatialRot_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.analyticAt_poincare_spatialPlanar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.analyticOnNhd_spatialPoincare' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialShift_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPlanarCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialGamma_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialZ_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialAngMom_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialZ_lt_angMom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatial_carrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatial_mem_incCarrier' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPlanar_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPlanar_gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.isOpen_spatialPoincareDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.eq_zero_of_symplecticForm_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_fderiv_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_localDiffeo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.dotProduct_mulVec_mulVec_of_orth' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.planarEmbed_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.planarEmbed_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.planarEmbed_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.planarEmbed_dot_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialRot_transpose_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialRot_det' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPlanar_snd_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialEnergy_rot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPlanar_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_cross_dot_e₃' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.e₃_dot_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_cross_dot_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_cross_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_eccVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialEnergy_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_mem_region' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.dotProduct_e₃_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatial_planeSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatial_planeLength_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincareInv_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialRec_cc_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialRec_Z' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialRec_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialRec_incCos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialRec_rot_e₃' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialState_cross_apply_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialState_dot_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialStateG_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialStateG_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialStateDir_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialStateDir_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialStateDir_two_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialStateG_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialStateDir_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialStateRot_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialStatePlanar_chart' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincareInv_spatialPoincare' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.hasDerivAt_fderiv_spatialLine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.hasDerivAt_affine' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.rot3_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialS_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialS_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialRot_eq_rot3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.incCos_eq_sqrt_ab' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialC_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialC_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatial_rel_d' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatial_rel_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatial_rel_v' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatial_rel_G' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.hasDerivAt_line_angMom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.hasDerivAt_line_S' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.hasDerivAt_line_u' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.hasDerivAt_line_v' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.hasDerivAt_line_A' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.hasDerivAt_line_B' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.hasDerivAt_line_C' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialRot_line_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialRot_line_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.incRotation_eq_rot3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.rot3_transpose_mul_deriv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.rot3_deriv_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.rot3_form_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.symplectic_form_alg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPlanar_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.hasDerivAt_planar_line' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.hasDerivAt_planar_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.hasDerivAt_planar_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.eventually_line_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.planarDeriv_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.hasDerivAt_rot_embed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialRotDeriv_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_fderiv_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_fderiv_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.dotProduct_e₃' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_symplectic_at' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincare_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.analyticOnNhd_spatialPoincareProd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.hasFDerivAt_spatialPoincareProd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.fderiv_spatialPoincareProd_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincareProd_symplectic' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincareProd_lattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincareProd_mem_region' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincareProd_image' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincareProd_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincareProd_fderiv_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincareProd_localDiffeo' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialKeplerEnergy_eq_spatialEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.planetAngularMomentum3_eq_cross' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialKeplerEnergy_spatialPoincareProd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Planetary.Spatial.spatialBlock_snd_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialKeplerAction_spatialPoincareProd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Planetary.Spatial.planetAngularMomentum3_dot_e₃' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.angularMomentum3_dot_e₃_spatialPoincareProd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Planetary.Spatial.spatialFixedPlaneDeficit_spatialPoincareProd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Planetary.Spatial.sum_gamma_add_z_eq_half_slow_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialFixedPlaneDeficit_eq_half_slow_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Planetary.Spatial.e₃_spaceLength' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialStrongAMD_le_spatialFixedPlaneDeficit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Planetary.Spatial.spatialStrongAMD_spatialPoincareProd_of_aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Planetary.Spatial.spatialPoincareProd_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.bodyVector3_ofSpatialBodies_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.bodyVector3_ofSpatialBodies_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.ofSpatialBodies_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.ofSpatialBodies_bodyVector3' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialBlock_unblockSpatial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialPoincareProd_block' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.ofSpatialBodiesCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialBlockCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.isOpen_spatialPoincareProdDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.symplecticForm_ofSpatialBodies' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.symplecticForm_spatialBlocks' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialBlock_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialHamiltonian_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.spatialHamiltonian_spatialPoincareProd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Planetary.Spatial.analyticOnNhd_fSpatial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.analyticOnNhd_fSpatial_spatialPoincareProd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Planetary.Spatial.isOpen_spatialPoincareProd_preimage' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.Spatial.analyticOnNhd_spatialHamiltonian_spatialPoincareProd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Lint was run only through the prescribed wrapper, after the builds and axiom probe had finished:

```text
/root/code/KAM-inp/.drafts/LP/lp_lint.sh /root/code/KAM-inp-lp-w4c
check_lean_modules: PASS (3747 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
exit 0
```

The ABI check explicitly uses file hashes for the two named opt-in KAMLunarBand anchors; it does
not build or replay those application declarations. No stale-root warning occurred.


Kernel replay and public short-name checks: **launcher-owned evidence**. The task explicitly
states these were already run, but their transcripts and exact commands/exit codes are not
visible in this auditor's pane. They were not rerun, in accordance with the economical scope;
this report does not invent independent replay/name-check output. The successful targeted
builds above are Lake builds, not leanchecker kernel replay. No frozen/provider identity or
seal-body probe is applicable because no track-LP statement is frozen.

Static scoped inspection: the 15 new modules range from 26 to 264 physical lines (maximum
Chart/Symplectic.lean, 264), all below 1500; module copyright, `module`, public imports and
docstrings are present. Declaration-bearing files have exposed public noncomputable sections;
facades contain no declarations and just re-export modules. No `sorry`, `admit`, `axiom`, `unsafe`,
`opaque`, resource override, EuclideanSpace, provider import, root import, or proof escape found
in the new package. SPEC statement-surface sentence is present in every module (with normal
line wrapping). No new structures, instances or bundled premise fields are introduced.

```text
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
<empty>
exit 0
```

The only generated-root delta is 15 public imports in `KAM/Root/Planetary.lean`, exactly the new
package modules, as disclosed in the handoff; the auditor did not edit or regenerate it. No
frozen file, manifest, README, lakefile, source, implementation or tracked build script was edited.

### Suspected source defects, deviations and uncertainties

No new suspected defect in the pinned MAIN/AMENDMENTS was found in this package's source slice;
there is no erratum to quote or register. N1 is a missing requested combined brief path, with
component briefs explicitly identified by the combined handoff. N2 is the already disclosed
real-angle representative/local-inverse distinction. The layout `n+(n+n)` versus `n+2*n` is an
exact finite-index engineering choice allowed by the product brief and AMENDMENTS N12. Dropping
unneeded global mass normalization, n≥2 and ordering assumptions strengthens the local results.
The generic prohibition on a generated root diff is accounted for by the expressly disclosed
regenerated root-import delta. The audit introduced no mathematical deviation. The only
validation uncertainty is the unavailable launcher replay/name-check transcript; it has not
been represented as an independently observed exit code.
