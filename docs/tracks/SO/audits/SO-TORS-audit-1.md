# SO-TORS independent audit 1

Verdict: **PASS WITH NOTES**. All six signed declarations pass; the scoped SO-TORS slice is complete and its producer/consumer contracts are ready for downstream assembly. No frozen theorem anchor is proved or sealed by this package: these are `KAM.Certificate` infrastructure declarations, not `KAM.Provider` exports. The per-anchor sealing test in the generic brief is therefore inapplicable; its exact-type and explicit-application tests were applied to the six signed exports instead.

Audited worktree: `/root/code/KAM-inp-sotors`; HEAD `b291e7c7ab4ac830a48d0f1719963f8b8663ba50`; `inp` `ea4f6ea55bac1564e644be75ffcd383cae0a259d`; merge base `bc4e6f2499702de2adb1577132c2916797979aa0`. Reviewed the complete `git diff inp...HEAD`: four new Lean files and the handoff only. The handoff names implementation head `46694661`; the sole later commit adds that handoff, with no Lean changes. Initial tracked working tree was clean.

Authority: user brief and exact destination override the generic brief's main-worktree destination. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `SO-TORS-handoff.md` including AUDIT FOCUS. Compared against Revision 7 `/root/code/KAM/docs/tracks/SO/design/SO-LEAN-DESIGN.md` §1.9, §4, §7 SO-TORS, §8 and §F; `/root/code/KAM-inp/.drafts/design/SOSignatures.lean:754–803`; track-I statement, blueprint `bpI:p0:stripdata`, `bpI:p0:extended`, and regularity steps under `bpI:p1:extended-basic`. There is no `docs/tracks/SO/statement.md` in this checkout; SO's signed design is the package authority. Read the frozen torsion, frame, Gram, bordered torsion and average definitions, and the actual consumer `KAM/Iso/Charts/Inputs.lean:62–63`. No I/N/P headline theorem is claimed here.

## Signed surface and mathematical review

All six declaration headers are **byte-identical** to the signature file, including binder names/order, fully qualified frozen references, `hn`, `{sw Nw}`, rational `s`, real scalar action, shape, enclosure and continuity. `torsionIdx`'s body also agrees exactly. Fresh scratch declarations copied each signed header and applied the export to every explicit binder in order. Both directions of `type_of%` assignment elaborated. Explicit argument lists:

| Export (`KAM.Certificate.` prefix) | Verdict | Explicit application |
|---|---|---|
| `torsionIdx` | PASS | `n` |
| `torsionModels` | PASS | `n e K wit Binv δβ box s W cfg pe` |
| `torsionModels_sound` | PASS | `hn hD hnv hW hKD wit Binv cfg hpe hG box s hT hω` |
| `torsionAvgCheck` | PASS | `n T S σTμ` |
| `torsionAvgCheck_shape` | PASS | `h` |
| `torsionAvgCheck_sound` | PASS | `hρ hT hcont S σTμ h` |

Producer (`Models.lean:551–625`): Gram invertibility and `‖G⁻¹-B‖` come from `gramCheck_sound`; `Slp.compose_sound` supplies all requested jet enclosures. The second-derivative character calculation uses `(2π)²(-k_j k_l)` with backend rounding paid in the radius. Index equivalences in matrix products exhaust `Fin n` or `Fin n ⊕ Fin n`. The normal-frame derivative uses `D(G⁻¹)=-G⁻¹(DLᵀL+LᵀDL)G⁻¹`. The torsion block is literally `Nᵀ Ω₀(DX_H N-DN[sω])`. The border is `sω`, the last row is **DH(K)N**, and the corner is zero. Shape is constructed, and continuity follows from holomorphy on the open strip/domain and the certified Gram unit condition. No invariance, Lagrangian identity, torsion invertibility or conclusion-shaped premise is assumed.

Consumer (`Average.lean:247–356`): the zero coefficient is enclosed as a ball, and its rounding radius is added to the model radius. `CertModel.Encloses.average` uses the supplied continuity and positive strip to justify integration over the unit real cube; no unproved integrability premise is hidden. With A the exact frozen average, the proof establishes bounds on `A-C`, S and `I-SC`, then bounds `I-SA`. `matrix_inv_of_approx_inverse` is applied on **Fin n ⊕ Unit**, without a principal-block substitution or a restriction to a special witness. The final division is justified by δ<1. The result is exactly the determinant unit and individual inverse row sums required by `IG1Body`, with rational σTμ cast to ℝ. The certificate assembly must choose σTμ with the required margin; that later assembly is outside SO-TORS.

F7: the check's first two conjunctions test exactly n+1 rows and n+1 entries in every row for T and S. The law-free shape theorem exposes both. `torsionIdx` is injective, bounded, and its sum covers all n+1 indices, including the final row/column. The successful producer emits the same shape. Thus a larger invertible matrix cannot certify a singular smaller one by changing the dimension.

## Every public declaration

Each row is one declaration; all names below are prefixed by `KAM.Certificate.`. The node column maps internal support declarations to the signed design operation they implement; they are not represented as additional blueprint theorems. There are **57 definitions and 65 theorems**, no new structure or abbreviation. Every helper's premises are typing/index data, arithmetic laws, source regularity, or the previously proved enclosure used in a compositional contract. No widened constant dependence or weakened signed conclusion was found.

| Node / file:line | Declaration | Verdict | Reason / definition classification |
|---|---|---|---|
| §1.9 / §F Frame.lean:41 | `torsionIdx` (def) | PASS | §F / F7: exact bordered index, range, injectivity, or exhaustive finite sum; includes the corner index n. |
| §1.9 / §F Frame.lean:43 | `torsionIdx_lt` (theorem) | PASS | §F / F7: exact bordered index, range, injectivity, or exhaustive finite sum; includes the corner index n. |
| §1.9 / §F Frame.lean:55 | `fderiv_tangentMat_eq_sum_partials` (theorem) | PASS | §1.9 / bpI:p0:stripdata, stepI:p1:eb-holo: genuine frame/field calculus; differentiability and Gram-unit premises are supplied by the producer. |
| §1.9 / §F Frame.lean:67 | `fderiv_normalMat_apply` (theorem) | PASS | §1.9 / bpI:p0:stripdata, stepI:p1:eb-holo: genuine frame/field calculus; differentiability and Gram-unit premises are supplied by the producer. |
| §1.9 / §F Frame.lean:93 | `differentiableOn_torsion_of_frame` (theorem) | PASS | §1.9 / bpI:p0:stripdata, stepI:p1:eb-holo: genuine frame/field calculus; differentiability and Gram-unit premises are supplied by the producer. |
| §1.9 / §F Frame.lean:101 | `fderiv_apply_normalFrame` (theorem) | PASS | §1.9 / bpI:p0:stripdata, stepI:p1:eb-holo: genuine frame/field calculus; differentiability and Gram-unit premises are supplied by the producer. |
| §1.9 / §F Frame.lean:111 | `sqMat_apply_eq_phaseBasis` (theorem) | PASS | §1.9 / bpI:p0:stripdata, stepI:p1:eb-holo: genuine frame/field calculus; differentiability and Gram-unit premises are supplied by the producer. |
| §1.9 / §F Frame.lean:118 | `linMat_apply_eq` (theorem) | PASS | §1.9 / bpI:p0:stripdata, stepI:p1:eb-holo: genuine frame/field calculus; differentiability and Gram-unit premises are supplied by the producer. |
| §1.9 / §F Frame.lean:130 | `continuousOn_extendedTorsion` (theorem) | PASS | §1.9 / bpI:p0:stripdata, stepI:p1:eb-holo: genuine frame/field calculus; differentiability and Gram-unit premises are supplied by the producer. |
| §1.9 / §F Frame.lean:182 | `hasFDerivAt_charSum` (theorem) | PASS | §1.9 second-derivative support: period-one characters, identity angle term and both embedding components; no extra analytic invoice. |
| §1.9 / §F Frame.lean:198 | `CertPoly.fderiv_fderiv_eval_single` (theorem) | PASS | §1.9 second-derivative support: period-one characters, identity angle term and both embedding components; no extra analytic invoice. |
| §1.9 / §F Frame.lean:223 | `CertPoly.differentiable_fderiv_eval_single` (theorem) | PASS | §1.9 second-derivative support: period-one characters, identity angle term and both embedding components; no extra analytic invoice. |
| §1.9 / §F Frame.lean:237 | `tangentMat_eval_inl` (theorem) | PASS | §1.9 second-derivative support: period-one characters, identity angle term and both embedding components; no extra analytic invoice. |
| §1.9 / §F Frame.lean:245 | `tangentMat_eval_inr` (theorem) | PASS | §1.9 second-derivative support: period-one characters, identity angle term and both embedding components; no extra analytic invoice. |
| §1.9 / §F Frame.lean:252 | `fderiv_tangentMat_eval_inl` (theorem) | PASS | §1.9 second-derivative support: period-one characters, identity angle term and both embedding components; no extra analytic invoice. |
| §1.9 / §F Frame.lean:262 | `fderiv_tangentMat_eval_inr` (theorem) | PASS | §1.9 second-derivative support: period-one characters, identity angle term and both embedding components; no extra analytic invoice. |
| §1.9 / §F Frame.lean:280 | `deriv2Mult` (def) | PASS | §1.9: -k_j k_l coefficient at degree d+2; rounded products paid in the weighted radius, zero-factor removal exact. |
| §1.9 / §F Frame.lean:283 | `deriv2Coeff` (def) | PASS | §1.9: -k_j k_l coefficient at degree d+2; rounded products paid in the weighted radius, zero-factor removal exact. |
| §1.9 / §F Frame.lean:286 | `deriv2Err` (def) | PASS | §1.9: -k_j k_l coefficient at degree d+2; rounded products paid in the weighted radius, zero-factor removal exact. |
| §1.9 / §F Frame.lean:289 | `deriv2Item` (def) | PASS | §1.9: -k_j k_l coefficient at degree d+2; rounded products paid in the weighted radius, zero-factor removal exact. |
| §1.9 / §F Frame.lean:295 | `CertModel.ofDeriv2` (def) | PASS | §1.9: -k_j k_l coefficient at degree d+2; rounded products paid in the weighted radius, zero-factor removal exact. |
| §1.9 / §F Frame.lean:301 | `norm_deriv2Coeff_sub` (theorem) | PASS | §1.9: -k_j k_l coefficient at degree d+2; rounded products paid in the weighted radius, zero-factor removal exact. |
| §1.9 / §F Frame.lean:318 | `deriv2Items_spec` (theorem) | PASS | §1.9: -k_j k_l coefficient at degree d+2; rounded products paid in the weighted radius, zero-factor removal exact. |
| §1.9 / §F Frame.lean:355 | `CertModel.Encloses.ofDeriv2` (theorem) | PASS | §1.9: -k_j k_l coefficient at degree d+2; rounded products paid in the weighted radius, zero-factor removal exact. |
| §1.9 / §F Average.lean:41 | `listShapeOk` (def) | PASS | §F / F7: exact row count and every row length; law-free shape contract matches signed header. |
| §1.9 / §F Average.lean:45 | `isZeroKeyN` (def) | PASS | §1.9 average: zero mode means certKeyFun n k = 0; all duplicate/short/long keys interpreted consistently, rounded coefficient sum retained as a ball. |
| §1.9 / §F Average.lean:48 | `zeroModeBall` (def) | PASS | §1.9 average: zero mode means certKeyFun n k = 0; all duplicate/short/long keys interpreted consistently, rounded coefficient sum retained as a ball. |
| §1.9 / §F Average.lean:52 | `ccEntry` (def) | PASS | §1.9: total list access and outward-rounded centres/radii/row sums; shapes prevent missing witness entries in successful certificates. |
| §1.9 / §F Average.lean:56 | `avgCentre` (def) | PASS | §1.9: total list access and outward-rounded centres/radii/row sums; shapes prevent missing witness entries in successful certificates. |
| §1.9 / §F Average.lean:60 | `avgRadius` (def) | PASS | §1.9: total list access and outward-rounded centres/radii/row sums; shapes prevent missing witness entries in successful certificates. |
| §1.9 / §F Average.lean:64 | `avgDefectUp` (def) | PASS | §1.9: total list access and outward-rounded centres/radii/row sums; shapes prevent missing witness entries in successful certificates. |
| §1.9 / §F Average.lean:72 | `avgDefectRows` (def) | PASS | §1.9: total list access and outward-rounded centres/radii/row sums; shapes prevent missing witness entries in successful certificates. |
| §1.9 / §F Average.lean:77 | `avgInvRows` (def) | PASS | §1.9: total list access and outward-rounded centres/radii/row sums; shapes prevent missing witness entries in successful certificates. |
| §1.9 / §F Average.lean:82 | `avgRadRows` (def) | PASS | §1.9: total list access and outward-rounded centres/radii/row sums; shapes prevent missing witness entries in successful certificates. |
| §1.9 / §F Average.lean:87 | `avgDegOk` (def) | PASS | §F / §1.9: exact-shape gates, degree-zero restriction and Neumann defect/target bound; conservative rejection, no unearned acceptance. |
| §1.9 / §F Average.lean:94 | `avgBoundsOk` (def) | PASS | §F / §1.9: exact-shape gates, degree-zero restriction and Neumann defect/target bound; conservative rejection, no unearned acceptance. |
| §1.9 / §F Average.lean:106 | `torsionAvgCheck` (def) | PASS | §F / §1.9: exact-shape gates, degree-zero restriction and Neumann defect/target bound; conservative rejection, no unearned acceptance. |
| §1.9 / §F Average.lean:119 | `listShapeOk_iff` (theorem) | PASS | §F / F7: exact row count and every row length; law-free shape contract matches signed header. |
| §1.9 / §F Average.lean:124 | `torsionAvgCheck_shape` (theorem) | PASS | §F / F7: exact row count and every row length; law-free shape contract matches signed header. |
| §1.9 / §F Average.lean:130 | `isZeroKeyN_iff` (theorem) | PASS | §1.9 average: zero mode means certKeyFun n k = 0; all duplicate/short/long keys interpreted consistently, rounded coefficient sum retained as a ball. |
| §1.9 / §F Average.lean:136 | `CertPoly.coeff_zero_eq` (theorem) | PASS | §1.9 average: zero mode means certKeyFun n k = 0; all duplicate/short/long keys interpreted consistently, rounded coefficient sum retained as a ball. |
| §1.9 / §F Average.lean:150 | `sum_torsionIdx` (theorem) | PASS | §F / F7: exact bordered index, range, injectivity, or exhaustive finite sum; includes the corner index n. |
| §1.9 / §F Average.lean:157 | `CertBall.mem_exact` (theorem) | PASS | §1.9 support: explicit ball membership and rounded norm bound for I-SC; no inverse assumption. |
| §1.9 / §F Average.lean:161 | `CertBall.mem_listSum_of` (theorem) | PASS | §1.9 support: explicit ball membership and rounded norm bound for I-SC; no inverse assumption. |
| §1.9 / §F Average.lean:177 | `norm_le_of_mem` (theorem) | PASS | §1.9 support: explicit ball membership and rounded norm bound for I-SC; no inverse assumption. |
| §1.9 / §F Average.lean:187 | `norm_sub_le_avgDefectUp` (theorem) | PASS | §1.9 support: explicit ball membership and rounded norm bound for I-SC; no inverse assumption. |
| §1.9 / §F Average.lean:222 | `avgBoundsOk_spec` (theorem) | PASS | §F / §1.9: exact-shape gates, degree-zero restriction and Neumann defect/target bound; conservative rejection, no unearned acceptance. |
| §1.9 / §F Average.lean:239 | `torsionIdx_injective` (theorem) | PASS | §F / F7: exact bordered index, range, injectivity, or exhaustive finite sum; includes the corner index n. |
| §1.9 / §F Average.lean:247 | `torsionAvgCheck_sound` (theorem) | PASS | §F signed contract: actual averaged full bordered matrix is invertible, inverse row sums ≤ σTμ; arbitrary supplied S, no added premise. |
| §1.9 / §F Models.lean:50 | `buildMat` (def) | PASS | §1.9 support: rectangular row-major list construction and in-range lookup; square shape produced exactly. |
| §1.9 / §F Models.lean:54 | `CertModel.negM` (def) | PASS | §1.9 support: exact coefficient negation, same degree/radius, enclosure of negative function. |
| §1.9 / §F Models.lean:58 | `modelMatMul` (def) | PASS | §1.9 matrix algebra: correct dimensions/signs, product-key routing, balanced sums and degree conversion; index equivalence covers the full inner carrier. |
| §1.9 / §F Models.lean:65 | `modelMatAdd` (def) | PASS | §1.9 matrix algebra: correct dimensions/signs, product-key routing, balanced sums and degree conversion; index equivalence covers the full inner carrier. |
| §1.9 / §F Models.lean:70 | `modelMatNeg` (def) | PASS | §1.9 matrix algebra: correct dimensions/signs, product-key routing, balanced sums and degree conversion; index equivalence covers the full inner carrier. |
| §1.9 / §F Models.lean:74 | `modelMatTranspose` (def) | PASS | §1.9 matrix algebra: correct dimensions/signs, product-key routing, balanced sums and degree conversion; index equivalence covers the full inner carrier. |
| §1.9 / §F Models.lean:79 | `modelMatOmega` (def) | PASS | §1.9 matrix algebra: correct dimensions/signs, product-key routing, balanced sums and degree conversion; index equivalence covers the full inner carrier. |
| §1.9 / §F Models.lean:84 | `ballModel` (def) | PASS | §1.9 frequency balls: centre s*c and radius |s|*r; valid for arbitrary rational s, including zero/negative s. |
| §1.9 / §F Models.lean:89 | `freqModel` (def) | PASS | §1.9 frequency balls: centre s*c and radius |s|*r; valid for arbitrary rational s, including zero/negative s. |
| §1.9 / §F Models.lean:93 | `dkModels` (def) | PASS | §1.9: models DK and D_(sω)DK from literal finite embedding derivatives, including angle/action degree factors. |
| §1.9 / §F Models.lean:99 | `d2kModel` (def) | PASS | §1.9: models DK and D_(sω)DK from literal finite embedding derivatives, including angle/action degree factors. |
| §1.9 / §F Models.lean:110 | `dkwModels` (def) | PASS | §1.9: models DK and D_(sω)DK from literal finite embedding derivatives, including angle/action degree factors. |
| §1.9 / §F Models.lean:117 | `gramInvRadius` (def) | PASS | §1.9: successful Gram certificate supplies genuine inverse; outward δβ/(1-δ) error, none on invalid scalar guards. |
| §1.9 / §F Models.lean:123 | `gramInvModels` (def) | PASS | §1.9: successful Gram certificate supplies genuine inverse; outward δβ/(1-δ) error, none on invalid scalar guards. |
| §1.9 / §F Models.lean:128 | `torsionSlots` (def) | PASS | §1.9 jet interface: d1 then row-major d2, valid slot bounds and compose soundness discharge all defaults; DX_H uses swapped Hessian row and Hamiltonian sign. |
| §1.9 / §F Models.lean:134 | `swapNat` (def) | PASS | §1.9 support: phase indices angle then action, swap and sum equivalence agree exactly. |
| §1.9 / §F Models.lean:138 | `dxhModels` (def) | PASS | §1.9 jet interface: d1 then row-major d2, valid slot bounds and compose soundness discharge all defaults; DX_H uses swapped Hessian row and Hamiltonian sign. |
| §1.9 / §F Models.lean:144 | `d1Models` (def) | PASS | §1.9 jet interface: d1 then row-major d2, valid slot bounds and compose soundness discharge all defaults; DX_H uses swapped Hessian row and Hamiltonian sign. |
| §1.9 / §F Models.lean:152 | `torsionModels` (def) | PASS | §F signed producer: exact (n+1) shape, literal torsion enclosure for every boxed ω, continuity; all source premises unchanged. |
| §1.9 / §F Models.lean:187 | `buildMat_entry` (theorem) | PASS | §1.9 support: rectangular row-major list construction and in-range lookup; square shape produced exactly. |
| §1.9 / §F Models.lean:192 | `buildMat_lookup` (theorem) | PASS | §1.9 support: rectangular row-major list construction and in-range lookup; square shape produced exactly. |
| §1.9 / §F Models.lean:197 | `buildMat_hasShape` (theorem) | PASS | §1.9 support: rectangular row-major list construction and in-range lookup; square shape produced exactly. |
| §1.9 / §F Models.lean:205 | `ModelMatrix.EntryEncloses` (def) | PASS | Internal support predicate/transport, distinctly named; assumes entry enclosures only for compositional helpers, proved at the producer boundary. |
| §1.9 / §F Models.lean:209 | `phaseNat_finSumFinEquiv_symm` (theorem) | PASS | §1.9 support: phase indices angle then action, swap and sum equivalence agree exactly. |
| §1.9 / §F Models.lean:215 | `phaseNat_lt_add` (theorem) | PASS | §1.9 support: phase indices angle then action, swap and sum equivalence agree exactly. |
| §1.9 / §F Models.lean:221 | `CertModel.Encloses.of_eqOn` (theorem) | PASS | Internal support predicate/transport, distinctly named; assumes entry enclosures only for compositional helpers, proved at the producer boundary. |
| §1.9 / §F Models.lean:225 | `CertModel.Encloses.negM` (theorem) | PASS | §1.9 support: exact coefficient negation, same degree/radius, enclosure of negative function. |
| §1.9 / §F Models.lean:237 | `ModelMatrix.EntryEncloses.modelMul` (theorem) | PASS | §1.9 matrix algebra: correct dimensions/signs, product-key routing, balanced sums and degree conversion; index equivalence covers the full inner carrier. |
| §1.9 / §F Models.lean:268 | `ModelMatrix.EntryEncloses.modelAdd` (theorem) | PASS | §1.9 matrix algebra: correct dimensions/signs, product-key routing, balanced sums and degree conversion; index equivalence covers the full inner carrier. |
| §1.9 / §F Models.lean:277 | `ModelMatrix.EntryEncloses.modelNeg` (theorem) | PASS | §1.9 matrix algebra: correct dimensions/signs, product-key routing, balanced sums and degree conversion; index equivalence covers the full inner carrier. |
| §1.9 / §F Models.lean:286 | `ModelMatrix.EntryEncloses.modelTranspose` (theorem) | PASS | §1.9 matrix algebra: correct dimensions/signs, product-key routing, balanced sums and degree conversion; index equivalence covers the full inner carrier. |
| §1.9 / §F Models.lean:294 | `ModelMatrix.EntryEncloses.modelOmega` (theorem) | PASS | §1.9 matrix algebra: correct dimensions/signs, product-key routing, balanced sums and degree conversion; index equivalence covers the full inner carrier. |
| §1.9 / §F Models.lean:316 | `dkModels_encloses` (theorem) | PASS | §1.9: models DK and D_(sω)DK from literal finite embedding derivatives, including angle/action degree factors. |
| §1.9 / §F Models.lean:331 | `gramInvModels_encloses` (theorem) | PASS | §1.9: successful Gram certificate supplies genuine inverse; outward δβ/(1-δ) error, none on invalid scalar guards. |
| §1.9 / §F Models.lean:341 | `gramInvRadius_spec` (theorem) | PASS | §1.9: successful Gram certificate supplies genuine inverse; outward δβ/(1-δ) error, none on invalid scalar guards. |
| §1.9 / §F Models.lean:364 | `freqModel_encloses` (theorem) | PASS | §1.9 frequency balls: centre s*c and radius |s|*r; valid for arbitrary rational s, including zero/negative s. |
| §1.9 / §F Models.lean:392 | `d2kModel_encloses` (theorem) | PASS | §1.9: models DK and D_(sω)DK from literal finite embedding derivatives, including angle/action degree factors. |
| §1.9 / §F Models.lean:405 | `dkwModels_encloses` (theorem) | PASS | §1.9: models DK and D_(sω)DK from literal finite embedding derivatives, including angle/action degree factors. |
| §1.9 / §F Models.lean:438 | `torsionSlots_length` (theorem) | PASS | §1.9 jet interface: d1 then row-major d2, valid slot bounds and compose soundness discharge all defaults; DX_H uses swapped Hessian row and Hamiltonian sign. |
| §1.9 / §F Models.lean:442 | `torsionSlots_getD_d1` (theorem) | PASS | §1.9 jet interface: d1 then row-major d2, valid slot bounds and compose soundness discharge all defaults; DX_H uses swapped Hessian row and Hamiltonian sign. |
| §1.9 / §F Models.lean:447 | `torsionSlots_getD_d2` (theorem) | PASS | §1.9 jet interface: d1 then row-major d2, valid slot bounds and compose soundness discharge all defaults; DX_H uses swapped Hessian row and Hamiltonian sign. |
| §1.9 / §F Models.lean:457 | `swapNat_phaseNat` (theorem) | PASS | §1.9 support: phase indices angle then action, swap and sum equivalence agree exactly. |
| §1.9 / §F Models.lean:466 | `SlotsEnclose` (def) | PASS | §1.9 jet interface: d1 then row-major d2, valid slot bounds and compose soundness discharge all defaults; DX_H uses swapped Hessian row and Hamiltonian sign. |
| §1.9 / §F Models.lean:471 | `dxhModels_encloses` (theorem) | PASS | §1.9 jet interface: d1 then row-major d2, valid slot bounds and compose soundness discharge all defaults; DX_H uses swapped Hessian row and Hamiltonian sign. |
| §1.9 / §F Models.lean:504 | `d1Models_encloses` (theorem) | PASS | §1.9 jet interface: d1 then row-major d2, valid slot bounds and compose soundness discharge all defaults; DX_H uses swapped Hessian row and Hamiltonian sign. |
| §1.9 / §F Models.lean:530 | `torsion_eq_models` (theorem) | PASS | §F signed producer: exact (n+1) shape, literal torsion enclosure for every boxed ω, continuity; all source premises unchanged. |
| §1.9 / §F Models.lean:551 | `torsionModels_sound` (theorem) | PASS | §F signed producer: exact (n+1) shape, literal torsion enclosure for every boxed ω, continuity; all source premises unchanged. |
| §8 Torsion.lean:41 | `torsTestW` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:43 | `torsTest_weight` (theorem) | PASS | §8: decide +kernel positive/negative controls; border-only invertibility, bad witness/target/degree/radius and F7 dimensions. |
| §8 Torsion.lean:45 | `torsTestPi` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:47 | `torsTest_pi` (theorem) | PASS | §8: decide +kernel positive/negative controls; border-only invertibility, bad witness/target/degree/radius and F7 dimensions. |
| §8 Torsion.lean:52 | `torsTestConst` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:54 | `torsTestMat` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:57 | `torsTestCC` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:59 | `torsTestSwap` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:62 | `torsTest_border` (theorem) | PASS | §8: decide +kernel positive/negative controls; border-only invertibility, bad witness/target/degree/radius and F7 dimensions. |
| §8 Torsion.lean:66 | `torsTest_failClosed` (theorem) | PASS | §8: decide +kernel positive/negative controls; border-only invertibility, bad witness/target/degree/radius and F7 dimensions. |
| §8 Torsion.lean:78 | `torsTestA3` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:81 | `torsTest_F7` (theorem) | PASS | §8: decide +kernel positive/negative controls; border-only invertibility, bad witness/target/degree/radius and F7 dimensions. |
| §8 Torsion.lean:91 | `torsTestCfg` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:100 | `torsTestCos` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:103 | `torsTestK` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:106 | `torsTestH` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:109 | `torsTestB` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:112 | `torsTestWit` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:114 | `torsTestBox` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:117 | `torsTestS` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:119 | `torsTestModels` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:123 | `torsTestRun` (def) | PASS | §8 test fixture: explicit rational finite data/wrappers, no assumed correctness; direct advice and intended malformed controls. |
| §8 Torsion.lean:128 | `torsTest_pipeline` (theorem) | PASS | §8: decide +kernel positive/negative controls; border-only invertibility, bad witness/target/degree/radius and F7 dimensions. |
| §8 Torsion.lean:130 | `torsTest_pipelineFail` (theorem) | PASS | §8: decide +kernel positive/negative controls; border-only invertibility, bad witness/target/degree/radius and F7 dimensions. |
| §8 Torsion.lean:134 | `torsTest_sound` (theorem) | PASS | §8: both contracts instantiated for toy; end-to-end inverse bound ≤ 4 for every boxed frequency, no torus-existence claim. |
| §8 Torsion.lean:149 | `torsTest_endToEnd` (theorem) | PASS | §8: both contracts instantiated for toy; end-to-end inverse bound ≤ 4 for every boxed frequency, no torus-existence claim. |

## Definition carriers and failure behavior

The table classifies all 57 new definitions. There are no new types with hidden proof fields. The only predicates, `ModelMatrix.EntryEncloses` and `SlotsEnclose`, transparently describe enclosure/slot data; they are internal intermediate interfaces discharged from existing soundness theorems, not added signed hypotheses.

List and natural-index operations are total with documented defaults. `ccEntry` returns zero if absent; `modelMatrixEntry` returns its existing default model; missing polynomial/embedding entries use the pre-existing zero semantics; jet slot access uses zero defaults. These are not used to erase a required mathematical entry: the public successful certificate first checks both exact square shapes; the producer builds every bordered entry; `buildMat_lookup` witnesses actual presence for its exported `ModelMatrix.Encloses`. Jet access is proved in bounds using the exact composition-result length and `torsionSlots_getD_d1/d2`. Helpers using `EntryEncloses` refer explicitly to total model lookup, so their claims are valid on that carrier even without a separate rectangular-shape premise. `swapNat` is intentionally a natural-index extension of coordinate swap, with its finite-index contract proved separately. Truncated natural subtraction/division outside valid indices is never substituted for a mathematical derivative.

Rounded constructions represent enclosures, not exact complex functions for arbitrary malformed arithmetic data. Their contracts require the existing `LawfulCertArith` laws, validated weights/π where needed, and actual frequency enclosure. `ballModel`/`freqModel` pay conversion error and use `|s|r`; negative s is supported by the theorem. `gramInvRadius` returns none if δ or β is negative, δ≥1, or the reciprocal enclosure fails. Its finite successful branch bounds the genuine Gram inverse deviation. `torsionModels` returns none on that failure or a failed composition; successful construction alone does not bypass its signed source/Gram hypotheses.

Degree-zero restriction: `Average.lean:87–109` rejects entries of nonzero degree, because this signed check has no π-enclosure argument. The Python mirror normalizes them instead. This is a documented conservative algorithmic deviation, not a type or soundness change: all producer output entries have degree zero (product outputs use `toDeg 0`, frequency and corner models also have degree zero). Arbitrary valid enclosures need not be accepted by a sufficient certificate check. The F7 dimensions and full bordered inverse remain exact. The other handoff deviations—three-module split, outward second-derivative rounding, generic product radii, balanced sums, fail-closed Gram guards, rounded zero-mode/defect balls and algebraic form of the final inverse bound—are visible in the implementation and consistent with the contracts. `Models` publicly re-exports `Average`, preserving the design interface.

## Independent checks and exact receipts

All Lean invocations were serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`; lint's ABI Lean probe ran only after kernel replay completed. No heartbeat, recursion or synthesis budget override was used. The scratch probes stayed under this worktree's `.lake/abi-scratch/` and were deleted after their results were incorporated into this report.

Targeted gated build (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sotors KAM.Certificate.Torsion.Frame KAM.Certificate.Torsion.Average KAM.Certificate.Torsion.Models KAM.Certificate.Tests.Torsion
```

```text
[inp-gate] slot 1 acquired 21:13:59 for KAM.Certificate.Torsion.Frame KAM.Certificate.Torsion.Average KAM.Certificate.Torsion.Models KAM.Certificate.Tests.Torsion
⚠ [2839/2881] Replayed KAM.Certificate.Arith.PiHigh
warning: KAM/Certificate/Arith/PiHigh.lean:218:8: This simp argument is unused:
  Nat.succ_eq_add_one
⚠ [2950/2984] Replayed KAM.Certificate.Expr.Basic
warning: KAM/Certificate/Expr/Basic.lean:85:5: Variable name `hS` is not explicitly referenced.
Build completed successfully (2984 jobs).
```

The two warnings are in unchanged dependency files, not the four audited modules. The build reused valid artifacts; fresh test elaboration and kernel replay below provide independent proof checks.

Exact headers and explicit applications (exit 0, no errors or warnings in the final probe):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOTorsAudit.lean
```

The generated probe imported `KAM.Certificate.Tests.Torsion`, opened the certificate and matrix namespaces, and used a noncomputable scratch section. For each signed declaration it copied the signed header under `KAM.Certificate.SOAudit.expected_<name>`, with body `KAM.Certificate.<name> <explicit arguments from the table>`. For each it checked both:

```lean
example : type_of% @expected_<name> := @KAM.Certificate.<name>
example : type_of% @KAM.Certificate.<name> := @expected_<name>
```

The header comparison printed `HEADER EXACT` for all six exports. Every new theorem received `#print axioms`; the full output is below. This is an actual Lean type/application check, not merely a textual signature comparison.

Kernel replay, one invocation (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Torsion.Frame KAM.Certificate.Torsion.Average KAM.Certificate.Torsion.Models KAM.Certificate.Tests.Torsion
```

```text
replaying KAM.Certificate.Tests.Torsion
replaying KAM.Certificate.Torsion.Models
replaying KAM.Certificate.Torsion.Average
replaying KAM.Certificate.Torsion.Frame
```

Repository lint (exit 1, **only the expressly permitted generated-root exception**):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1360 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The generated root was not edited. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` emitted nothing (exit 0); the package's protected paths are unchanged. `git diff --check inp...HEAD` emitted nothing (exit 0).

Short-name check (exit 0):

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-sotors KAM.Certificate.Torsion.Frame KAM.Certificate.Torsion.Average KAM.Certificate.Torsion.Models KAM.Certificate.Tests.Torsion
```

```text
short-name check OK (no reused public short name)
```

Every new declaration is under `KAM.Certificate` (including its nested model namespaces); no new root declaration or harmful shadow was found. All files have copyright, module, public imports, module docstring and public section. Body-unfolding definitions in the production modules are in `@[expose] public noncomputable section`; test data are in their public test module.

| File | Total lines | Maximum Unicode line length |
|---|---:|---:|
| `KAM/Certificate/Torsion/Frame.lean` | 382 | 100 |
| `KAM/Certificate/Torsion/Average.lean` | 362 | 100 |
| `KAM/Certificate/Torsion/Models.lean` | 633 | 99 |
| `KAM/Certificate/Tests/Torsion.lean` | 163 | 100 |

A scoped `rg -n` scan for `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `native_decide`, `ofReduceBool`, `elab`, `macro`, `run_cmd`, `addDecl`, `implemented_by`, `extern`, `EuclideanSpace`, `set_option`, and heartbeat/recursion/synthesis overrides returned no matches (rg exit 1). Inspection and repository lint corroborated the result.

Recursive source-import inspection reached 80 KAM modules, including 18 frozen modules, all manifest `SEALED` definitions. No provider and no DRAFT frozen theorem appeared. The frozen paths are `KAM/Frozen/Defs/{ActionNbhd,ComplexStrip,DotC,FrequencyMap,GramMatrix,HamiltonianVectorField,HamiltonianVectorFieldC,InvarianceError,IsDiophantine,IsPrimaryOnStrip,IsRealOnReals,NormalFrame,OmegaZero,RealHamiltonian,Torsion,TorsionAverage}.lean` and `KAM/Frozen/Iso/Defs/{ExtendedTorsion,ExtendedTorsionAverage}.lean`.

## Axiom output, every new public theorem

Command: the signature/application probe above, with one `#print axioms KAM.Certificate.<name>` for each of the 65 public theorems in the declaration table. No `sorryAx` or nonstandard axiom occurs.

```text
'KAM.Certificate.torsionIdx_lt' does not depend on any axioms
'KAM.Certificate.fderiv_tangentMat_eq_sum_partials' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.fderiv_normalMat_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.differentiableOn_torsion_of_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.fderiv_apply_normalFrame' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sqMat_apply_eq_phaseBasis' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.linMat_apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.continuousOn_extendedTorsion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.hasFDerivAt_charSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.fderiv_fderiv_eval_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.differentiable_fderiv_eval_single' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.tangentMat_eval_inl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.tangentMat_eval_inr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.fderiv_tangentMat_eval_inl' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.fderiv_tangentMat_eval_inr' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_deriv2Coeff_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.deriv2Items_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.Encloses.ofDeriv2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.listShapeOk_iff' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.torsionAvgCheck_shape' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.isZeroKeyN_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.coeff_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sum_torsionIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertBall.mem_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertBall.mem_listSum_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_le_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_sub_le_avgDefectUp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.avgBoundsOk_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsionIdx_injective' does not depend on any axioms
'KAM.Certificate.torsionAvgCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.buildMat_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.buildMat_lookup' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.buildMat_hasShape' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.phaseNat_finSumFinEquiv_symm' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.phaseNat_lt_add' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.CertModel.Encloses.of_eqOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.Encloses.negM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ModelMatrix.EntryEncloses.modelMul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ModelMatrix.EntryEncloses.modelAdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ModelMatrix.EntryEncloses.modelNeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ModelMatrix.EntryEncloses.modelTranspose' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ModelMatrix.EntryEncloses.modelOmega' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.dkModels_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.gramInvModels_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.gramInvRadius_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.freqModel_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.d2kModel_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.dkwModels_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsionSlots_length' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.torsionSlots_getD_d1' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.torsionSlots_getD_d2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.swapNat_phaseNat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.dxhModels_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.d1Models_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsion_eq_models' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsionModels_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_border' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_failClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_F7' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_pipeline' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_pipelineFail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.torsTest_endToEnd' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Fresh kernel-reduction tests

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOTorsTests.lean
```

Exit 0; stdout/stderr empty. The probe copied the complete 163-line test source into the fresh namespace `KAM.Certificate.SOAuditTests` with the same imports and proof bodies. Thus all nine public test theorems were elaborated anew, including the `decide +kernel` proofs, rather than accepted solely from a cached build. The pipeline success at 4 and failure at 3, border-only inverse example, four bad witness/target/degree/radius controls, and F7 larger-matrix controls all passed. Both soundness contracts and the end-to-end frequency-uniform theorem also elaborated.

Three additional independent controls, all `by decide +kernel`, passed:

```lean
open KAM.Certificate KAM.Certificate.SOAuditTests in
example : torsionAvgCheck 1 [[torsTestConst 0 0], [torsTestConst 1 0, torsTestConst 0 0]]
    (torsTestCC torsTestSwap) 100 = false := by decide +kernel
open KAM.Certificate KAM.Certificate.SOAuditTests in
example : torsionAvgCheck 1 (torsTestMat torsTestSwap 0) (torsTestCC [[0, 1], [1]]) 100 = false :=
  by decide +kernel
open KAM.Certificate KAM.Certificate.SOAuditTests in
example : torsionAvgCheck 1 (torsTestMat torsTestSwap 0) (torsTestCC torsTestSwap) (-1) = false :=
  by decide +kernel
```

These check wrong individual row lengths independently of the existing F7 wrong-row-count controls and reject an impossible negative inverse bound.

## Notes, uncertainties and errata

- **Generated root:** the sole lint failure is the brief's explicitly allowed `KAM.lean is out of date`; protected-path comparison is empty. Regeneration belongs to the orchestrator.
- **Dependency warnings:** the independent build replayed two existing linter warnings in `Arith/PiHigh` and `Expr/Basic`; the scoped modules generated no warning. This qualifies the handoff's historical “No warning” build statement, without changing its mathematical result.
- **Conservative checks / documented deviations:** degree-zero restriction, rounding/degree normalization, balanced sums, negative-s radius correction and module split are as analyzed above. They do not change signed types or create a proof gap. No audit-introduced implementation deviation occurred: only this report was added.
- **Scale:** tests exercise n=1 and the n=2 F7 matrix, not the full lunar certificate. Lunar-scale reduction cost and eventual SO-SOUND/SO-DATA assembly remain unmeasured here; this audit establishes reusable contracts, not the physical confinement theorem or headline closure.
- **Source / blueprint / frozen defects:** none found in this slice. No false or altered frozen statement, contradictory blueprint step, source-sign substitution, or missing producer-to-consumer mathematical premise was identified. No new errata-ledger entry is proposed. The generic request to inspect provider sealing is inapplicable to this infrastructure package, as explained above; frozen theorem files were not modified.

Final validation: the only worktree change is this exact report path; targeted build, exact signed applications, all 65 axiom probes, four-module kernel replay, fresh kernel tests, short-name check, protected-path comparison and whitespace checks passed. Lint's one permitted exception is recorded verbatim. Audit scratch files were removed; no state-changing git command was used.
