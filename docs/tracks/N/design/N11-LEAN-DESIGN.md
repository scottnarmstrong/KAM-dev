# N11 Lean design: stopped partial-convex Nekhoroshev

Design draft, 2026-10-28, branch `inp-design-n11`. Scope: every graph node with statement or proof source in
`blueprint-N/parts/p11a-partial-route.tex`, `p11b-partial-nf.tex`, `p11c-partial-stability.tex`, including the
frozen root `bpN:p0:partial`. This is an implementation design, not a mathematical audit or a proof closure.
The untracked delivery path is `/root/code/KAM-inp/.drafts/design/N11Signatures.lean`;
Appendix A is the exact elaboration target. Every theorem body is `sorry`; definitions have literal bodies.

## Snapshot fingerprints

These are source-text pins, distinct from the shared build used for elaboration.

| File | SHA-256 |
|---|---|
| `blueprint-N/parts/p11a-partial-route.tex` | `dede87e5ec7b638136dff072abbf021b24ed4a4cedf6befae88eddf6e87d57b3` |
| `blueprint-N/parts/p11b-partial-nf.tex` | `4005a51b99ed21cba7c6cbca27b8e70392f9d8d6c67d6b59fec9e25cac51232d` |
| `blueprint-N/parts/p11c-partial-stability.tex` | `5d6fe7fc6b09459b6bf307596832695fcda1b62bf5292bd926d84bf216f7b7ea` |
| `docs/graph/N/DEPGRAPH.md` | `941c8d1d4bb6c17e3369d57b86441798544e1dabc8a9af1735882f75aa8972d2` |
| `KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean` | `e6bb9443a34096433a84e3450162ed032b07d934352c7ecaaa10eb7caf16b4a3` |

The exact copied N6–7 Revision-2 carrier/core definitions are present in Appendix A; the live upstream signature file may continue to change.

## Revision 2

Resolves independent audit 1 (FAIL); these are interface repairs, not proof closure.

| Finding | Resolution and implementation owner |
|---|---|
| F1 (major) | `energy_free` now assumes `RealFastConvex`, whose upper Hessian bound quantifies only over real actions. `FastConvex` retains its complex bound for `resonant`/domain. N11-E3 proves `FastConvex.toRealFastConvex` by real/complex Hessian transport; N11-M2 uses this bridge before N11-L2. Energy has no complex Hessian premise. |
| F2 (major), canonical_map | Both Φ and Ψ explicitly map the intermediate domain U into Dom(R−ρ,s−σ). N11-F2 exports the inverse image clause. |
| F2 (major), iterative | N11-H exports holomorphy and image inclusion on Dom(R−3ρ/2,s−3σ/2), integer-angle equivariance there, and the actual negative-time flow left inverse on Dom(R−2ρ,s−2σ). N11-K1/K2 consume these exports when composing nested maps. All earlier estimates and witnesses remain. |
| F2 (major), real_system | N11-D exports integer-angle periodicity of the real weighted vector field, in addition to scalar periodicity. N11-J2 uses it for periodic continuation. |
| F3 (medium) | `real_system_resonant` assumes `InClass`, with no reality clause, and exports span membership of both real and imaginary angular derivative vectors. The energy consumer takes the first conjunct; complex observables retain the full source assertion. |
| F4 (medium) | Threshold/reuse and graph inventory use root `tendsto_exp_div_rpow_atTop` (or root `tendsto_exp_mul_div_rpow_atTop` with positive multiplier), from `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`. |
| N1 | N11-G remains blocked on reconciliation with actual Part-8 covering/cutoff signatures for all four listed geometric inputs; no upstream statement is invented. Remove the twelve exact N6–7 staging definitions when owner modules land. |
| N2 | Required imports are explicit below and in Appendix A. The equal-size `KAM.hamiltonian_real_fderiv` is only a proof pattern: N11-D supplies regrouping and local derivative transport on EC n k, without a replacement-field equality hypothesis. |
| N3 | Preserve the open-ball interpretation at C L31 and report the stale adjoint locator B L69–86 (actual end L73); both remain in the issue list and handoff. No source or graph edits. |

Implementation import closure: `KAM.Weighted.SupWeighted` for sup/weighted conversion,
`KAM.Weighted.Algebra` for algebra estimates, `KAM.ODE.Continuation` for `gen_continuation`,
and `Mathlib.Analysis.Complex.ExponentialBounds` for `Real.exp_one_lt_d9`.
`KAM.Canonical.FlowRegular` and `KAM.Canonical.FlowInverse` remain explicit N11-E1 imports.
N11-O imports the asymptotics module for both root-level limit declarations. No additional source
premise is introduced by any repair; the provider declaration remains byte-identical to the frozen type.

## Decisions

1. Follow route (ii), with a local extended weighted bracket and a frequency-free energy argument. Do not
   use Nek77's unavailable Part-II proofs, add a frequency upper bound, or import the ordinary Part-9 stability theorem.
2. Use the existing Part-4 weighted representation with independent base dimension. The coordinates are
   `EC n k = (Fin n → ℂ) × (Fin (n+(k+k)) → ℂ)`, ordered θ then I,q,p. This is a type abbreviation,
   with Mathlib's ordinary max norms. There is no second analytic class or coefficient representation.
3. Freeze λ=w/rB and c=2π/λ² once per block. An iterative radius R changes the tube, never λ or c.
   Separate the physical coordinates used by `block` from the scaled coordinates used by `nf`.
4. Reuse Part-5 `flow` and `SmallField` directly for existence/regularity/inversion; prove the weighted
   symplectic argument locally. `flow_e` requires a real-preserving coordinate regrouping (audit R2-02),
   recorded explicitly as `flow_real`. It does not apply verbatim on this unequal product.
5. `transfer_conditional` is an explicitly conditional helper with source premise T3. It is never the
   source-facing nonresonant or resonant result. Those propositions prove T3; the provider assumes none of it.
6. Preserve the frozen slow margin μ^b, the stopped quantifiers, empty-G branch, global sign and supplied
   solution interval. Only the fast angles are divided by 2π; time is unchanged.
7. All statements are internal design targets. No frozen file, manifest, graph, source or production Lean file is changed.
   Use the exact provider export `KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev` below the anchor.

Every future Lean brief repeats the repository hard rules verbatim:

1. **Never use `set_option maxHeartbeats`** (or any heartbeat-budget override). A default-heartbeat elaboration
   failure is a design signal to refactor or split the proof, not something to mask with a larger budget. If a
   proof will not elaborate at default heartbeats, report it as a design signal.
2. **No Lean file may exceed 1500 lines of code.** When a file approaches the cap, split it into focused modules,
   preserving public import paths as cheap facades.
3. **Every `.lean` file is a Lean module**: copyright comment, `module`, imports (`public import` for the
   interface), module docstring, `public section`. Expose (`@[expose]`) definitions whose bodies must unfold.
4. **No `axiom`, `admit`, `unsafe`, `opaque`; `sorry` only** as the manifest-bound body of a frozen statement in
   `KAM/Frozen/`. No recursion-depth or synthesis-heartbeat overrides either.
5. **Frozen files are read-only.** Never edit anything under `KAM/Frozen/` or `manifest/`. If a frozen
   declaration looks wrong, stop and report; never add a premise or substitute a helper.
6. **No conclusion-shaped hypotheses.** A theorem may assume only source premises, standing assumptions, typing
   data and explicit owner rulings. Conditional helpers get distinct names and never stand in for a source result.
7. **Ambient types:** `Fin n → ℝ`, `Fin n → ℂ`, Fourier indices `Fin n → ℤ`. Never `EuclideanSpace`.
8. **Builds:** one targeted `nice -n 5 lake build <Module>` at a time; never `lake clean`; never rebuild the
   library from scratch in a worktree (worktrees use a copy-on-write overlay on `main`'s build snapshot). A wait
   on the compile gate is expected, not a hang.
9. **Providers are quarantined.** `KAM/Provider/<Name>.lean` proves its frozen theorem as `KAM.Provider.<name>`;
   no module except the frozen anchor may import a provider or a `DRAFT_SORRY` anchor (the root file skips them).
10. **Never edit `README.md`** (generated) or `KAM.lean` (generated by `scripts/gen_root_imports.py`).
11. **Errata:** report every suspected defect in a pinned source (location, quoted text, why it is wrong) in your
    handoff; the orchestrator records it in `docs/errata/ledger.json`. Deviations you introduce are reported too.


## Carriers, definitions and conventions

| Object | Exact interface | Meaning |
|---|---|---|
| Extended complex/real phase | `Ext`, `EC`, `ER` | θ × (I,q,p), all coordinates `Fin _ → ℂ/ℝ` |
| Projections | `fastAction`, `slowPair` | `Fin.castAdd`/`Fin.natAdd`; no coercion-based reordering |
| Real locus | `extCx`, `extRe`, `extReal` | inclusion/real part; extReal aliases exact `RealOnParam`; no equality premise with a replacement frozen object |
| Block geometry | `PartialBlock`, `.lam`, `.c`, `.base` | singleton Ic × λ⁻¹S embedded into the weighted base |
| Analytic domain/class/norm | `KAM.Weighted.Dom`, `InClass`, `WBound` | exactly the existing independent-dimension definitions |
| Real domain | `PartialBlock.realDom` | preimage of `Dom ... R 1`; on real angles every positive width gives the same set |
| Real restriction/orbits | `realHamiltonianExt`, `ExtOrbit` | restriction with zero off-domain; existing `KAM.ODE.IsSolutionIn`, two-sided derivatives |
| Weighted field and bracket | `wfield`, `realWfield`, `extBracket` | Du·Xv; fast weight 1, slow weight c; sign +,-,+,- |
| Normal-form iterates | `extAd`, `extFlow` | finite recursive brackets; the existing canonical flow |
| Canonical condition | `ExtCanonical` | DΨ Ωc DΨᵀ=Ωc tested on every pair of complex linear functionals |
| Euclidean size | existing `KAM.Nekhoroshev.euclid` | sqrt of sum of coordinate norm squares; never a global inner-product instance |
| Resonant span | existing designed `KAM.Stability.resSpan` | literal real span of integer frequencies |
| Fast Hessian assumptions | `RealFastConvex`, `FastConvex`, `FastConvex.toRealFastConvex` | real-slice upper bound for energy; complex upper bound for resonant/domain; extraction proved in Hessian |
| Resonance closeness | `NearResonance` | dual expression of projection norm ≤δ: absolute pairing with every v in span ≤δ|v|₂ |
| Allowed transfer sizes | existing designed `KAM.Stability.IsActionNorm` | covers max norm and `euclid`, no new norm instance |
| Source data | `PartialData` | the exact frozen premises as fields, no stability or normal-form conclusion |
| Numerical data | `PartialConstants`, `constants` | formulas of 11a L79–83, independent of μ,P,C,z,t |
| Physical/scaled perturbations | `signedF`, `slowScale`, `blockPert` | σμP/(2π), then x=λx̃; no action or time scaling |

Widths are geometric; Fourier weight is exp(2πs|j|₁), angles period one. All coefficient-reading derivative
statements carry positive strip width. `WBound` carries summability, and explicit nonnegative numerical
bounds are supplied where arithmetic requires them, including empty base sets. `ExtCompose`, `ExtNFHyp`,
`RealFastConvex`, `FastConvex`, `ExtConjHyp`, `DefiniteSign` expand only source assumptions or a named conditional map contract.
In `resonant`, the normal-form perturbation smallness is derived from ε≤mr²/2¹⁴, not packaged as a premise.
The `nf` theorem receives that source smallness separately. No global instances are installed.

The two short upstream stub namespaces in Appendix A contain **verbatim definitions/types** from
`NPart67Signatures.lean`: `KAM.NormalForm.{zBall,freq,dotC,conjExp,IsNonresonant,FreqLipschitz,DivisorBound,homGenParam,homResParam,RealOnParam}`
and `KAM.Stability.{resSpan,IsActionNorm}`. Full qualification of `polyNbhd` is the only lexical difference.
They are staging copies, never new owners: delete them and import their owner modules when those land.
Already implemented weighted declarations are imported, never copied.

## Reuse map and upstream interface (to reconcile)

| Graph input / consumer | Exact owner declarations | Hypotheses supplied / conclusion consumed |
|---|---|---|
| Part 4 / ext-part4, bracket, hom, domain | `KAM.Weighted.{Dom,InClass,WBound,coeff,coefficients_deriv,coefficients_repr,coeff_differentiableOn,sup_le_wbound,wbound_of_sup_bound,wbound_mul,cauchy_theta,cauchy_action,general_cauchy,projections,truncation_tail,projMode,truncate}` | instantiate base dimension n+(k+k), base b.base; same constants; sum angular derivatives at fixed base before taking sup |
| Part 5 / flow, symplectic, canonical-map | `KAM.Canonical.{flow,SmallField,gaugeInterior,flow_a,flow_b,flow_c,flow_d,flow_e}` | three-block gauge, holomorphic small field; a–d generic directly, e by regrouping and uniqueness; c gives inverse and derivative estimates |
| Part 3 / continuation, transfer | `KAM.ODE.{IsSolutionIn,IsMaximalSolution,gen_maximal,gen_uniqueness,gen_continuation,gen_uniform_exist}` | real C1 periodic field on ℝⁿ×U; compact transverse tail; generalize the proof of `gen_continuation_periodic` to independent N |
| Part 1 / hessian, domain | `KAM.Nekhoroshev.{euclid,norm_le_euclid}`, `KAM.holomorphic_regularity_of_finiteDimensional`, `KAM.hamiltonian_real_fderiv` | finite-coordinate Cauchy/real restriction; `hamiltonian_real_fderiv` is an equal-size proof pattern only: N11-D proves unequal-carrier derivative transport locally using regrouping, never an equality premise; use arbitrary-open-domain arguments |
| Part 6 / hom, nf | `KAM.NormalForm.{freq,dotC,IsNonresonant,FreqLipschitz,DivisorBound,divisor,starNorm,homological_param,homGenParam,homResParam,RealOnParam}` | Revision-2 exact signatures, independent base dimension; singleton fast base, real frequencies; **do not** apply canonical n=n homological theorem on unequal extended coordinates |
| Part 6 / nf composition | graph `bpN:p6:telescope`, owners `KAM.NormalForm.telescope`, `KAM.NormalForm.chain` | componentwise displacement telescoping; source-inspected generalization to extended coordinate space, no full upstream restatement invented here |
| Part 7 / real-system, energy-free | `KAM.Stability.{resSpan,IsActionNorm,isActionNorm_norm,isActionNorm_euclid,exit_ball}` | exact existing designed carriers; repeat fixed-base Fourier argument for extended base. `no_exit` and `energy_core` do not apply to slow-dependent Hamiltonians |
| Part 8 / block-data | graph `bpN:p8:covering`, reserved `KAM.Nekhoroshev.covering` | singleton {Ic}; p=9/8,b=1/32,r0,M1,m1,K,A; need radius bounds, block membership, strict span-projection closeness, full-rank block exclusion |
| Part 8 / block-data | graph `bpN:p8:cutoffs`, reserved `KAM.Nekhoroshev.cutoffs` | Kgeom=K, Kanalytic=K/√n; consume divisors for ℓ¹ cutoff, not Euclidean cutoff K |
| Part 9 / constants | graph `bpN:p9:setting`, `bpN:p9:elementary` | provenance only; formulas and elementary inequalities rederived locally with b=1/32, not Part 9's b=1/8 contract |
| Numeric / threshold | `Real.{rpow_add,rpow_neg,rpow_lt_rpow_of_exponent_gt}`, root `tendsto_exp_div_rpow_atTop`, `tendsto_exp_mul_div_rpow_atTop` | positive μ, positive exponent gaps; exp dominates each polynomial |
| Chain / orbit | `HasFDerivAt.comp`, `HasFDerivAt.hasDerivAt` (via curve composition), `HasDerivAt.comp` | explicit coordinate linear equivalence and frozen differentiability guard |

The N6–7 Revision-2 update arrived during this design. Its F1 correction supplies `map_zero` and
`smul` in the exact `IsActionNorm` copied in Appendix A. Its F3 correction supplies `homological_param`:
instantiate m=n+(k+k), D=b.base, frequency J↦freq h (fast projection J), q≥1, α>0, s>0, K≥0,
frequency holomorphy and the supplied divisor bound. Consume class, support, directional equation,
resonant part, norm bounds and reality by their exact existing signature. `homGenerator` is just
`homGenParam` specialized to that frequency. The remaining N11 bridge proves holomorphy of this
projected frequency and identifies its directional derivative with the extended bracket. The original
canonical homological theorem is not used on an incompatible carrier. Part-6 telescope is still
canonical-coordinate-specific; N11-K2 generalizes its finite-map proof locally, rather than applying it unchanged.

Part 8 is concurrent and its full statement is intentionally not fabricated.
N11-G is BLOCKED until the owner signatures explicitly supply singleton-base radius bounds, K/√n analytic cutoff divisors, strict resonance closeness and full-rank exclusion. `block_data` is a target, not evidence for these inputs. Reconcile the two reserved names with its actual design and check the strict closeness clause for Λ=0
separately (projection zero). Part 6/7 exact owner signatures are in the already delivered design;
new generalizations get distinct extended declarations in this design. No `sorry` stub theorem is imported.

## Complete graph-to-declaration inventory

A/B/C below mean `blueprint-N/parts/p11a-partial-route.tex`, `p11b-partial-nf.tex`,
`p11c-partial-stability.tex`. Each locator retains the exact graph label and line range.
A step row is an internal proof obligation inside the named theorem, **not an extra assumed lemma**.
Definition subnodes are covered by the named literal definitions. External rows identify library work,
not a new source theorem with `sorry`. All non-provider declaration names below are in `KAM.Nekhoroshev`
unless qualified. This includes every graph node sourced in the three files, plus the root proved there.

| Graph node | Lean declaration / owner proof | Statement locator | Proof locator |
|---|---|---|---|
| `bpN:p0:partial` | `KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev` | `blueprint-N/parts/p0-conventions.tex#bpN:p0:partial@L319-L335` | `C#bpN:p0:partial@L170-L180` |
| `bpN:p11:ext-num` | Mathlib numerical exp bounds; `bracket_dominated` arithmetic | `A#bpN:p11:ext-num@L40-L40` | — |
| `bpN:p11:ext-rpow` | `Real.rpow_add`, `tendsto_exp_div_rpow_atTop` | `A#bpN:p11:ext-rpow@L41-L41` | — |
| `bpN:p11:ext-chain` | `HasFDerivAt.comp`, `HasDerivAt.comp` | `A#bpN:p11:ext-chain@L42-L42` | — |
| `bpN:p11:wfield` | `wfield`, `realWfield`, `extBracket` | `A#bpN:p11:wfield@L48-L56` | — |
| `bpN:p11:orbit` | `orbit`, `theta`, `thetaInv`, `converted` | `A#bpN:p11:orbit@L58-L61` | `A#bpN:p11:orbit@L62-L65` |
| `stepN:p11:or-chain` | internal `orbit`, `theta`, `thetaInv`, `converted` | `A#stepN:p11:or-chain@L63-L63` | `A#stepN:p11:or-chain@L63-L63` |
| `stepN:p11:or-eq` | internal `orbit`, `theta`, `thetaInv`, `converted` | `A#stepN:p11:or-eq@L64-L64` | `A#stepN:p11:or-eq@L64-L64` |
| `bpN:p11:exponents` | `exponents` | `A#bpN:p11:exponents@L67-L69` | `A#bpN:p11:exponents@L70-L73` |
| `stepN:p11:ex-den` | internal `exponents` | `A#stepN:p11:ex-den@L71-L71` | `A#stepN:p11:ex-den@L71-L71` |
| `stepN:p11:ex-cmp` | internal `exponents` | `A#stepN:p11:ex-cmp@L72-L72` | `A#stepN:p11:ex-cmp@L72-L72` |
| `bpN:p11:constants` | `PartialConstants`, `constants` | `A#bpN:p11:constants@L77-L84` | — |
| `bpN:p11:ext-class` | `ext_class`, `PartialBlock.base`, `slowLoss`, `PartialBlock.SL` | `B#bpN:p11:ext-class@L8-L14` | — |
| `bpN:p11:ext-part4` | `ext_part4`; all Part-4 declarations by dimension instantiation | `B#bpN:p11:ext-part4@L16-L18` | `B#bpN:p11:ext-part4@L16-L18` |
| `bpN:p11:bracket` | `bracket`, `bracket_dominated` | `B#bpN:p11:bracket@L20-L24` | `B#bpN:p11:bracket@L25-L29` |
| `stepN:p11:br-fast` | internal `bracket`, `bracket_dominated` | `B#stepN:p11:br-fast@L26-L26` | `B#stepN:p11:br-fast@L26-L26` |
| `stepN:p11:br-slow` | internal `bracket`, `bracket_dominated` | `B#stepN:p11:br-slow@L27-L27` | `B#stepN:p11:br-slow@L27-L27` |
| `stepN:p11:br-dom` | internal `bracket`, `bracket_dominated` | `B#stepN:p11:br-dom@L28-L28` | `B#stepN:p11:br-dom@L28-L28` |
| `bpN:p11:bracket-g` | `bracket_g` | `B#bpN:p11:bracket-g@L31-L33` | `B#bpN:p11:bracket-g@L34-L36` |
| `bpN:p11:scaled` | `scaled` | `B#bpN:p11:scaled@L40-L42` | — |
| `bpN:p11:vf` | `vf` | `B#bpN:p11:vf@L44-L46` | `B#bpN:p11:vf@L47-L49` |
| `bpN:p11:flow` | `flow`, `flow_real`; `KAM.Canonical.flow_a..d` | `B#bpN:p11:flow@L51-L53` | `B#bpN:p11:flow@L54-L56` |
| `bpN:p11:symplectic` | `symplectic`, `symplectic_bracket`, `symplectic_det`, `symplectic_form`; field identity inside `conj` | `B#bpN:p11:symplectic@L58-L60` | `B#bpN:p11:symplectic@L61-L63` |
| `bpN:p11:adjoint` | `adjoint` | `B#bpN:p11:adjoint@L65-L68` | `B#bpN:p11:adjoint@L69-L86` |
| `stepN:p11:ad-setup` | internal `adjoint` | `B#stepN:p11:ad-setup@L70-L70` | `B#stepN:p11:ad-setup@L70-L70` |
| `stepN:p11:ad-step` | internal `adjoint` | `B#stepN:p11:ad-step@L71-L71` | `B#stepN:p11:ad-step@L71-L71` |
| `stepN:p11:ad-prod` | internal `adjoint` | `B#stepN:p11:ad-prod@L72-L72` | `B#stepN:p11:ad-prod@L72-L72` |
| `bpN:p11:composition` | `composition`, `composition_domain`, `composition_real` | `B#bpN:p11:composition@L88-L93` | `B#bpN:p11:composition@L94-L98` |
| `stepN:p11:co-field` | internal `composition`, `composition_domain`, `composition_real` | `B#stepN:p11:co-field@L95-L95` | `B#stepN:p11:co-field@L95-L95` |
| `stepN:p11:co-series` | internal `composition`, `composition_domain`, `composition_real` | `B#stepN:p11:co-series@L96-L96` | `B#stepN:p11:co-series@L96-L96` |
| `stepN:p11:co-remainder` | internal `composition`, `composition_domain`, `composition_real` | `B#stepN:p11:co-remainder@L97-L97` | `B#stepN:p11:co-remainder@L97-L97` |
| `bpN:p11:ext-taylor` | `ext_taylor`, `ext_taylor_bound`, `ext_taylor_regular` | `B#bpN:p11:ext-taylor@L75-L81` | `B#bpN:p11:ext-taylor@L82-L86` |
| `stepN:p11:et-one` | internal `ext_taylor`, `ext_taylor_bound`, `ext_taylor_regular` | `B#stepN:p11:et-one@L83-L83` | `B#stepN:p11:et-one@L83-L83` |
| `stepN:p11:et-ind` | internal `ext_taylor`, `ext_taylor_bound`, `ext_taylor_regular` | `B#stepN:p11:et-ind@L84-L84` | `B#stepN:p11:et-ind@L84-L84` |
| `stepN:p11:et-taylor` | internal `ext_taylor`, `ext_taylor_bound`, `ext_taylor_regular` | `B#stepN:p11:et-taylor@L85-L85` | `B#stepN:p11:et-taylor@L85-L85` |
| `bpN:p11:ext-e-upper` | `Real.exp_one_lt_d9` | `B#bpN:p11:ext-e-upper@L96-L96` | — |
| `bpN:p11:transform` | `transform`, `transform_integral` | `B#bpN:p11:transform@L100-L102` | `B#bpN:p11:transform@L103-L106` |
| `stepN:p11:tr-taylor` | internal `transform`, `transform_integral` | `B#stepN:p11:tr-taylor@L104-L104` | `B#stepN:p11:tr-taylor@L104-L104` |
| `stepN:p11:tr-int` | internal `transform`, `transform_integral` | `B#stepN:p11:tr-int@L105-L105` | `B#stepN:p11:tr-int@L105-L105` |
| `bpN:p11:canonical-map` | `canonical_map` | `B#bpN:p11:canonical-map@L108-L110` | `B#bpN:p11:canonical-map@L111-L113` |
| `bpN:p11:hom` | `hom`, `homGenerator` | `B#bpN:p11:hom@L119-L121` | `B#bpN:p11:hom@L122-L124` |
| `bpN:p11:iterative` | `iterative` | `B#bpN:p11:iterative@L126-L133` | `B#bpN:p11:iterative@L134-L139` |
| `stepN:p11:it-gen` | internal `iterative` | `B#stepN:p11:it-gen@L135-L135` | `B#stepN:p11:it-gen@L135-L135` |
| `stepN:p11:it-map` | internal `iterative` | `B#stepN:p11:it-map@L136-L136` | `B#stepN:p11:it-map@L136-L136` |
| `stepN:p11:it-taylor` | internal `iterative` | `B#stepN:p11:it-taylor@L137-L137` | `B#stepN:p11:it-taylor@L137-L137` |
| `stepN:p11:it-est` | internal `iterative` | `B#stepN:p11:it-est@L138-L138` | `B#stepN:p11:it-est@L138-L138` |
| `bpN:p11:nf` | `nf` | `B#bpN:p11:nf@L141-L147` | `B#bpN:p11:nf@L148-L160` |
| `stepN:p11:nf-sl` | internal `nf` | `B#stepN:p11:nf-sl@L150-L150` | `B#stepN:p11:nf-sl@L150-L150` |
| `stepN:p11:nf-first` | internal `nf` | `B#stepN:p11:nf-first@L151-L151` | `B#stepN:p11:nf-first@L151-L151` |
| `stepN:p11:nf-case` | internal `nf` | `B#stepN:p11:nf-case@L152-L154` | `B#stepN:p11:nf-case@L152-L154` |
| `stepN:p11:nf-N` | internal `nf` | `B#stepN:p11:nf-N@L155-L155` | `B#stepN:p11:nf-N@L155-L155` |
| `stepN:p11:nf-induct` | internal `nf` | `B#stepN:p11:nf-induct@L156-L156` | `B#stepN:p11:nf-induct@L156-L156` |
| `stepN:p11:nf-concl` | internal `nf` | `B#stepN:p11:nf-concl@L157-L157` | `B#stepN:p11:nf-concl@L157-L157` |
| `stepN:p11:nf-disp` | internal `nf` | `B#stepN:p11:nf-disp@L158-L158` | `B#stepN:p11:nf-disp@L158-L158` |
| `stepN:p11:nf-real` | internal `nf` | `B#stepN:p11:nf-real@L159-L159` | `B#stepN:p11:nf-real@L159-L159` |
| `bpN:p11:s-ext-class#data` | `PartialBlock` | `B#bpN:p11:s-ext-class#data@L4-L6` | — |
| `bpN:p11:s-nf#data` | `ExtNFHyp`, `liftFast` | `B#bpN:p11:s-nf#data@L117-L117` | — |
| `bpN:p11:real-system` | `real_system`, `real_system_bounds`, `real_system_resonant` | `C#bpN:p11:real-system@L7-L13` | `C#bpN:p11:real-system@L14-L18` |
| `stepN:p11:rs-a` | internal `real_system`, `real_system_bounds`, `real_system_resonant` | `C#stepN:p11:rs-a@L15-L15` | `C#stepN:p11:rs-a@L15-L15` |
| `stepN:p11:rs-b` | internal `real_system`, `real_system_bounds`, `real_system_resonant` | `C#stepN:p11:rs-b@L16-L16` | `C#stepN:p11:rs-b@L16-L16` |
| `stepN:p11:rs-cd` | internal `real_system`, `real_system_bounds`, `real_system_resonant` | `C#stepN:p11:rs-cd@L17-L17` | `C#stepN:p11:rs-cd@L17-L17` |
| `bpN:p11:conj` | `conj`, `ExtConjHyp` | `C#bpN:p11:conj@L20-L22` | `C#bpN:p11:conj@L23-L25` |
| `stepN:p11:cj` | internal `conj`, `ExtConjHyp` | `C#stepN:p11:cj@L24-L24` | `C#stepN:p11:cj@L24-L24` |
| `bpN:p11:preimage` | `preimage` | `C#bpN:p11:preimage@L27-L29` | `C#bpN:p11:preimage@L30-L32` |
| `bpN:p11:continuation` | `continuation` | `C#bpN:p11:continuation@L35-L37` | `C#bpN:p11:continuation@L38-L41` |
| `stepN:p11:ct-data` | internal `continuation` | `C#stepN:p11:ct-data@L39-L39` | `C#stepN:p11:ct-data@L39-L39` |
| `stepN:p11:ct-concl` | internal `continuation` | `C#stepN:p11:ct-concl@L40-L40` | `C#stepN:p11:ct-concl@L40-L40` |
| `bpN:p11:transfer` | `transfer_conditional` | `C#bpN:p11:transfer@L43-L52` | `C#bpN:p11:transfer@L53-L61` |
| `stepN:p11:tr-orbit` | internal `transfer_conditional` | `C#stepN:p11:tr-orbit@L55-L55` | `C#stepN:p11:tr-orbit@L55-L55` |
| `stepN:p11:tr-E` | internal `transfer_conditional` | `C#stepN:p11:tr-E@L56-L56` | `C#stepN:p11:tr-E@L56-L56` |
| `stepN:p11:tr-bounds` | internal `transfer_conditional` | `C#stepN:p11:tr-bounds@L57-L57` | `C#stepN:p11:tr-bounds@L57-L57` |
| `stepN:p11:tr-open` | internal `transfer_conditional` | `C#stepN:p11:tr-open@L58-L58` | `C#stepN:p11:tr-open@L58-L58` |
| `stepN:p11:tr-closed` | internal `transfer_conditional` | `C#stepN:p11:tr-closed@L59-L59` | `C#stepN:p11:tr-closed@L59-L59` |
| `stepN:p11:tr-concl` | internal `transfer_conditional` | `C#stepN:p11:tr-concl@L60-L60` | `C#stepN:p11:tr-concl@L60-L60` |
| `bpN:p11:nonresonant` | `nonresonant` | `C#bpN:p11:nonresonant@L65-L68` | `C#bpN:p11:nonresonant@L69-L74` |
| `stepN:p11:nr-nf` | internal `nonresonant` | `C#stepN:p11:nr-nf@L70-L70` | `C#stepN:p11:nr-nf@L70-L70` |
| `stepN:p11:nr-t12` | internal `nonresonant` | `C#stepN:p11:nr-t12@L71-L71` | `C#stepN:p11:nr-t12@L71-L71` |
| `stepN:p11:nr-t3` | internal `nonresonant` | `C#stepN:p11:nr-t3@L72-L72` | `C#stepN:p11:nr-t3@L72-L72` |
| `stepN:p11:nr-concl` | internal `nonresonant` | `C#stepN:p11:nr-concl@L73-L73` | `C#stepN:p11:nr-concl@L73-L73` |
| `bpN:p11:energy-free` | `energy_free` | `C#bpN:p11:energy-free@L78-L84` | `C#bpN:p11:energy-free@L85-L109` |
| `stepN:p11:ef-tube` | internal `energy_free` | `C#stepN:p11:ef-tube@L87-L87` | `C#stepN:p11:ef-tube@L87-L87` |
| `stepN:p11:ef-adm` | internal `energy_free` | `C#stepN:p11:ef-adm@L88-L88` | `C#stepN:p11:ef-adm@L88-L88` |
| `stepN:p11:ef-en` | internal `energy_free` | `C#stepN:p11:ef-en@L89-L89` | `C#stepN:p11:ef-en@L89-L100` |
| `stepN:p11:ef-en-energy` | internal `energy_free` | `C#stepN:p11:ef-en-energy@L91-L93` | `C#stepN:p11:ef-en-energy@L91-L93` |
| `stepN:p11:ef-en-taylor` | internal `energy_free` | `C#stepN:p11:ef-en-taylor@L95-L95` | `C#stepN:p11:ef-en-taylor@L95-L95` |
| `stepN:p11:ef-en-split` | internal `energy_free` | `C#stepN:p11:ef-en-split@L97-L100` | `C#stepN:p11:ef-en-split@L97-L100` |
| `stepN:p11:ef-id` | internal `energy_free` | `C#stepN:p11:ef-id@L101-L102` | `C#stepN:p11:ef-id@L101-L102` |
| `stepN:p11:ef-C` | internal `energy_free` | `C#stepN:p11:ef-C@L103-L107` | `C#stepN:p11:ef-C@L103-L107` |
| `stepN:p11:ef-contra` | internal `energy_free` | `C#stepN:p11:ef-contra@L108-L108` | `C#stepN:p11:ef-contra@L108-L108` |
| `bpN:p11:resonant` | `resonant` | `C#bpN:p11:resonant@L111-L114` | `C#bpN:p11:resonant@L115-L121` |
| `stepN:p11:rs-red` | internal `resonant` | `C#stepN:p11:rs-red@L116-L116` | `C#stepN:p11:rs-red@L116-L116` |
| `stepN:p11:rs-nf` | internal `resonant` | `C#stepN:p11:rs-nf@L117-L117` | `C#stepN:p11:rs-nf@L117-L117` |
| `stepN:p11:rs-t12` | internal `resonant` | `C#stepN:p11:rs-t12@L118-L118` | `C#stepN:p11:rs-t12@L118-L118` |
| `stepN:p11:rs-t3` | internal `resonant` | `C#stepN:p11:rs-t3@L119-L119` | `C#stepN:p11:rs-t3@L119-L119` |
| `stepN:p11:rs-concl` | internal `resonant` | `C#stepN:p11:rs-concl@L120-L120` | `C#stepN:p11:rs-concl@L120-L120` |
| `bpN:p11:hessian` | `hessian`, `hessian_at_sign` | `C#bpN:p11:hessian@L125-L127` | `C#bpN:p11:hessian@L128-L130` |
| `stepN:p11:hs-op` | internal `hessian`, `hessian_at_sign` | `C#stepN:p11:hs-op@L129-L129` | `C#stepN:p11:hs-op@L129-L129` |
| `bpN:p11:block-setting` | `block_setting`, `blockPert` | `C#bpN:p11:block-setting@L132-L134` | — |
| `bpN:p11:domain` | `domain`, `domain_field` | `C#bpN:p11:domain@L136-L138` | `C#bpN:p11:domain@L139-L143` |
| `stepN:p11:dm-pts` | internal `domain`, `domain_field` | `C#stepN:p11:dm-pts@L140-L140` | `C#stepN:p11:dm-pts@L140-L140` |
| `stepN:p11:dm-norm` | internal `domain`, `domain_field` | `C#stepN:p11:dm-norm@L141-L141` | `C#stepN:p11:dm-norm@L141-L141` |
| `stepN:p11:dm-field` | internal `domain`, `domain_field` | `C#stepN:p11:dm-field@L142-L142` | `C#stepN:p11:dm-field@L142-L142` |
| `bpN:p11:block-data` | `block_data` | `C#bpN:p11:block-data@L145-L148` | `C#bpN:p11:block-data@L149-L153` |
| `stepN:p11:bd-cover` | internal `block_data` | `C#stepN:p11:bd-cover@L150-L150` | `C#stepN:p11:bd-cover@L150-L150` |
| `stepN:p11:bd-24` | internal `block_data` | `C#stepN:p11:bd-24@L151-L151` | `C#stepN:p11:bd-24@L151-L151` |
| `stepN:p11:bd-5` | internal `block_data` | `C#stepN:p11:bd-5@L152-L152` | `C#stepN:p11:bd-5@L152-L152` |
| `bpN:p11:block` | `block` | `C#bpN:p11:block@L155-L158` | `C#bpN:p11:block@L159-L166` |
| `stepN:p11:bl-block` | internal `block` | `C#stepN:p11:bl-block@L161-L161` | `C#stepN:p11:bl-block@L161-L161` |
| `stepN:p11:bl-sl` | internal `block` | `C#stepN:p11:bl-sl@L162-L162` | `C#stepN:p11:bl-sl@L162-L162` |
| `stepN:p11:bl-ext` | internal `block` | `C#stepN:p11:bl-ext@L163-L163` | `C#stepN:p11:bl-ext@L163-L163` |
| `stepN:p11:bl-theta` | internal `block` | `C#stepN:p11:bl-theta@L164-L164` | `C#stepN:p11:bl-theta@L164-L164` |
| `stepN:p11:bl-res` | internal `block` | `C#stepN:p11:bl-res@L165-L165` | `C#stepN:p11:bl-res@L165-L165` |
| `stepN:p11:final-empty` | internal provider assembly; `threshold` for final-mu/time | `C#stepN:p11:final-empty@L171-L171` | `C#stepN:p11:final-empty@L171-L171` |
| `stepN:p11:final-data` | internal provider assembly; `threshold` for final-mu/time | `C#stepN:p11:final-data@L172-L172` | `C#stepN:p11:final-data@L172-L172` |
| `stepN:p11:final-mu` | internal provider assembly; `threshold` for final-mu/time | `C#stepN:p11:final-mu@L173-L173` | `C#stepN:p11:final-mu@L173-L173` |
| `stepN:p11:final-time` | internal provider assembly; `threshold` for final-mu/time | `C#stepN:p11:final-time@L174-L174` | `C#stepN:p11:final-time@L174-L174` |
| `stepN:p11:final-given` | internal provider assembly; `threshold` for final-mu/time | `C#stepN:p11:final-given@L175-L175` | `C#stepN:p11:final-given@L175-L175` |
| `stepN:p11:final-orbit` | internal provider assembly; `threshold` for final-mu/time | `C#stepN:p11:final-orbit@L176-L176` | `C#stepN:p11:final-orbit@L176-L176` |
| `stepN:p11:final-sign` | internal provider assembly; `threshold` for final-mu/time | `C#stepN:p11:final-sign@L177-L177` | `C#stepN:p11:final-sign@L177-L177` |
| `stepN:p11:final-drift` | internal provider assembly; `threshold` for final-mu/time | `C#stepN:p11:final-drift@L178-L178` | `C#stepN:p11:final-drift@L178-L178` |
| `stepN:p11:final-order` | internal provider assembly; `threshold` for final-mu/time | `C#stepN:p11:final-order@L179-L179` | `C#stepN:p11:final-order@L179-L179` |
| `bpN:p11:s-real#data` | `PartialBlock.realDom`, `ExtOrbit`, `realHamiltonianExt` | `C#bpN:p11:s-real#data@L4-L5` | — |
| `bpN:p11:hessian#real-hessian` | internal `hessian_at_sign`: real/complex Hessian bridge | `C#bpN:p11:hessian@L126-L126` | `C#stepN:p11:hs-op@L129-L129` |


## Departures and their reasons

| Departure | Reason and preservation obligation |
|---|---|
| Flatten I,q,p into one `Fin (n+(k+k))` base | Fits existing `Weighted` verbatim. Prove norm-preserving append/split identities; frozen fast/slow coordinates remain the actual definitions. |
| Bound predicates with nonnegative bounds | Existing norm API; no total supremum or nonsummable tsum is interpreted as a norm. |
| `ExtCanonical` by linear functionals | Equivalent matrix identity; nondegeneracy c>0 gives form invariance and determinant ±1. No different symplectic hypothesis. |
| `NearResonance` by all pairings in `resSpan` | Equivalent Euclidean projection bound by duality. `block_data` retains strictness using a witness δ below mr/32. Reconcile against the Part-8 projection carrier. |
| Extended T in `transfer_conditional` | `T : ℝ≥0∞` with `ENNReal.ofReal (abs t) ≤ T` retains the source infinite-time case; finite consumers supply their explicit positive times. |
| `slowTube` uses a witness at distance ≤dx | Only the conditional helper needs this closed bound; the witness is the actual physical orbit's slow coordinate. Open tube bounds elsewhere use `<` and are equivalent to distance `<R` without a closedness premise on S. |
| `hessian_at_sign` added | Avoid a second choice of σ after extracting the actual frozen `HasDefiniteFastPart` witness. |
| Local versions of flow reality, symplectic, hom, Taylor | Existing signatures have canonical equal-size coordinates. Their arguments generalize; their theorems cannot simply be applied verbatim. |
| b=1/32, A=40M/m, ε0 denominator 2¹⁴ | Blueprint's declared deviation from Pos93 b=1/8, needed for the energy/free-transfer margins. |
| No upper bound on frequency | Required by exact frozen quantifiers over possibly unbounded G; use the new identity in energy_free. |

No frozen premise is dropped or strengthened. The initial fast erosion is used only to deduce Ic∈G.
The source's k≥1 is retained even though the final theorem might admit k=0; no stronger theorem is asserted.
No new statement is frozen under overnight D29.

## Blueprint issues, source gaps and suspected errata

1. **Nek77 acquisition gap**, 11a L18–22: quotes “will be given elsewhere” for the §10 proofs. This is
   source incompleteness, not an erratum. Do not mark Lemmas 10.3/10.5/10.7 paid by the pinned Part I.
2. **Unbounded-frequency issue**, 11a L33–35, quote “time bound proportional to 1/sup norm omega”.
   Pos93 pp.198–200 does not supply uniform time on unbounded G. It is not a false Pos93 theorem;
   `energy_free` is genuinely new mathematics and remains an independent audit gate.
3. **Unaudited new arguments**, 11c L195–201, quote “No claim is made that the audit ... is complete”.
   Preserve the explicit slow half-radius margin in energy_free; all Cauchy estimates occur only on
   Dom(r/2,s/2). Preserve the separate compact transverse tail in transfer. The graph's round-3 closure
   review does not prove these analytic inequalities or their Lean implementations.
4. **Preimage boundary phrasing**, 11c L31, quote “complex ν-ball of radius 1/2 ... lies in Dom”. If
   interpreted as a *closed* ball, σ'=2s can touch |Im θ|=s, outside the open strip. The proof needs
   only the **open** ball for `KAM.Weighted.general_cauchy`. Use that reading (or radii a<1/2 and a limit);
   the theorem's non-strict σ'≤2s is preserved. This is a proof-language ambiguity, not a refutation.
5. **Graph locator range**, `bpN:p11:adjoint` has PROOF_SOURCE B#adjoint@L69–L86, but its proof ends at
   B L73; L75–86 belong to ext-taylor. Consume the labels ad-setup/ad-step/ad-prod at L70–72. Report
   the stale range to the graph owner; do not edit the graph in this design task.
6. **R2-02 upstream audit**, `PART145-design-audit-2.md`: quote “flow_e is not verbatim on a triple product”.
   The unequal-product implementation here requires the assigned `flow_real` transport. No assumption
   of conjugation invariance of an arbitrary complex domain is silently added.

Pinned-source PDFs were not re-audited in this design task; source-gap and Pos93 claims above are the
current blueprint's own recorded provenance. Newly observed issues 4–5 are blueprint/graph issues.

## Modules, import DAG and prover packages

All paths below are relative to `KAM/Nekhoroshev/Partial/`, except the provider. Estimates include proofs;
each module remains below 1500 lines, and each dispatched package targets 150–800 lines. Split estimates
at theorem boundaries if elaboration or file size requires it. Every module uses copyright, `module`,
`public import`, a module docstring, exposed definitions and `public section`.

| Package / wave | Exact module path(s) | Declarations and inputs | Estimated lines |
|---|---|---|---|
| N11-A / 1 | `Setting.lean`, `Coordinates.lean` | Ext/projections/wfield/bracket, FastConvex/RealFastConvex source bundles, block geometry, extReal/ext_class, ExtCanonical, ExtNFHyp, ExtConjHyp, reExtMap, NearResonance; orbit, θ/θ⁻¹; frozen defs, Weighted/Norm | 300+300 |
| N11-B / 1 | `Constants.lean` | PartialData/PartialConstants, DefiniteSign, exponents, literal numerical formulas; frozen exponents, Weighted.coth | 300 |
| N11-C / 2 | `Bracket.lean`, `VectorField.lean` | bracket/bracket_g, scaled/vf; A, Weighted algebra/Cauchy | 450+250 |
| N11-D / 2 | `RealSystem.lean`, `Continuation.lean` | real_system incl field periodicity; Fourier gradient real/imaginary spans; continuation; A, ODE/Maximal/Continuation, exact Part7 carriers | 450+300 |
| N11-E1 / 3 | `Flow.lean`, `Symplectic.lean` | flow wrapper/reality, Ωc invariance/determinant/field, conj; C,D, Canonical.Flow/FlowRegular/FlowInverse | 200+500 |
| N11-E2 / 3 | `Lie.lean`, `Adjoint.lean` | ext_taylor/derivatives/remainder; adjoint product; A,C, generic calculus | 350+350 |
| N11-E3 / 3 | `Domain.lean`, `Hessian.lean` | physicalDomain/block_setting/blockPert, complex domain, field equality, selected sign, FastConvex/RealFastConvex and toRealFastConvex; A,B, frozen perturbation/definiteness, real restriction | 450+350 |
| N11-F1 / 4 | `Composition.lean`, `Transform.lean` | composition incl norm convergence; transform/integral; C,E1,E2, Weighted.Parametric | 600+450 |
| N11-F2 / 4 | `CanonicalMap.lean` | canonical-map a–e incl both map images and slow displacement; C,E1 | 450 |
| N11-F3 / 3 | `Homological.lean` | homGenerator wrapper/hom; A, exact Part6 homological_param/divisor, extended Part4 | 450 |
| N11-G / 4 | `BlockData.lean` | block_data; B,E3, Part8 covering/cutoffs (reconcile first) | 400 |
| N11-H / 5 | `Iterative.lean` | iterative incl holomorphy, image, equivariance and flow left inverse; C,F1,F2,F3 | 650 |
| N11-J1 / 5 | `Preimage.lean` | preimage, positive margins; A,E1, general_cauchy and Banach contraction | 300 |
| N11-J2 / 6 | `Transfer.lean` | transfer_conditional; D,E1,J1, ODE uniqueness/maximal | 550 |
| N11-K1 / 6 | `NormalFormInduction.lean` | nf admissibility, case A/B, N=0, geometric induction; H | 650 |
| N11-K2 / 7 | `NormalForm.lean` | nf joint witness and displacement; K1, extended telescope argument | 550 |
| N11-L1 / 4 | `EnergyIdentity.lean` | ω-free identity and transverse pairing estimate; C,D, generic FTC | 400 |
| N11-L2 / 5 | `Energy.lean` | energy_free with RealFastConvex only; L1, Part7 exit_ball proof pattern; real-bound bundle declared in Setting | 550 |
| N11-M1 / 8 | `Nonresonant.lean` | nonresonant; K2,J2, Fourier derivative bound | 350 |
| N11-M2 / 8 | `Resonant.lean` | resonant; K2,J2,L2,E3; extract RealFastConvex via toRealFastConvex before energy_free; prove T3 | 450 |
| N11-N / 9 | `Block.lean` | block; G,M1,M2,E3; Θ versus nontrivial lattice, fixed λ scaling | 450 |
| N11-O / 2 | `Threshold.lean` | threshold; B, exponents, rpow/exp asymptotics; all constants before μ | 450 |
| N11-P / 10 | `KAM/Provider/Nekhoroshev/PartialConvexNekhoroshev.lean` | exact provider theorem; N,O,Coordinates,Hessian, frozen defs only | 300 |

Module paths in the table with short names mean, for example,
`KAM/Nekhoroshev/Partial/Setting.lean`; the provider row is already a full path.
Inputs are import dependencies, not assumptions to be appended to source theorems. Modules follow the
package edges above. Setting/Constants are leaves; Domain and Hessian depend on them, never the reverse.
`Threshold` imports numerical constants only, so no cycle through Block/NormalForm is allowed.
`NormalFormInduction` owns the induction helpers; `NormalForm` imports it and exports the joint theorem.
`EnergyIdentity` does not import NormalForm; it works on arbitrary source normal-form data, permitting early audit.
`Transfer` does not import either stability proposition. The provider imports their assembled Block theorem,
and nothing imports the provider except the frozen anchor when sealing is authorized.

Dispatch briefs include the full hard rules above, exact Appendix-A signatures, named upstream receipts,
source locators and a narrow package boundary. At each landing: source lint, targeted compile through the
orchestrator's gate, and `#print axioms` for public results (only propext, Classical.choice, Quot.sound allowed).
This design session runs no builds: the common brief supersedes the generic targeted-build instruction
with the signature-only gate. The mathematical audit of Energy and Transfer remains separate from elaboration.

## Binder-by-binder provider assembly

The exact provider type is the last declaration of Appendix A, copied from the anchor without importing it.
Its binders and the meaning-carrying frozen definitions are unchanged. Assembly proceeds as follows:

| Frozen binder(s) | Assembly use |
|---|---|
| `{n k}`, `hn`, `hk` | dimensions and exponent gaps; preserved exactly, including n≥2,k≥1 |
| `G G' D`, `hG hGc hG' hGc' hD` | store in `PartialData`; G may be empty/unbounded; D may be empty |
| `ρ g m Mcomplex`, `hρ hMc`, `hcollar` | numerical constants, complex collars, positivity from hdef; no extra nonempty premise |
| `h`, `hhol`, `hC2`, `hreal`, `hHess`, `hdef` | the actual frozen function and derivative bounds; extract σ once from hdef; hessian_at_sign supplies signed convexity |
| `∃ μ₀,0<μ₀` | if G=∅ take 1; otherwise threshold gives μ₀ before μ,P,C,z,t |
| `μ`, `0<μ`, `μ<μ₀` | all six comparisons in threshold, including the physical time and final drift |
| `P`, `IsPartialPerturbation ... P` | domain/domain_field with the actual frozen predicate, normalized by μ/(2π) |
| `C`, `0<C`, `z`, `IsSolutionOn ...` | unpack existing guarded derivative and field equation; orbit converts θ while preserving fast actions/slow pair/time |
| initial membership in `innerCore G (μ^b)` | use frozen innerCore inclusion to get Ic∈G; do not require the whole orbit in that inner core |
| `t∈Icc 0 (min C (...))` | derive t≥0, t≤C, t≤frozen time≤blockTime; t=0 is immediate |
| slow predicate `∀u∈Icc 0 t,...` | exactly the stopped interval used by block; no future slow confinement assumption |
| final fast max-norm inequality | block gives R0/(2K); threshold gives ≤μ^b/2; θ leaves fastAction unchanged |

For σ=1 apply Block on J=[0,C], F=F0. For σ=-1 use u↦θ(z(-u)) on [-C,0], F=-F0,
and query -t. Its prefixes correspond exactly to [0,t]; sign reversal preserves the source data bounds.
Do not treat `IsSolutionOn` as a global flow theorem: no extension or global existence is needed for the supplied orbit.
Internal maximal solutions occur only in `transfer_conditional`, where periodic transverse continuation is proved.
The full-rank lattice branch is excluded using |frequency|∞≥g1 and mr0/32≤g1, not a frequency upper bound.

The frozen original hypotheses `hC2`, domain convexity and k≥1 remain in the provider even if individual
internal lemmas use less. No helper changes the anchor ABI. Final sealing is outside this design task.

## Risks and validation

- EnergyIdentity/Energy and Transfer are the unpaid mathematical core; independently audit their constants,
  slow margins, negative times, and continuation before claiming provider closure.
- The shared signature gate elaborates against `/root/code/KAM-inp`'s build snapshot, not a new worktree build.
  Reconcile Part8 names and retire exact upstream stubs before implementation integration.
- Flattened coordinates require explicit real-preserving linear equivalences and derivative transport;
  whole-expression simplification over Fin addition is likely expensive. Prove component identities first.
- Avoid giant normal-form inductions; keep arithmetic, case splitting, map telescoping and reality in separate lemmas.
  Default heartbeat failure is a refactoring signal. No budget override is permitted.
- Empty S/D is allowed; statements with a supplied slow initial point become vacuous. Nonempty G is used only
  in hessian/block-data/threshold and discharged by the provider's explicit branch.
- Elaborating `sorry` statements is type checking only. It supplies no Lean proof of normal form, energy confinement,
  stopped transfer, or the frozen result. `#print axioms` of the provider draft includes `sorryAx` as expected.

Revision-2 validation (2026-10-28):
`/mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-n11 .drafts/scratch/N11Signatures.lean`
exited 0 with exactly 45 `declaration uses sorry` warnings and no other compiler diagnostics
(receipt `.drafts/scratch/N11-r2-signatures.log`). The 845-line signatures file, scratch copy and
Appendix A are byte-identical; the provider command type is byte-identical to the frozen anchor.
All 123 graph inventory entries and all source fingerprints are retained.
A separate invocation of the same gate on `.drafts/scratch/N11R2Inspection.lean` exited 0:
all seven API-name probes passed, and `nf`, `energy_free`, `FastConvex.toRealFastConvex`,
`transfer_conditional` and the provider each printed `[propext, sorryAx, Classical.choice, Quot.sound]`.
Receipt: `.drafts/scratch/N11-r2-inspection.log`. All theorem bodies remain `sorry`;
these checks establish design typing and API availability, not mathematical proof closure.
`scripts/lint_sources.sh` exited 0: `check_lean_modules: PASS (412 Lean files, 0 comparator configurations)`,
`FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (144 frozen declarations)`.
Receipt: `.drafts/scratch/N11-r2-lint.log`; the ABI invocation used the same signature gate via
`.drafts/scratch/lint-bin/lake`. No production Lean module was changed, so the common brief's
signature-only check replaces a targeted module build. `git diff --check` passed.

## Appendix A. Exact signatures

`N11Signatures.lean`: 845 lines; SHA-256 `23bd2cc2645243b3357acccda6e04ff69fad4d055963010025c582f3c886a0e4`.

```lean
/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Weighted.SupWeighted
public import KAM.Weighted.Algebra
public import KAM.ODE.Continuation
public import Mathlib.Analysis.Complex.ExponentialBounds
public import KAM.Weighted.Projections
public import KAM.Weighted.Cauchy
public import KAM.Canonical.Flow
public import KAM.ODE.Maximal
public import KAM.Nekhoroshev.Interfaces.Norms
public import KAM.Frozen.Nekhoroshev.Defs.HasDefiniteFastPart
public import KAM.Frozen.Nekhoroshev.Defs.IsPartialPerturbation
public import KAM.Frozen.Nekhoroshev.Defs.InnerCore
public import KAM.Frozen.Nekhoroshev.Defs.PartialTimeExponent
public import KAM.Frozen.Nekhoroshev.Defs.PartialDriftExponent
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! # Part 11 design signatures
All theorem bodies are deliberately `sorry`. Definitions have literal bodies.
No draft anchor or provider is imported. NF upstream definitions are copied
verbatim from NPart67Signatures until their implementation modules land.
-/
@[expose] public noncomputable section
open Set Metric
open scoped BigOperators

namespace KAM.NormalForm
open KAM.Weighted
variable {n : ℕ}
def zBall (n : ℕ) (K : ℝ) : Set (Fin n → ℤ) := {k | KAM.Fourier.modeSize k ≤ K}
def freq (h : (Fin n → ℂ) → ℂ) (I : Fin n → ℂ) : Fin n → ℂ := fun i => fderiv ℂ h I (Pi.single i 1)
def dotC (k : Fin n → ℤ) (v : Fin n → ℂ) : ℂ := ∑ i, (k i : ℂ) * v i
def conjExp (p : ℝ) : ℝ := p / (p - 1)
def IsNonresonant (D : Set (Fin n → ℂ)) (K α : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ I ∈ D, ∀ k ∈ zBall n K \ Λ, α ≤ ‖dotC k (freq h I)‖
def FreqLipschitz (D : Set (Fin n → ℂ)) (r L : ℝ) (h : (Fin n → ℂ) → ℂ) : Prop :=
  ∀ I₀ ∈ D, ∀ I ∈ KAM.Weighted.polyNbhd D r, ‖I - I₀‖ < r → ‖freq h I - freq h I₀‖ ≤ L * ‖I - I₀‖
def DivisorBound (V : Set (Fin n → ℂ)) (K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (c : ℝ) : Prop :=
  ∀ I ∈ V, ∀ k ∈ zBall n K \ Λ, c ≤ ‖dotC k (freq h I)‖
def homGenParam {m : ℕ} (K : ℝ) (Λ : Set (Fin n → ℤ)) (ω : (Fin m → ℂ) → Fin n → ℂ)
    (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) : (Fin n → ℂ) × (Fin m → ℂ) → ℂ :=
  fun z => ∑' k, (zBall n K \ Λ).indicator (fun k =>
    coeff f z.2 k / (2 * (Real.pi : ℂ) * Complex.I * dotC k (ω z.2)) * KAM.character k z.1) k

def homResParam {m : ℕ} (K : ℝ) (Λ : Set (Fin n → ℤ)) (f : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) :
    (Fin n → ℂ) × (Fin m → ℂ) → ℂ :=
  projMode Λ (truncate K f)

def RealOnParam {m : ℕ} (U : Set ((Fin n → ℂ) × (Fin m → ℂ)))
    (u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ) : Prop :=
  ∀ x : (Fin n → ℝ) × (Fin m → ℝ), (KAM.realInclusion n x.1, KAM.realInclusion m x.2) ∈ U →
    (u (KAM.realInclusion n x.1, KAM.realInclusion m x.2)).im = 0
end KAM.NormalForm
open scoped ContDiff

namespace KAM.Nekhoroshev
open KAM.Weighted KAM.NormalForm
variable {n k : ℕ}

/-- Coordinates are θ, followed by I,q,p in a single weighted base. -/
abbrev Ext (n k : ℕ) (𝕜 : Type*) := (Fin n → 𝕜) × (Fin (n + (k + k)) → 𝕜)
abbrev EC (n k : ℕ) := Ext n k ℂ
abbrev ER (n k : ℕ) := Ext n k ℝ

def fastAction {𝕜 : Type*} (z : Ext n k 𝕜) : Fin n → 𝕜 := fun i => z.2 (Fin.castAdd (k+k) i)
def slowPair {𝕜 : Type*} (z : Ext n k 𝕜) : (Fin k → 𝕜) × (Fin k → 𝕜) :=
  (fun i => z.2 (Fin.natAdd n (Fin.castAdd k i)),
   fun i => z.2 (Fin.natAdd n (Fin.natAdd k i)))
def extCx (z : ER n k) : EC n k := (fun i => (z.1 i : ℂ), fun i => (z.2 i : ℂ))
def extRe (z : EC n k) : ER n k := (fun i => (z.1 i).re, fun i => (z.2 i).re)
abbrev extReal (U : Set (EC n k)) (f : EC n k → ℂ) : Prop :=
  KAM.NormalForm.RealOnParam U f

def wfield (c : ℝ) (H : EC n k → ℂ) (z : EC n k) : EC n k :=
  (fun i => fderiv ℂ H z (0, Pi.single (Fin.castAdd (k+k) i) 1),
   Fin.append (fun i => -fderiv ℂ H z (Pi.single i 1, 0))
    (Fin.append
      (fun i => (c : ℂ) * fderiv ℂ H z (0, Pi.single (Fin.natAdd n (Fin.natAdd k i)) 1))
      (fun i => -(c : ℂ) * fderiv ℂ H z (0, Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1))))
def realWfield (c : ℝ) (H : ER n k → ℝ) (z : ER n k) : ER n k :=
  (fun i => fderiv ℝ H z (0, Pi.single (Fin.castAdd (k+k) i) 1),
   Fin.append (fun i => -fderiv ℝ H z (Pi.single i 1, 0))
    (Fin.append
      (fun i => c * fderiv ℝ H z (0, Pi.single (Fin.natAdd n (Fin.natAdd k i)) 1))
      (fun i => -c * fderiv ℝ H z (0, Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1))))
def extBracket (c : ℝ) (u v : EC n k → ℂ) (z : EC n k) : ℂ :=
  fderiv ℂ u z (wfield c v z)
def extAd (c : ℝ) (φ : EC n k → ℂ) : ℕ → (EC n k → ℂ) → EC n k → ℂ
  | 0, u => u
  | j+1, u => extBracket c (extAd c φ j u) φ

def theta (z : KAM.Planetary.Phase (n+k)) : ER n k :=
  (fun i => KAM.Planetary.fast (b := k) z.1 i / (2*Real.pi),
   Fin.append (KAM.Planetary.fast (b := k) z.2)
     (Fin.append (KAM.Planetary.slow (a := n) z.1) (KAM.Planetary.slow (a := n) z.2)))
def thetaInv (z : ER n k) : KAM.Planetary.Phase (n+k) :=
  (Fin.append (fun i => 2*Real.pi*z.1 i) (slowPair z).1,
   Fin.append (fastAction z) (slowPair z).2)
def converted (H : KAM.Planetary.Phase (n+k) → ℝ) (z : ER n k) : ℝ :=
  H (thetaInv z) / (2*Real.pi)
theorem orbit (H : KAM.Planetary.Phase (n+k) → ℝ)
    (z : ℝ → KAM.Planetary.Phase (n+k)) (t : ℝ) (hh : DifferentiableAt ℝ H (z t)) :
    HasDerivAt z (KAM.hamiltonianVectorField H (z t)) t ↔
    HasDerivAt (theta ∘ z) (realWfield (2*Real.pi) (converted H) (theta (z t))) t := sorry

theorem exponents (hn : 2 ≤ n) :
    0 < partialTimeExponent n ∧ partialTimeExponent n < partialDriftExponent n ∧
    2 * partialDriftExponent n < 1/(2*(n:ℝ)) := sorry

/-- Numerical data, no hypotheses or conclusions hidden in this carrier. -/
structure PartialConstants where
  n : ℕ
  ρ : ℝ
  g : ℝ
  m : ℝ
  Mc : ℝ
namespace PartialConstants
def s (a : PartialConstants) := a.ρ / (4*Real.pi)
def m1 (a : PartialConstants) := a.m / (2*Real.pi)
def M1 (a : PartialConstants) := a.Mc / (2*Real.pi)
def g1 (a : PartialConstants) := a.g / (2*Real.pi)
def r0 (a : PartialConstants) := min (a.ρ/2) (32*a.g/a.m)
def A (a : PartialConstants) := 40*a.Mc/a.m
def eps0 (a : PartialConstants) := a.m1*a.r0^2 / ((2:ℝ)^14*a.A^(2*a.n))
def R0 (a : PartialConstants) := a.r0/a.A
def kappaC (a : PartialConstants) := coth (Real.pi*a.s)^a.n
def cK (a : PartialConstants) := (2*Real.pi*a.eps0/a.kappaC) ^ (1/(2*(a.n:ℝ)))
def eps (a : PartialConstants) (μ : ℝ) := a.kappaC*μ/(2*Real.pi)
def K (a : PartialConstants) (μ : ℝ) := (a.eps0/a.eps μ) ^ (1/(2*(a.n:ℝ)))
def d (a : PartialConstants) (μ : ℝ) := μ ^ partialDriftExponent a.n
def kappa (a : PartialConstants) (μ : ℝ) := 2*Real.pi*a.K μ*a.s/Real.sqrt a.n
def rTheta (a : PartialConstants) (μ : ℝ) := a.r0/(a.A*a.K μ)^a.n
def blockTime (a : PartialConstants) (μ : ℝ) :=
  a.s*a.m1*a.rTheta μ/(240*a.M1*a.eps μ)*Real.exp (a.kappa μ/6)
end PartialConstants

/-- Fixed block geometry: λ and c are computed once, never from an iterated R. -/
structure PartialBlock (n k : ℕ) where
  Ic : Fin n → ℝ
  S : Set (KAM.Planetary.Phase k)
  rB : ℝ
  w : ℝ
namespace PartialBlock
def lam (b : PartialBlock n k) := b.w/b.rB
def c (b : PartialBlock n k) := 2*Real.pi/b.lam^2
def base (b : PartialBlock n k) : Set (Fin (n+(k+k)) → ℂ) :=
  {J | ∃ x ∈ b.S, J = Fin.append (fun i => (b.Ic i : ℂ))
    (Fin.append (fun i => ((x.1 i/b.lam : ℝ) : ℂ)) (fun i => ((x.2 i/b.lam : ℝ) : ℂ)))}
def realDom (b : PartialBlock n k) (R : ℝ) : Set (ER n k) :=
  {z | extCx z ∈ Dom n b.base R 1}
def SL (b : PartialBlock n k) (s : ℝ) : Prop := 64*Real.pi*k*s*b.rB ≤ b.w^2
end PartialBlock

def ext_class (b : PartialBlock n k) (R s : ℝ) (u : EC n k → ℂ) : Prop :=
  InClass b.base R s u ∧ extReal (Dom n b.base R s) u
def slowLoss (c ρ σ : ℝ) (k : ℕ) : Prop := 16*k*c*σ ≤ ρ
def scaled (ρ σ : ℝ) (z : EC n k) : ℝ := max (‖z.1‖/σ) (‖z.2‖/ρ)
def liftFast (h : (Fin n → ℂ) → ℂ) (z : EC n k) : ℂ := h (fastAction z)
def realHamiltonianExt (b : PartialBlock n k) (R : ℝ) (H : EC n k → ℂ) : ER n k → ℝ :=
  (b.realDom R).indicator (fun z => (H (extCx z)).re)
def ExtOrbit (b : PartialBlock n k) (R : ℝ) (H : EC n k → ℂ)
    (J : Set ℝ) (y : ℝ → ER n k) : Prop :=
  KAM.ODE.IsSolutionIn (realWfield b.c (realHamiltonianExt b R H)) (b.realDom R) J y

theorem ext_part4 (b : PartialBlock n k) {R s U : ℝ} {u : EC n k → ℂ}
    (hs : 0 < s) (hu : InClass b.base R s u) (hb : WBound b.base R s u U) :
    ∀ z ∈ Dom n b.base R s, ‖u z‖ ≤ U := sorry

theorem bracket (b : PartialBlock n k) {R0 s0 R s ρ σ U V : ℝ} {u v : EC n k → ℂ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hσ : 0 < σ) (hσs : σ < s)
    (hR0 : R-ρ < R0) (hs0 : s-σ < s0)
    (hu : InClass b.base R0 s0 u) (hv : InClass b.base R s v)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hbu : WBound b.base R0 s0 u U) (hbv : WBound b.base R s v V) :
    InClass b.base (R-ρ) (s-σ) (extBracket b.c u v) ∧
    WBound b.base (R-ρ) (s-σ) (extBracket b.c u v)
      (((Real.exp 1)⁻¹*(1/((R0-R+ρ)*σ)+1/((s0-s+σ)*ρ))+
        2*k*b.c/((R0-R+ρ)*ρ))*U*V) := sorry

theorem bracket_dominated {c ρ σ R0 R s0 s : ℝ} (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hσ : 0 < σ) (hR : R-ρ < R0) (hs : s-σ < s0) (hSL : slowLoss c ρ σ k) :
    (Real.exp 1)⁻¹*(1/((R0-R+ρ)*σ)+1/((s0-s+σ)*ρ)) + 2*k*c/((R0-R+ρ)*ρ) ≤
      (1/2)*(1/((R0-R+ρ)*σ)+1/((s0-s+σ)*ρ)) := sorry

/-- Decomposition is literal finite summation, as Part 6, with independent base dimension. -/
theorem bracket_g (b : PartialBlock n k) {N : ℕ} {R s ρ σ V : ℝ}
    (gj : Fin N → EC n k → ℂ) (Rj sj Uj : Fin N → ℝ) (φ : EC n k → ℂ)
    (hρ : 0 < ρ) (hρR : ρ < R) (hσ : 0 < σ) (hσs : σ < s)
    (hSL : slowLoss b.c ρ σ k) (hRj : ∀ j, R ≤ Rj j) (hsj : ∀ j, s ≤ sj j)
    (hU : ∀ j, 0 ≤ Uj j) (hV : 0 ≤ V)
    (hg : ∀ j, InClass b.base (Rj j) (sj j) (gj j))
    (hgb : ∀ j, WBound b.base (Rj j) (sj j) (gj j) (Uj j))
    (hφ : InClass b.base R s φ) (hφb : WBound b.base R s φ V) :
    WBound b.base (R-ρ) (s-σ) (extBracket b.c (fun z => ∑ j, gj j z) φ)
      ((∑ j, (1/2)*(ρ/(Rj j-R+ρ)+σ/(sj j-s+σ))*Uj j)*V/(ρ*σ)) := sorry

theorem vf (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ U : ℝ} {φ : EC n k → ℂ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hσ : 0 < σ) (hσs : σ < s)
    (hSL : slowLoss b.c ρ σ k) (hU : 0 ≤ U)
    (hφ : InClass b.base R s φ) (hb : WBound b.base R s φ U) :
    ∀ z ∈ Dom n b.base (R-ρ) (s-σ), scaled ρ σ (wfield b.c φ z) ≤ U/(ρ*σ) ∧
      ‖slowPair (wfield b.c φ z)‖ ≤ b.c*U/ρ := sorry

/-- Generic Part 5 flow is consumed directly: no second choice of flow. -/
theorem flow (W : EC n k ≃L[ℂ] EC n k) {Ω : Set (EC n k)} {F : EC n k → EC n k} {ε : ℝ}
    (hF : KAM.Canonical.SmallField W Ω F ε) {z : EC n k}
    (hz : z ∈ KAM.Canonical.gaugeInterior W Ω (1/2)) {t : ℝ} (ht : |t| ≤ 1) :
    KAM.Canonical.flow F Ω t z ∈ Ω ∧
    ‖W (KAM.Canonical.flow F Ω t z-z)‖ ≤ |t| *ε := sorry

/-- Basis-free expression of DΨ Ω DΨᵀ=Ω, for all linear functionals. -/
def ExtCanonical (c : ℝ) (U : Set (EC n k)) (Ψ : EC n k → EC n k) : Prop :=
  ∀ z ∈ U, ∀ u v : EC n k →L[ℂ] ℂ,
    extBracket c (fun x => u (Ψ x)) (fun x => v (Ψ x)) z =
      extBracket c (fun x => u x) (fun x => v x) (Ψ z)

theorem symplectic {Ω : Set (EC n k)} (hΩ : IsOpen Ω) {c ε : ℝ} (hc : 0 < c)
    (φ : EC n k → ℂ) (hφ : DifferentiableOn ℂ φ Ω) (W : EC n k ≃L[ℂ] EC n k)
    (hF : KAM.Canonical.SmallField W Ω (wfield c φ) ε) {t : ℝ} (ht : |t| ≤ 1) :
    ExtCanonical c (KAM.Canonical.gaugeInterior W Ω (1/2))
      (KAM.Canonical.flow (wfield c φ) Ω t) := sorry

theorem adjoint (b : PartialBlock n k) {R' s' R s ρ σ U V : ℝ} {φ u : EC n k → ℂ}
    (hρ : 0 < ρ) (hρR : ρ < R) (hσ : 0 < σ) (hσs : σ < s)
    (hRR : R+ρ ≤ R') (hss : s+σ ≤ s') (hSL : slowLoss b.c ρ σ k)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hφ : InClass b.base R' s' φ) (hu : InClass b.base R s u)
    (hφb : WBound b.base R' s' φ V) (hub : WBound b.base R s u U) (j : ℕ) (hj : 1 ≤ j) :
    InClass b.base (R-ρ) (s-σ) (extAd b.c φ j u) ∧
    WBound b.base (R-ρ) (s-σ) (fun z => ((j.factorial:ℂ)⁻¹)*extAd b.c φ j u z)
      ((Real.exp 1^2*(2*V/(ρ*σ))/8)^j*U) := sorry

theorem ext_taylor {Ω : Set (EC n k)} (hΩ : IsOpen Ω) {c : ℝ}
    {φ u : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω) (hu : DifferentiableOn ℂ u Ω)
    {γ : ℝ → EC n k} (hγ : KAM.ODE.IsSolutionIn (wfield c φ) Ω (Icc 0 1) γ)
    (N : ℕ) (hN : 1 ≤ N) :
    u (γ 1) = (∑ j ∈ Finset.range N, ((j.factorial:ℂ)⁻¹)*extAd c φ j u (γ 0)) +
      ∫ t in (0:ℝ)..1, (((1-t)^(N-1)/(N-1).factorial:ℝ):ℂ)*extAd c φ N u (γ t) := sorry

/-- Source assumptions for B.5, including explicit norm bounds. -/
structure ExtCompose (b : PartialBlock n k) (R' s' R s ρ σ V : ℝ) (φ : EC n k → ℂ) : Prop where
  rho_pos : 0 < ρ
  rho_lt : ρ < R
  sig_pos : 0 < σ
  sig_lt : σ < s
  radii : R+ρ ≤ R'
  widths : s+σ ≤ s'
  bound_nonneg : 0 ≤ V
  hol : InClass b.base R' s' φ
  bound : WBound b.base R' s' φ V
  small : 2*V/(ρ*σ) ≤ 1/2
  slow : slowLoss b.c ρ σ k

def extFlow (b : PartialBlock n k) (R s ρ σ : ℝ) (φ : EC n k → ℂ) (t : ℝ) : EC n k → EC n k :=
  KAM.Canonical.flow (wfield b.c φ) (Dom n b.base (R-ρ) (s-σ)) t

theorem composition (b : PartialBlock n k) (hk : 1 ≤ k) {R' s' R s ρ σ V U : ℝ}
    {φ u : EC n k → ℂ} (hc : ExtCompose b R' s' R s ρ σ V φ)
    (hU : 0 ≤ U) (hu : InClass b.base R s u) (hub : WBound b.base R s u U) :
    let X := extFlow b R' s' ρ σ φ
    (∀ t : ℝ, |t| ≤ 1 → MapsTo (X t) (Dom n b.base (R-ρ) (s-σ)) (Dom n b.base R s)) ∧
    (∀ t : ℝ, |t| ≤ 1 → InClass b.base (R-ρ) (s-σ) (u ∘ X t) ∧
      WBound b.base (R-ρ) (s-σ) (u ∘ X t) ((1-|t| *(2*V/(ρ*σ)))⁻¹*U)) ∧
    (∀ z ∈ Dom n b.base (R-ρ) (s-σ),
      HasSum (fun j : ℕ => ((j.factorial:ℂ)⁻¹)*extAd b.c φ j u z) (u (X 1 z))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ N' ≥ N,
      WBound b.base (R-ρ) (s-σ)
        (fun z => u (X 1 z)-∑ j ∈ Finset.range N', ((j.factorial:ℂ)⁻¹)*extAd b.c φ j u z) ε) := sorry

theorem transform (b : PartialBlock n k) (hk : 1 ≤ k) {R' s' R s ρ σ V U W : ℝ}
    {φ h f : EC n k → ℂ} (hc : ExtCompose b R' s' R s ρ σ V φ)
    (hh : InClass b.base R s h) (hf : InClass b.base R s f)
    (hw : InClass b.base R s (extBracket b.c h φ)) (hU : 0 ≤ U) (hW : 0 ≤ W)
    (hfb : WBound b.base R s f U) (hwb : WBound b.base R s (extBracket b.c h φ) W) :
    let X := extFlow b R' s' ρ σ φ
    let rem := fun z => ∫ t in (0:ℝ)..1,
      extBracket b.c (fun x => ((1-t:ℝ):ℂ)*extBracket b.c h φ x+f x) φ (X t z)
    (∀ z ∈ Dom n b.base (R-ρ) (s-σ),
      (h+f) (X 1 z) = h z+extBracket b.c h φ z+f z+rem z) ∧
    InClass b.base (R-ρ) (s-σ) rem ∧
    WBound b.base (R-ρ) (s-σ) rem ((2*V/(ρ*σ))/(1-2*V/(ρ*σ))*(W/2+U)) := sorry

/-- Separate statement retains joint continuity required by the integral clause. -/
theorem transform_integral (b : PartialBlock n k) (hk : 1 ≤ k) {R' s' R s ρ σ V U : ℝ}
    {φ : EC n k → ℂ} (hc : ExtCompose b R' s' R s ρ σ V φ) (v : ℝ → EC n k → ℂ)
    (hU : 0 ≤ U) (hv : ∀ t ∈ Icc (0:ℝ) 1, InClass b.base R s (v t))
    (hvb : ∀ t ∈ Icc (0:ℝ) 1, WBound b.base R s (v t) U)
    (hcont : ContinuousOn (fun p : ℝ × EC n k => v p.1 p.2) (Icc 0 1 ×ˢ Dom n b.base R s))
    (hdcont : ContinuousOn (fun p : ℝ × EC n k => fderiv ℂ (v p.1) p.2) (Icc 0 1 ×ˢ Dom n b.base R s)) :
    InClass b.base (R-ρ) (s-σ) (fun z => ∫ t in (0:ℝ)..1, v t (extFlow b R' s' ρ σ φ t z)) ∧
    WBound b.base (R-ρ) (s-σ) (fun z => ∫ t in (0:ℝ)..1, v t (extFlow b R' s' ρ σ φ t z))
      ((1-2*V/(ρ*σ))⁻¹*U) := sorry

theorem canonical_map (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ V : ℝ} {φ : EC n k → ℂ}
    (hρ : 0 < ρ) (hρR : ρ < R/2) (hσ : 0 < σ) (hσs : σ < s/2)
    (hSL : slowLoss b.c ρ σ k) (hV : 0 ≤ V) (hsmall : V/(ρ*σ) ≤ 1/2)
    (hφ : InClass b.base R s φ) (hb : WBound b.base R s φ V) :
    let Φ := extFlow b R s ρ σ φ 1
    let Ψ := extFlow b R s ρ σ φ (-1)
    let U := Dom n b.base (R-3*ρ/2) (s-3*σ/2)
    DifferentiableOn ℂ Φ U ∧ DifferentiableOn ℂ Ψ U ∧ MapsTo Φ U (Dom n b.base (R-ρ) (s-σ)) ∧
    MapsTo Ψ U (Dom n b.base (R-ρ) (s-σ)) ∧
    ExtCanonical b.c U Φ ∧
    (∀ z ∈ U, ‖(Φ z).1-z.1‖ ≤ V/ρ ∧ ‖fastAction (Φ z)-fastAction z‖ ≤ V/(Real.exp 1*σ) ∧
      ‖slowPair (Φ z)-slowPair z‖ ≤ b.c*V/ρ) ∧
    (∀ z ∈ U, ∀ ℓ : Fin n → ℤ,
      Φ (z.1+(fun i => (ℓ i:ℂ)), z.2) = Φ z+((fun i => (ℓ i:ℂ)),0)) ∧
    (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), Ψ (Φ z) = z ∧ Φ (Ψ z) = z ∧ Φ z ∈ U) ∧
    (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), ∀ v : EC n k,
      scaled ρ σ (fderiv ℂ Φ z v-v) ≤ 2*(V/(ρ*σ))*scaled ρ σ v) ∧
    (extReal (Dom n b.base R s) φ → ∀ z : ER n k, extCx z ∈ U → extCx (extRe (Φ (extCx z))) = Φ (extCx z)) := sorry

def homGenerator (K : ℝ) (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ)
    (f : EC n k → ℂ) : EC n k → ℂ :=
  KAM.NormalForm.homGenParam K Λ (fun J => freq h (fun i => J (Fin.castAdd (k+k) i))) f

theorem hom (b : PartialBlock n k) {R s K α q U : ℝ} (h : (Fin n → ℂ) → ℂ)
    (f : EC n k → ℂ) (hR : 0 < R) (hs : 0 < s) (hK : 0 ≤ K) (hα : 0 < α) (hq : 1 ≤ q)
    (Λ : Set (Fin n → ℤ)) (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} R))
    (hdiv : DivisorBound (polyNbhd {KAM.realInclusion n b.Ic} R) K Λ h (α/q))
    (hU : 0 ≤ U) (hf : InClass b.base R s f) (hb : WBound b.base R s f U) :
    let ξ := projMode Λ (truncate K f)
    let φ := homGenerator K Λ h f
    InClass b.base R s ξ ∧ InClass b.base R s φ ∧
    WBound b.base R s ξ U ∧ WBound b.base R s (truncate K f) U ∧
    WBound b.base R s φ (q*U/(2*Real.pi*α)) ∧
    (∀ z ∈ Dom n b.base R s, extBracket b.c φ (liftFast h) z+ξ z = truncate K f z) ∧
    (∀ z ∈ Dom n b.base R s, projMode Λ φ z = 0) ∧
    ((∀ j, j ∈ Λ ↔ -j ∈ Λ) → extReal (Dom n b.base R s) f →
      (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} R →
        ∀ i, (freq h (KAM.realInclusion n I) i).im = 0) →
      extReal (Dom n b.base R s) ξ ∧ extReal (Dom n b.base R s) φ) := sorry

/-- Source premises for a block normal form, not its conclusion. -/
structure ExtNFHyp (b : PartialBlock n k) (s K α L p ε : ℝ)
    (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ) (f : EC n k → ℂ) : Prop where
  n_pos : 1 ≤ n
  k_pos : 1 ≤ k
  radius_pos : 0 < b.rB
  slow_width_pos : 0 < b.w
  s_pos : 0 < s
  K_pos : 0 < K
  alpha_pos : 0 < α
  L_nonneg : 0 ≤ L
  p_gt : 1 < p
  eps_pos : 0 < ε
  symmetric : ∀ j, j ∈ Λ ↔ -j ∈ Λ
  hol : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} b.rB)
  real : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} b.rB →
    (h (KAM.realInclusion n I)).im = 0
  nr : IsNonresonant {KAM.realInclusion n b.Ic} K α Λ h
  lip : FreqLipschitz {KAM.realInclusion n b.Ic} b.rB L h
  divisor_size : K*L*b.rB ≤ α/p
  slow : b.SL s
  pert : ext_class b b.rB s f
  bound : WBound b.base b.rB s f ε
  cutoff : 6 ≤ 2*Real.pi*K*s

theorem iterative (b : PartialBlock n k) (hk : 1 ≤ k) {R s ρ σ K α p δ : ℝ}
    (h : (Fin n → ℂ) → ℂ) (f : EC n k → ℂ) (Λ : Set (Fin n → ℤ))
    (hR : 0 < ρ) (hR' : 2*ρ < R) (hs : 0 < σ) (hs' : 2*σ < s)
    (hSL : slowLoss b.c ρ σ k) (hα : 0 < α) (hp : 1 < p) (hK : 0 ≤ K)
    (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} R))
    (hdiv : DivisorBound (polyNbhd {KAM.realInclusion n b.Ic} R) K Λ h (α/conjExp p))
    (hδ : 0 ≤ δ) (hf : InClass b.base R s f) (hfb : WBound b.base R s f δ)
    (hsmall : δ ≤ 2*Real.pi*α*ρ*σ/(4*conjExp p))
    {N : ℕ} (gj : Fin N → EC n k → ℂ) (Rj sj Uj : Fin N → ℝ)
    (hRj : ∀ j, R ≤ Rj j) (hsj : ∀ j, s ≤ sj j) (hUj : ∀ j, 0 ≤ Uj j)
    (hgj : ∀ j, InClass b.base (Rj j) (sj j) (gj j))
    (hgjb : ∀ j, WBound b.base (Rj j) (sj j) (gj j) (Uj j)) :
    let q := conjExp p
    let φ := homGenerator K Λ h f
    let Φ := extFlow b R s ρ σ φ 1
    let g := fun z => ∑ j, gj j z
    let gp := g+projMode Λ (truncate K f)
    DifferentiableOn ℂ Φ (Dom n b.base (R-3*ρ/2) (s-3*σ/2)) ∧
    MapsTo Φ (Dom n b.base (R-3*ρ/2) (s-3*σ/2)) (Dom n b.base (R-ρ) (s-σ)) ∧
    (∀ z ∈ Dom n b.base (R-3*ρ/2) (s-3*σ/2), ∀ ℓ : Fin n → ℤ,
      Φ (z.1+(fun i => (ℓ i:ℂ)),z.2) = Φ z+((fun i => (ℓ i:ℂ)),0)) ∧
    (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), extFlow b R s ρ σ φ (-1) (Φ z) = z) ∧
    ∃ fp : EC n k → ℂ,
      InClass b.base (R-2*ρ) (s-2*σ) fp ∧
      (∀ z ∈ Dom n b.base (R-2*ρ) (s-2*σ), liftFast h (Φ z)+g (Φ z)+f (Φ z) = liftFast h z+gp z+fp z) ∧
      WBound b.base (R-2*ρ) (s-2*σ) fp
        ((1-2*q*δ/(2*Real.pi*α*ρ*σ))⁻¹*
          (q/(2*Real.pi*α*ρ*σ)*((∑ j, (1/2)*(ρ/(Rj j-R+ρ)+σ/(sj j-s+σ))*Uj j)+δ)+
            Real.exp (-2*Real.pi*K*σ))*δ) ∧
      ExtCanonical b.c (Dom n b.base (R-3*ρ/2) (s-3*σ/2)) Φ ∧
      Set.InjOn Φ (Dom n b.base (R-2*ρ) (s-2*σ)) ∧
      WBound b.base (R-2*ρ) (s-2*σ) (gp-g) δ ∧
      (∀ z ∈ Dom n b.base (R-3*ρ/2) (s-3*σ/2),
        ‖(Φ z).1-z.1‖ ≤ q*δ/(2*Real.pi*α*ρ) ∧
        ‖fastAction (Φ z)-fastAction z‖ ≤ q*δ/(Real.exp 1*2*Real.pi*α*σ) ∧
        ‖slowPair (Φ z)-slowPair z‖ ≤ q*δ/(16*k*2*Real.pi*α*σ)) ∧
      ((∀ j, j ∈ Λ ↔ -j ∈ Λ) →
        (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} R →
          (h (KAM.realInclusion n I)).im = 0) →
        extReal (Dom n b.base R s) g → extReal (Dom n b.base R s) f →
        extReal (Dom n b.base R s) φ ∧ extReal (Dom n b.base (R-2*ρ) (s-2*σ)) gp ∧
        extReal (Dom n b.base (R-2*ρ) (s-2*σ)) fp ∧
        ∀ z : ER n k, extCx z ∈ Dom n b.base (R-3*ρ/2) (s-3*σ/2) →
          extCx (extRe (Φ (extCx z))) = Φ (extCx z)) := sorry

theorem nf (b : PartialBlock n k) {s K α L p ε : ℝ} {Λ : Set (Fin n → ℤ)}
    {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ} (ha : ExtNFHyp b s K α L p ε Λ h f)
    (hsmall : ε ≤ α*b.rB/(2^7*conjExp p*K)) :
    ∃ Ψ : EC n k → EC n k, ∃ g fs : EC n k → ℂ,
      DifferentiableOn ℂ Ψ (Dom n b.base (b.rB/2) (s/6)) ∧
      MapsTo Ψ (Dom n b.base (b.rB/2) (s/6)) (Dom n b.base b.rB s) ∧
      Set.InjOn Ψ (Dom n b.base (b.rB/2) (s/6)) ∧
      ExtCanonical b.c (Dom n b.base (b.rB/2) (s/6)) Ψ ∧
      (∀ z ∈ Dom n b.base (b.rB/2) (s/6), ∀ ℓ : Fin n → ℤ,
        Ψ (z.1+(fun i => (ℓ i:ℂ)),z.2) = Ψ z+((fun i => (ℓ i:ℂ)),0)) ∧
      (∀ z : ER n k, extCx z ∈ Dom n b.base (b.rB/2) (s/6) →
        extCx (extRe (Ψ (extCx z))) = Ψ (extCx z)) ∧
      ext_class b (b.rB/2) (s/6) g ∧ ext_class b (b.rB/2) (s/6) fs ∧
      (∀ J ∈ polyNbhd b.base (b.rB/2), ∀ j : Fin n → ℤ,
        j ∉ Λ ∩ zBall n K → coeff g J j = 0) ∧
      (∀ z ∈ Dom n b.base (b.rB/2) (s/6), liftFast h (Ψ z)+f (Ψ z) = liftFast h z+g z+fs z) ∧
      WBound b.base (b.rB/2) (s/6) (g-projMode Λ (truncate K f))
        (16*(2*conjExp p*K/(α*b.rB))*ε^2) ∧
      WBound b.base (b.rB/2) (s/6) fs (Real.exp (-(2*Real.pi*K*s)/6)*ε) ∧
      (∀ z ∈ Dom n b.base (b.rB/2) (s/6),
        ‖fastAction (Ψ z)-fastAction z‖ ≤ conjExp p*K*ε/α ∧
        ‖(Ψ z).1-z.1‖ ≤ 10*conjExp p*ε/(2*Real.pi*α*b.rB) ∧
        ‖slowPair (Ψ z)-slowPair z‖ ≤ conjExp p*K*ε/(8*α)) := sorry

/-- Literal real restriction and energy; finite norm is absent here. -/
theorem real_system (b : PartialBlock n k) {R s : ℝ} {H : EC n k → ℂ}
    (hR : 0 < R) (hs : 0 < s) (hH : ext_class b R s H) :
    ContDiffOn ℝ ∞ (realHamiltonianExt b R H) (b.realDom R) ∧
    ContDiffOn ℝ 1 (realWfield b.c (realHamiltonianExt b R H)) (b.realDom R) ∧
    (∀ z ∈ b.realDom R, extCx (realWfield b.c (realHamiltonianExt b R H) z) = wfield b.c H (extCx z)) ∧
    (∀ ℓ : Fin n → ℤ, ∀ z ∈ b.realDom R,
      realHamiltonianExt b R H (z.1+(fun i => (ℓ i:ℝ)),z.2) = realHamiltonianExt b R H z) ∧
    (∀ ℓ : Fin n → ℤ, ∀ z ∈ b.realDom R,
      realWfield b.c (realHamiltonianExt b R H) (z.1+(fun i => (ℓ i:ℝ)),z.2) =
        realWfield b.c (realHamiltonianExt b R H) z) ∧
    (∀ J : Set ℝ, J.OrdConnected → ∀ r, 0 < r → r ≤ R → ∀ y, ExtOrbit b r H J y →
      ∀ t ∈ J, ∀ u ∈ J, realHamiltonianExt b R H (y t) = realHamiltonianExt b R H (y u)) := sorry

theorem real_system_bounds (b : PartialBlock n k) {R s U : ℝ} {u : EC n k → ℂ}
    (hs : 0 < s) (hu : InClass b.base R s u) (hb : WBound b.base R s u U) :
    ∀ y ∈ b.realDom R, ‖u (extCx y)‖ ≤ U ∧
      ∑ j, ‖dtheta j u (extCx y)‖ ≤ U/(Real.exp 1*s) := sorry

def reExtMap (Ψ : EC n k → EC n k) (y : ER n k) : ER n k := extRe (Ψ (extCx y))
/-- Source hypotheses about the map; no orbit confinement in this structure. -/
structure ExtConjHyp (b : PartialBlock n k) (R s r t : ℝ) (H Ht : EC n k → ℂ)
    (Ψ : EC n k → EC n k) : Prop where
  R_pos : 0 < R
  r_pos : 0 < r
  s_pos : 0 < s
  t_pos : 0 < t
  r_le : r ≤ R
  t_le : t ≤ s
  outer : ext_class b R s H
  inner : ext_class b r t Ht
  hol : DifferentiableOn ℂ Ψ (Dom n b.base r t)
  maps : MapsTo Ψ (Dom n b.base r t) (Dom n b.base R s)
  real : ∀ z : ER n k, extCx z ∈ Dom n b.base r t → extCx (reExtMap Ψ z) = Ψ (extCx z)
  canon : ExtCanonical b.c (Dom n b.base r t) Ψ
  identity : ∀ z ∈ Dom n b.base r t, Ht z = H (Ψ z)

theorem conj (b : PartialBlock n k) {R s r t : ℝ} {H Ht : EC n k → ℂ} {Ψ : EC n k → EC n k}
    (hc : ExtConjHyp b R s r t H Ht Ψ) {J : Set ℝ} {y : ℝ → ER n k}
    (hy : ExtOrbit b r Ht J y) : ExtOrbit b R H J (reExtMap Ψ ∘ y) := sorry

theorem preimage (b : PartialBlock n k) (hbR : 0 < b.rB) (hbw : 0 < b.w) {R s dθ dI dx ρ σ : ℝ} {Ψ : EC n k → EC n k}
    (hΨ : DifferentiableOn ℂ Ψ (Dom n b.base R s))
    (hr : ∀ y : ER n k, extCx y ∈ Dom n b.base R s → extCx (reExtMap Ψ y) = Ψ (extCx y))
    (hb : ∀ z ∈ Dom n b.base R s,
      ‖(Ψ z).1-z.1‖ ≤ dθ ∧ ‖fastAction (Ψ z)-fastAction z‖ ≤ dI ∧ ‖slowPair (Ψ z)-slowPair z‖ ≤ dx)
    (hρ : 0 < ρ) (hρR : ρ ≤ R) (hσ : 0 < σ) (hσs : σ ≤ 2*s)
    (hsmall : max (dθ/σ) (max (dI/ρ) (dx/ρ)) ≤ 1/4) :
    ∀ y : ER n k, fastAction y = b.Ic → b.lam • slowPair y ∈ b.S →
      ∃ x ∈ b.realDom R, Ψ (extCx x) = extCx y ∧
        ‖x.1-y.1‖ ≤ dθ ∧ ‖fastAction x-b.Ic‖ ≤ dI ∧ ‖slowPair x-slowPair y‖ ≤ dx := sorry

theorem continuation {N : ℕ} {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    {F : (Fin n → ℝ) × (Fin N → ℝ) → (Fin n → ℝ) × (Fin N → ℝ)}
    (hF : ContDiffOn ℝ 1 F (univ ×ˢ U))
    (hper : ∀ ℓ : Fin n → ℤ, ∀ z ∈ (univ : Set (Fin n → ℝ)) ×ˢ U,
      F (z.1+(fun i => (ℓ i:ℝ)),z.2) = F z)
    {z0 : (Fin n → ℝ) × (Fin N → ℝ)} {Tm Tp : EReal} {z : ℝ → (Fin n → ℝ) × (Fin N → ℝ)}
    (hz : KAM.ODE.IsMaximalSolution F (univ ×ˢ U) z0 Tm Tp z)
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hconf : ∃ t0 : ℝ, 0 ≤ t0 ∧ (t0:EReal) < Tp ∧
      ∀ t : ℝ, t0 ≤ t → (t:EReal) < Tp → (z t).2 ∈ K) : Tp = ⊤ := sorry

end KAM.Nekhoroshev

/-! Verbatim Part 7 definitions; delete these stubs when Stability/Gradient and Transfer land. -/
namespace KAM.Stability
variable {n : ℕ}
def resSpan (Λ : Set (Fin n → ℤ)) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ ((fun k i => (k i : ℝ)) '' Λ)
structure IsActionNorm (N : (Fin n → ℝ) → ℝ) : Prop where
  continuous : Continuous N
  map_zero : N 0 = 0
  add_le : ∀ a b, N (a + b) ≤ N a + N b
  neg : ∀ a, N (-a) = N a
  smul : ∀ (c : ℝ) a, N (c • a) = |c| * N a
  norm_le : ∀ a, ‖a‖ ≤ N a
end KAM.Stability
namespace KAM.Nekhoroshev
open KAM.Weighted KAM.NormalForm
variable {n k : ℕ}

def slowTube (b : PartialBlock n k) (a : ℝ) (x : KAM.Planetary.Phase k) : Prop :=
  ∃ v ∈ b.S, ‖x-b.lam⁻¹ • v‖ ≤ a

theorem real_system_resonant (b : PartialBlock n k) {R s U : ℝ} {g : EC n k → ℂ}
    (hs : 0 < s) (hg : InClass b.base R s g) (hb : WBound b.base R s g U)
    {Λ : Set (Fin n → ℤ)}
    (hsupp : ∀ J ∈ polyNbhd b.base R, ∀ j : Fin n → ℤ, j ∉ Λ → coeff g J j = 0) :
    ∀ z ∈ b.realDom R,
      (fun i => (dtheta i g (extCx z)).re) ∈ KAM.Stability.resSpan Λ ∧
      (fun i => (dtheta i g (extCx z)).im) ∈ KAM.Stability.resSpan Λ := sorry

/-- Conditional helper only. T3 is proved by nonresonant integration or energy_free,
never forwarded as a premise of nonresonant, resonant, block or the provider. -/
theorem transfer_conditional (b : PartialBlock n k) (hbR : 0 < b.rB) (hbw : 0 < b.w) {R s r t d dx a : ℝ} {T : ENNReal}
    {H Ht : EC n k → ℂ} {Ψ : EC n k → EC n k} (hc : ExtConjHyp b R s r t H Ht Ψ)
    (Nrm : (Fin n → ℝ) → ℝ) (hN : KAM.Stability.IsActionNorm Nrm)
    (hd : 0 ≤ d) (hdx : 0 ≤ dx) (hdxr : dx < r) (ha : 0 < a) (hgap : d+a < r) (hT : 0 < T)
    (hdisp : ∀ z ∈ b.realDom r, Nrm (fastAction (reExtMap Ψ z)-fastAction z) ≤ d ∧
      ‖slowPair (reExtMap Ψ z)-slowPair z‖ ≤ dx)
    (hpre : ∀ y : ER n k, fastAction y = b.Ic → b.lam • slowPair y ∈ b.S →
      ∃ x ∈ b.realDom r, reExtMap Ψ x = y ∧ Nrm (fastAction x-b.Ic) ≤ d)
    (hT3 : ∀ J : Set ℝ, J.OrdConnected → (0:ℝ) ∈ J → ∀ y : ℝ → ER n k,
      ExtOrbit b r Ht J y → Nrm (fastAction (y 0)-b.Ic) ≤ d →
      (∀ u ∈ J, slowTube b dx (slowPair (y u))) →
      ∀ u ∈ J, ENNReal.ofReal |u| ≤ T → Nrm (fastAction (y u)-fastAction (y 0)) ≤ a)
    (F : ER n k → ER n k) (hF : EqOn F (realWfield b.c (realHamiltonianExt b R H)) (b.realDom R))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u)
    (hI : fastAction (y 0) = b.Ic) (hx : b.lam • slowPair (y 0) ∈ b.S)
    {t1 : ℝ} (ht1 : t1 ∈ J) (htT : ENNReal.ofReal |t1| ≤ T)
    (hstop : ∀ u ∈ uIcc 0 t1, b.lam • slowPair (y u) ∈ b.S) :
    ∀ u ∈ uIcc 0 t1, y u ∈ b.realDom R ∧ Nrm (fastAction (y u)-b.Ic) ≤ a+2*d := sorry

/-- Energy-source assumptions: the upper Hessian bound is only on real actions. -/
structure RealFastConvex (Ic : Fin n → ℝ) (R m M : ℝ) (h : (Fin n → ℂ) → ℂ) : Prop where
  m_pos : 0 < m
  m_le : m ≤ M
  hol : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n Ic} R)
  real : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n Ic} R →
    (h (KAM.realInclusion n I)).im = 0
  convex : ∀ I : Fin n → ℝ, ‖I-Ic‖ < R → ∀ v : Fin n → ℝ,
    m*euclid v^2 ≤ fderiv ℝ (fderiv ℝ (realPart h)) I v v
  hessian_real : ∀ I : Fin n → ℝ, ‖I-Ic‖ < R → ∀ v : Fin n → ℝ,
    euclid (fun i => fderiv ℝ (fderiv ℝ (realPart h)) I (Pi.single i 1) v) ≤ M*euclid v


/-- Fast convexity and Hessian bound; the frequency need have no upper bound. -/
structure FastConvex (Ic : Fin n → ℝ) (R m M : ℝ) (h : (Fin n → ℂ) → ℂ) : Prop where
  m_pos : 0 < m
  m_le : m ≤ M
  hol : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n Ic} R)
  real : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n Ic} R →
    (h (KAM.realInclusion n I)).im = 0
  convex : ∀ I : Fin n → ℝ, ‖I-Ic‖ < R → ∀ v : Fin n → ℝ,
    m*euclid v^2 ≤ fderiv ℝ (fderiv ℝ (realPart h)) I v v
  hessian : ∀ I ∈ polyNbhd {KAM.realInclusion n Ic} R, ∀ v : Fin n → ℂ,
    euclid (fun i => fderiv ℂ (fderiv ℂ h) I (Pi.single i 1) v) ≤ M*euclid v

/-- Restrict the complex Hessian bound to the real slice; no extra source premise. -/
theorem FastConvex.toRealFastConvex {Ic : Fin n → ℝ} {R m M : ℝ}
    {h : (Fin n → ℂ) → ℂ} (hh : FastConvex Ic R m M h) :
    RealFastConvex Ic R m M h := sorry

def NearResonance (Λ : Set (Fin n → ℤ)) (h : (Fin n → ℂ) → ℂ) (Ic : Fin n → ℝ) (δ : ℝ) : Prop :=
  ∀ v ∈ KAM.Stability.resSpan Λ, |∑ i, KAM.frequencyMap h Ic i*v i| ≤ δ*euclid v

theorem energy_free (b : PartialBlock n k) {r s m M ε η ζ δ : ℝ}
    {Λ : Set (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {g fs : EC n k → ℂ}
    (hr : 0 < r) (hs : 0 < s) (hh : RealFastConvex b.Ic r m M h)
    (hg : ext_class b r s g) (hf : ext_class b r s fs)
    (hgb : WBound b.base r s g (5*ε/4)) (hfb : WBound b.base r s fs η)
    (hsupp : ∀ J ∈ polyNbhd b.base r, ∀ j : Fin n → ℤ, j ∉ Λ → coeff g J j = 0)
    (hε : 0 < ε) (hη : 0 ≤ η) (hζ : 0 < ζ) (hηζ : η ≤ ζ) (hζε : ζ ≤ ε/Real.exp 1)
    (hsmall : ε ≤ m*r^2/2^12) (hSL : 16*k*b.c*s ≤ r)
    (hδ : 0 < δ) (hδr : δ ≤ m*r/16) (hnr : NearResonance Λ h b.Ic δ)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ExtOrbit b r (liftFast h+g+fs) J y)
    (hinit : euclid (fastAction (y 0)-b.Ic) < δ/(4*M))
    (hslow : ∀ u ∈ J, ∃ v ∈ b.S, ‖slowPair (y u)-b.lam⁻¹ • v‖ < r/2) :
    ∀ t ∈ J, |t| ≤ s*m*r/(20*M*ζ) → euclid (fastAction (y t)-fastAction (y 0)) ≤ r/4 := sorry

theorem nonresonant (b : PartialBlock n k) {s K α L p ε : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ}
    (hh : ExtNFHyp b s K α L p ε {0} h f)
    (hsmall : ε ≤ α*b.rB/(2^7*conjExp p*K))
    (F : ER n k → ER n k)
    (hF : EqOn F (realWfield b.c (realHamiltonianExt b b.rB (liftFast h+f))) (b.realDom b.rB))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u)
    (hinit : fastAction (y 0) = b.Ic) (hx : b.lam • slowPair (y 0) ∈ b.S)
    {t1 : ℝ} (ht1 : t1 ∈ J) (ht : |t1| ≤ s*b.rB/(5*ε)*Real.exp ((2*Real.pi*K*s)/6))
    (hstop : ∀ u ∈ uIcc 0 t1, b.lam • slowPair (y u) ∈ b.S) :
    ∀ u ∈ uIcc 0 t1, ‖fastAction (y u)-b.Ic‖ ≤ b.rB/2 := sorry

theorem resonant (b : PartialBlock n k) {s K α m M ε : ℝ}
    {Λ : AddSubgroup (Fin n → ℤ)} {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ}
    (hh : ExtNFHyp b s K α (Real.sqrt n*M) (9/8) ε (Λ:Set (Fin n → ℤ)) h f)
    (hconv : FastConvex b.Ic b.rB m M h) (hne : NearResonance (Λ:Set (Fin n → ℤ)) h b.Ic (m*b.rB/32))
    (hsmall : ε ≤ m*b.rB^2/2^14)
    (F : ER n k → ER n k)
    (hF : EqOn F (realWfield b.c (realHamiltonianExt b b.rB (liftFast h+f))) (b.realDom b.rB))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u)
    (hinit : fastAction (y 0) = b.Ic) (hx : b.lam • slowPair (y 0) ∈ b.S)
    {t1 : ℝ} (ht1 : t1 ∈ J) (ht : |t1| ≤ s*m*b.rB/(240*M*ε)*Real.exp ((2*Real.pi*K*s)/6))
    (hstop : ∀ u ∈ uIcc 0 t1, b.lam • slowPair (y u) ∈ b.S) :
    ∀ u ∈ uIcc 0 t1, euclid (fastAction (y u)-b.Ic) ≤ b.rB/2 := sorry

/-- Exactly the frozen source premises, bundled only for internal signatures. -/
structure PartialData (n k : ℕ) where
  G : Set (Fin n → ℝ)
  G' : Set (Fin n → ℝ)
  D : Set (KAM.Planetary.Phase k)
  ρ : ℝ
  g : ℝ
  m : ℝ
  Mc : ℝ
  h : (Fin n → ℂ) → ℂ
  hn : 2 ≤ n
  hk : 1 ≤ k
  hG : IsOpen G
  hGc : Convex ℝ G
  hG' : IsOpen G'
  hGc' : Convex ℝ G'
  hD : IsOpen D
  hρ : 0 < ρ
  hMc : 0 < Mc
  collar : ∀ I ∈ G, Metric.closedBall I ρ ⊆ G'
  hol : DifferentiableOn ℂ h (KAM.actionNbhd G' ρ)
  C2 : ContDiffOn ℂ 2 h (KAM.actionNbhd G' ρ)
  real : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd G' ρ →
    (h (KAM.realInclusion n I)).im = 0
  Hess : ∀ z ∈ KAM.actionNbhd G' ρ, ‖fderiv ℂ (fderiv ℂ h) z‖ ≤ Mc
  definite : HasDefiniteFastPart G' ρ g m h

def constants (a : PartialData n k) : PartialConstants := ⟨n,a.ρ,a.g,a.m,a.Mc⟩
def block_setting (a : PartialData n k) (μ : ℝ) (Ic : Fin n → ℝ) (r : ℝ) : PartialBlock n k :=
  ⟨Ic, innerCore a.D (3*(constants a).d μ/4), r, (constants a).d μ/4⟩
def signedH (a : PartialData n k) (σ : ℝ) (I : Fin n → ℂ) : ℂ :=
  (σ:ℂ)*a.h I/(2*(Real.pi:ℂ))
def signedF (_a : PartialData n k) (σ μ : ℝ) (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ)
    (z : EC n k) : ℂ :=
  (σ*μ/(2*Real.pi):ℝ)*P (Fin.append (fun i => (2*Real.pi:ℂ)*z.1 i) (slowPair z).1,
    Fin.append (fastAction z) (slowPair z).2)
/-- Pull physical slow coordinates back by the fixed block scale. -/
def slowScale (lam : ℝ) (z : EC n k) : EC n k :=
  (z.1, Fin.append (fastAction z)
    (Fin.append (fun i => (lam:ℂ)*(slowPair z).1 i) (fun i => (lam:ℂ)*(slowPair z).2 i)))
def blockPert (a : PartialData n k) (μ σ : ℝ) (Ic : Fin n → ℝ) (r : ℝ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) : EC n k → ℂ :=
  signedF a σ μ P ∘ slowScale (block_setting a μ Ic r).lam

theorem hessian (a : PartialData n k) (hne : a.G.Nonempty) :
    a.m ≤ a.Mc ∧ ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ Ic ∈ a.G, ∀ R : ℝ, 0 < R → R ≤ (constants a).r0 →
        FastConvex Ic R (constants a).m1 (constants a).M1 (signedH a σ)) ∧
      (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd a.G' a.ρ →
        (constants a).g1 ≤ ‖KAM.frequencyMap (signedH a σ) I‖) := sorry

/-- Explicit selected sign is a source witness, not a convexity conclusion. -/
def DefiniteSign (a : PartialData n k) (σ : ℝ) : Prop :=
  (σ = 1 ∨ σ = -1) ∧ ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ KAM.actionNbhd a.G' a.ρ →
    a.g ≤ ‖KAM.frequencyMap a.h I‖ ∧ ∀ v : Fin n → ℝ,
      a.m*(∑ i, (v i)^2) ≤ σ*fderiv ℝ (fderiv ℝ (realPart a.h)) I v v

theorem domain (a : PartialData n k) {μ σ R : ℝ} {Ic : Fin n → ℝ}
    (hμ : 0 < μ) (hσ : DefiniteSign a σ) (hIc : Ic ∈ a.G) (hR : 0 < R) (hRR : R ≤ (constants a).r0)
    (hd : (constants a).d μ ≤ a.ρ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (hP : IsPartialPerturbation a.G' a.D a.ρ P) :
    let b := block_setting a μ Ic R
    polyNbhd {KAM.realInclusion n Ic} R ⊆ KAM.actionNbhd a.G' a.ρ ∧
    ext_class b R (constants a).s (blockPert a μ σ Ic R P) ∧
    WBound b.base R (constants a).s (blockPert a μ σ Ic R P) ((constants a).eps μ) := sorry

/-- The geometric output consumed by Part 11; covering itself is an upstream theorem.
No new representation of the Part 8 lattice enumeration is introduced. -/
theorem block_data (a : PartialData n k) (hne : a.G.Nonempty) {μ σ : ℝ} (hμ : 0 < μ)
    (hε : (constants a).eps μ ≤ (constants a).eps0) (hσ : DefiniteSign a σ)
    (hκ : 6 ≤ (constants a).kappa μ) {Ic : Fin n → ℝ} (hIc : Ic ∈ a.G) :
    let c := constants a
    ∃ Λ : AddSubgroup (Fin n → ℤ), ∃ r : ℝ,
      Λ ≠ ⊤ ∧ c.rTheta μ ≤ r ∧ r ≤ c.R0/c.K μ ∧ 0 < r ∧
      IsNonresonant {KAM.realInclusion n Ic} (c.K μ/Real.sqrt n) ((9/8)*c.M1*c.K μ*r)
        (Λ:Set (Fin n → ℤ)) (signedH a σ) ∧
      (∃ δ : ℝ, 0 ≤ δ ∧ δ < c.m1*r/32 ∧ NearResonance (Λ:Set (Fin n → ℤ)) (signedH a σ) Ic δ) ∧
      FreqLipschitz {KAM.realInclusion n Ic} r (Real.sqrt n*c.M1) (signedH a σ) ∧
      c.eps μ ≤ c.m1*r^2/2^14 ∧
      c.eps μ ≤ ((9/8)*c.M1*c.K μ*r)*r/(2^7*9*(c.K μ/Real.sqrt n)) := sorry

/-- Physical period-one coordinates (no block-dependent coordinate scale). -/
def physicalDomain (Ic : Fin n → ℝ) (R w : ℝ) (S : Set (KAM.Planetary.Phase k)) : Set (ER n k) :=
  {z | ‖fastAction z-Ic‖ < R ∧ ∃ v ∈ S, ‖slowPair z-v‖ < w}

theorem domain_field (a : PartialData n k) {μ σ R : ℝ} {Ic : Fin n → ℝ}
    (hμ : 0 < μ) (hσ : DefiniteSign a σ) (hIc : Ic ∈ a.G) (hR : 0 < R) (hRR : R ≤ (constants a).r0)
    (hd : (constants a).d μ ≤ a.ρ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (hP : IsPartialPerturbation a.G' a.D a.ρ P) :
    let b := block_setting a μ Ic R
    let H := KAM.Planetary.degenerateHamiltonian (realPart a.h) (fun _ w => (P (complexifyPhase w)).re) μ
    EqOn (fun z => σ • realWfield (2*Real.pi) (converted H) z)
      (realWfield (2*Real.pi) (fun z => (liftFast (signedH a σ) (extCx z)+signedF a σ μ P (extCx z)).re))
      (physicalDomain Ic R b.w b.S) := sorry

theorem block (a : PartialData n k) (hne : a.G.Nonempty) {μ σ : ℝ} (hμ : 0 < μ)
    (hσ : DefiniteSign a σ) (hε : (constants a).eps μ ≤ (constants a).eps0)
    (hd : (constants a).d μ ≤ a.ρ) (hκ : 6 ≤ (constants a).kappa μ)
    (hSL : 256*k*a.ρ*(constants a).R0/((constants a).d μ)^2 ≤ (constants a).K μ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (hP : IsPartialPerturbation a.G' a.D a.ρ P)
    {Ic : Fin n → ℝ} (hIc : Ic ∈ a.G) (F : ER n k → ER n k)
    (hF : EqOn F (realWfield (2*Real.pi)
      (fun z => (liftFast (signedH a σ) (extCx z)+signedF a σ μ P (extCx z)).re))
      (physicalDomain Ic (constants a).r0 ((constants a).d μ/4)
        (innerCore a.D (3*(constants a).d μ/4))))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u) (hinit : fastAction (y 0) = Ic)
    (hx : slowPair (y 0) ∈ innerCore a.D (3*(constants a).d μ/4))
    {t1 : ℝ} (ht1 : t1 ∈ J) (htT : |t1| ≤ (constants a).blockTime μ)
    (hstop : ∀ u ∈ uIcc 0 t1, slowPair (y u) ∈ innerCore a.D ((constants a).d μ)) :
    ∀ u ∈ uIcc 0 t1, ‖fastAction (y u)-Ic‖ ≤ (constants a).R0/(2*(constants a).K μ) := sorry

theorem threshold (a : PartialData n k) (hne : a.G.Nonempty) :
    ∃ μ0 : ℝ, 0 < μ0 ∧ ∀ μ : ℝ, 0 < μ → μ < μ0 →
      let c := constants a
      c.eps μ ≤ c.eps0 ∧ c.d μ ≤ a.ρ ∧ 6 ≤ c.kappa μ ∧
      256*k*a.ρ*c.R0/(c.d μ)^2 ≤ c.K μ ∧ c.R0/(2*c.K μ) ≤ c.d μ/2 ∧
      μ⁻¹*Real.exp (μ^(-partialTimeExponent n)) ≤ c.blockTime μ := sorry


/-- The selected frozen definiteness witness is retained for assembly. -/
theorem hessian_at_sign (a : PartialData n k) (hne : a.G.Nonempty) {σ : ℝ}
    (hσ : DefiniteSign a σ) :
    a.m ≤ a.Mc ∧ ∀ Ic ∈ a.G, ∀ R : ℝ, 0 < R → R ≤ (constants a).r0 →
      FastConvex Ic R (constants a).m1 (constants a).M1 (signedH a σ) := sorry

/-- Generic real-preservation wrapper: Part 5 flow_e needs coordinate regrouping. -/
theorem flow_real (W : EC n k ≃L[ℂ] EC n k) {Ω : Set (EC n k)} {F : EC n k → EC n k} {ε : ℝ}
    (hF : KAM.Canonical.SmallField W Ω F ε)
    (hr : ∀ z : ER n k, extCx z ∈ Ω → extCx (extRe (F (extCx z))) = F (extCx z))
    {z : ER n k} (hz : extCx z ∈ KAM.Canonical.gaugeInterior W Ω (1/2)) {t : ℝ} (ht : |t| ≤ 1) :
    extCx (extRe (KAM.Canonical.flow F Ω t (extCx z))) = KAM.Canonical.flow F Ω t (extCx z) := sorry

/-- Taylor remainder bound, without choosing a maximum on an empty set. -/
theorem ext_taylor_bound {Ω : Set (EC n k)} (hΩ : IsOpen Ω) {c : ℝ}
    {φ u : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω) (hu : DifferentiableOn ℂ u Ω)
    {γ : ℝ → EC n k} (hγ : KAM.ODE.IsSolutionIn (wfield c φ) Ω (Icc 0 1) γ)
    (N : ℕ) (hN : 1 ≤ N) (B : ℝ)
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ‖extAd c φ N u (γ t)‖ ≤ B) :
    ‖∫ t in (0:ℝ)..1, (((1-t)^(N-1)/(N-1).factorial:ℝ):ℂ)*extAd c φ N u (γ t)‖ ≤ B/N.factorial := sorry

/-- Arbitrary holomorphic observables inherit weighted bracket invariance. -/
theorem symplectic_bracket {c : ℝ} {U V : Set (EC n k)} (hU : IsOpen U) (hV : IsOpen V)
    {Ψ : EC n k → EC n k} (hΨ : DifferentiableOn ℂ Ψ U) (hm : MapsTo Ψ U V)
    (hc : ExtCanonical c U Ψ) {u v : EC n k → ℂ}
    (hu : DifferentiableOn ℂ u V) (hv : DifferentiableOn ℂ v V) :
    ∀ z ∈ U, extBracket c (u ∘ Ψ) (v ∘ Ψ) z = extBracket c u v (Ψ z) := sorry

theorem symplectic_det {c : ℝ} (hc : 0 < c) {U : Set (EC n k)} (hU : IsOpen U)
    {Ψ : EC n k → EC n k} (hΨ : DifferentiableOn ℂ Ψ U) (hcanon : ExtCanonical c U Ψ) :
    ∀ z ∈ U, (fderiv ℂ Ψ z).det = 1 ∨ (fderiv ℂ Ψ z).det = -1 := sorry


/-- B.5(i) keeps its smaller image tube, used by the integral remainder. -/
theorem composition_domain (b : PartialBlock n k) (hk : 1 ≤ k) {R' s' R s ρ σ V : ℝ}
    {φ : EC n k → ℂ} (hc : ExtCompose b R' s' R s ρ σ V φ) :
    (∀ z ∈ Dom n b.base (R'-ρ) (s'-σ), scaled ρ σ (wfield b.c φ z) ≤ V/(ρ*σ)) ∧
    (∀ t : ℝ, |t| ≤ 1 → MapsTo (extFlow b R' s' ρ σ φ t)
      (Dom n b.base (R-ρ) (s-σ))
      (Dom n b.base (R-(1-V/(ρ*σ))*ρ) (s-(1-V/(ρ*σ))*σ))) := sorry

theorem composition_real (b : PartialBlock n k) (hk : 1 ≤ k) {R' s' R s ρ σ V : ℝ}
    {φ u : EC n k → ℂ} (hc : ExtCompose b R' s' R s ρ σ V φ)
    (hφ : extReal (Dom n b.base R' s') φ) (hu : extReal (Dom n b.base R s) u) :
    extReal (Dom n b.base (R-ρ) (s-σ)) (u ∘ extFlow b R' s' ρ σ φ 1) := sorry

/-- Smoothness and the full derivative sequence in the source Taylor statement. -/
theorem ext_taylor_regular {Ω : Set (EC n k)} (hΩ : IsOpen Ω) {c : ℝ}
    {φ u : EC n k → ℂ} (hφ : DifferentiableOn ℂ φ Ω) (hu : DifferentiableOn ℂ u Ω)
    {γ : ℝ → EC n k} (hγ : KAM.ODE.IsSolutionIn (wfield c φ) Ω (Icc 0 1) γ) :
    ContDiffOn ℝ ∞ (u ∘ γ) (Icc 0 1) ∧
    ∀ j : ℕ, ∀ t ∈ Icc (0:ℝ) 1,
      iteratedDerivWithin j (u ∘ γ) (Icc 0 1) t = extAd c φ j u (γ t) := sorry

def extForm (c : ℝ) (v w : EC n k) : ℂ :=
  (∑ i, (fastAction v i*w.1 i-v.1 i*fastAction w i)) +
    (c:ℂ)⁻¹*(∑ i, ((slowPair v).2 i*(slowPair w).1 i-(slowPair v).1 i*(slowPair w).2 i))

theorem symplectic_form {c : ℝ} (hc : 0 < c) {U : Set (EC n k)} (hU : IsOpen U)
    {Ψ : EC n k → EC n k} (hΨ : DifferentiableOn ℂ Ψ U) (hcanon : ExtCanonical c U Ψ) :
    ∀ z ∈ U, ∀ v w : EC n k,
      extForm c (fderiv ℂ Ψ z v) (fderiv ℂ Ψ z w) = extForm c v w := sorry

end KAM.Nekhoroshev

namespace KAM.Provider.Nekhoroshev
open KAM.Nekhoroshev
theorem partialConvex_nekhoroshev
    {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (G G' : Set (Fin n → ℝ)) (D : Set (KAM.Planetary.Phase k))
    (hG : IsOpen G) (hGc : Convex ℝ G)
    (hG' : IsOpen G') (hGc' : Convex ℝ G') (hD : IsOpen D)
    (ρ g m Mcomplex : ℝ) (hρ : 0 < ρ) (hMc : 0 < Mcomplex)
    (hcollar : ∀ I ∈ G, Metric.closedBall I ρ ⊆ G')
    (h : (Fin n → ℂ) → ℂ)
    (hhol : DifferentiableOn ℂ h (KAM.actionNbhd G' ρ))
    (hC2 : ContDiffOn ℂ 2 h (KAM.actionNbhd G' ρ))
    (hreal : ∀ I : Fin n → ℝ,
      (fun i => (I i : ℂ)) ∈ KAM.actionNbhd G' ρ → (h (fun i => (I i : ℂ))).im = 0)
    (hHess : ∀ z ∈ KAM.actionNbhd G' ρ, ‖fderiv ℂ (fderiv ℂ h) z‖ ≤ Mcomplex)
    (hdef : HasDefiniteFastPart G' ρ g m h) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ →
      ∀ P : (Fin (n + k) → ℂ) × (Fin (n + k) → ℂ) → ℂ,
      IsPartialPerturbation G' D ρ P → ∀ C : ℝ, 0 < C →
      ∀ z : ℝ → KAM.Planetary.Phase (n + k),
      IsSolutionOn
        (KAM.Planetary.degenerateHamiltonian (realPart h)
          (fun _ w => (P (complexifyPhase w)).re) μ)
        {I | KAM.Planetary.fast (b := k) I ∈ G} (Set.Icc 0 C) z →
      KAM.Planetary.fast (b := k) (z 0).2 ∈ innerCore G (μ ^ partialDriftExponent n) →
      ∀ t ∈ Set.Icc 0
        (min C (μ⁻¹ * Real.exp (μ ^ (-partialTimeExponent n)))),
      (∀ u ∈ Set.Icc 0 t,
        (KAM.Planetary.slow (a := n) (z u).1, KAM.Planetary.slow (a := n) (z u).2)
          ∈ innerCore D (μ ^ partialDriftExponent n)) →
      ‖KAM.Planetary.fast (b := k) (z t).2 - KAM.Planetary.fast (b := k) (z 0).2‖
        ≤ μ ^ partialDriftExponent n / 2 :=
  sorry

end KAM.Provider.Nekhoroshev
end
```
