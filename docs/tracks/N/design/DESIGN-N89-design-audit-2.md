# Delta design audit 2: N89 Revision 2

**Overall verdict: PASS WITH NOTES.** F1 and F2 are resolved, and N1 is fully addressed. No signature, consumer, frozen-object, or package blocker remains in this delta. N3 is a nonblocking deprecated-import note. This is approval of the revised design contract, not a theorem proof or frozen-root closure.

Target: `/root/code/KAM-inp-design-n89`, branch `inp-design-n89`, revision commit `aaa81c4dc07dc445a6290405562a7f3d727536c6`. Compared `HEAD^...HEAD` and `inp...HEAD`, read Revision 2, the handoff, audit brief, AGENTS.md, PLAN.md and DECISIONS.md. The committed revision changes only the design Markdown. The earlier audit report is preserved.

## Delta boundary and inventory

The current signatures SHA-256 is `01270a67c964001a1f6f86a2416ce572fee94f326c34cec43fcef7de0fea4b88` (532 lines). Appendix A and the fresh scratch copy match it. Declaration-by-declaration comparison against the first design's committed Appendix A, ignoring comments and order, establishes:

- 86 old declarations → **88** revised declarations; no removed declaration.
- Only `projection_matrix` changes its type. Its former type/body is preserved verbatim as `projection_matrix_lattice`.
- `projection_distance_subspace` is the other added declaration. All other types and bodies, including the raw parameter records, `elementary`, `m_le_M`, `block_hyp`, `block_stab` and `thm1`, are unchanged.
- All **15/15** upstream excerpts still match `NPart67Signatures.lean` literally. Its hash and both blueprint hashes equal the design snapshot.
- Inventory by **STATEMENT_SOURCE file**, without assuming a colon after the part number, yields **83/83** unique graph nodes and design rows, with no missing or extra row. The newly represented `bpN:p9#data` is a pre-existing graph node; the source and graph were not changed.

The source claims, affected graph records, general projection formulas, early parameter ownership, all consumers affected by the renamed export, and retained main stability types were checked directly. Unchanged signatures retain audit 1's mathematical assessment; their unchanged status was verified rather than inferred from the handoff.

## Earlier findings and revision findings

| ID | Severity / status | Re-check and disposition |
|---|---|---|
| F1 | MAJOR — CLOSED | Signatures L187–192 now quantify over arbitrary independent real columns. L173–177 supplies arbitrary-subspace distance attainment. L194–196 retains the old lattice matrix formula. This matches `bpN:p8:projection`, `stepN:p8:pr-alg`, `stepN:p8:pr-dist` (blueprint p8:53–66; graph `N-p8.nodes.md:328,360,387`). |
| F2 | MAJOR — CLOSED | Design §6 assigns raw `CoverParams` and `CoverParams.Valid` to early P1 `Interfaces/CoverParams.lean`; `Poschel.Elementary` owns all four constants and `elementary`. G7 imports the early interface and owns only the geometry-dependent covering declarations. P2 explicitly imports Elementary. The stated DAG and wave order now agree with the exact types. |
| N1 | LOW — CLOSED | Design §5 and the `m_le_M` docstring now disclose omitted positivity of m and M and weakened nonnegative ell. The unchanged stronger signature remains true by the nonzero transverse-vector argument. |
| N2 | LOW — CLOSED; audit-1 correction | My earlier 82/82 inventory missed `bpN:p9#data` because the matcher required a colon after p9. The designer's correction is right. The corrected source-file-based inventory gives 83/83; this report supersedes that count without editing audit 1. |
| N3 | LOW — OPEN, nonblocking | The new early module's planned `Mathlib.Data.Real.Sqrt` import is a working deprecated compatibility import. The audit probe emits Lean's explicit replacement recommendation. Use `Mathlib.Analysis.Real.Sqrt` for the production module and its DAG entry. No signature type or source contract changes. |

### F1 fidelity and consumer closure

`projection_matrix` uses `Matrix (Fin n) (Fin d) ℝ`, real column independence, the real column span and exactly `A * (A.transpose * A)⁻¹ * A.transpose`. There is no integer, rational-span, lattice, or saturation premise. Independent columns imply invertibility of the Gram matrix; d=0 and n=0 are valid stronger extensions, with the empty-span projector zero. No assertion depends on a junk matrix inverse.

`projection_distance_subspace` explicitly gives `compProj V w` in the dot-orthogonal complement, its achieved distance equal to `euclid (proj V w)`, and a lower bound against every point in that complement. Together these express the source minimum, rather than just a lower bound or a distance with changed ambient norm. The norm is still the explicit Euclidean function on `Fin n → ℝ`.

Existing lattice consumers can use `projection_matrix_lattice` with exactly their former binders, and `projection_distance` is unchanged. G2's proof plan identifies the basis column span with `lattice Λ` and supplies real independence from G1; these are proof obligations, not added assumptions. Arbitrary-subspace `geom_formula` and downstream lattice-volume/geometric arguments remain applicable. The new names are reflected in the inventory and G2 ownership table. No production consumer was silently redirected to a narrower signature.

### F2 package closure

The early raw record has only real numerical fields; its Valid predicate has the source dimension, positivity and A-bound fields. Neither references a lattice, a projection, a Hamiltonian or a late theorem. Its existing body/type was moved, not strengthened. `theoremCover` depends only on this record and the early constants, and the last conjunct of `elementary` depends only on its Valid predicate.

An audit-only probe placed `Theorem1Setting`, `setting`, `thmA`, `thmEps0`, `thmK`, `theoremCover` and `elementary` **before every lattice declaration**, with the unchanged upstream excerpts and early parameter record. It elaborated successfully, exercising precisely the previously hidden late dependency. This is a dependency-order probe, not an implementation of the proposed production modules.

The revised design assigns **12 packages / 14 files**, each estimated at ≤650 lines (P1: 40+200+250). G2's larger real-column contract remains below the 1500-line cap. The G1→…→G7 and P1→P2→P3→P4→P5 dependencies remain acyclic; the early P1 interface is ready for G7 in wave 7. The restriction that upstream projection/energy modules must not import the new G2 module is preserved. **Package verdict: PASS, with N3 import hygiene.**

### N1 mathematical re-check

Take I in the nonempty P and a nonzero real ξ perpendicular to the frozen frequency at I (n≥2). Nonnegative ell excludes the strict first disjunct in quasi-convexity. The real restriction of the Hessian bound gives

```text
m * euclid ξ ^ 2 ≤ Q(I)[ξ,ξ] ≤ M * euclid ξ ^ 2.
```

Since `euclid ξ ^ 2 > 0`, m≤M follows without either m>0 or M>0. No conclusion-shaped hypothesis was introduced; the signature still does not assume m≤M.

### N3 proposed import correction

Locators: design §6 DAG and the paragraph beginning “P1 owns Interfaces/CoverParams.lean”. The exact probe diagnostic is:

```text
'Mathlib.Data.Real.Sqrt' has been deprecated: please replace this import by

import Mathlib.Analysis.Real.Sqrt
```

Use the module-interface form in the planned production file:

```lean
public import Mathlib.Analysis.Real.Sqrt
```

The current compatibility import still resolves, so this is not an elaboration failure of the supplied signatures and does not reopen F2.

## Per-signature verdicts

One row per current declaration (88 total, 35 theorem bodies). Lines refer to the current original signatures file. Unchanged rows preserve audit 1's contract verdict after exact delta comparison; revised/relocated declarations are assessed above. There is no FAIL requiring a replacement signature.

| Lean name and line | Blueprint label | Verdict | Reason |
|---|---|---|---|
| `KAM.NormalForm.zBall` (L29) | `bpN:p6:setting / cond-L` | PASS | Literal upstream interface excerpt. |
| `KAM.NormalForm.freq` (L31) | `bpN:p6:setting / cond-L` | PASS | Literal upstream interface excerpt. |
| `KAM.NormalForm.dotC` (L33) | `bpN:p6:setting / cond-L` | PASS | Literal upstream interface excerpt. |
| `KAM.NormalForm.IsNonresonant` (L35) | `bpN:p6:setting / cond-L` | PASS | Literal upstream interface excerpt. |
| `KAM.NormalForm.FreqLipschitz` (L38) | `bpN:p6:setting / cond-L` | PASS | Literal upstream interface excerpt. |
| `KAM.Stability.cpx` (L46) | `bpN:p7:setting` | PASS | Literal upstream interface excerpt; frozen bridges checked. |
| `KAM.Stability.realNbhd` (L48) | `bpN:p7:setting` | PASS | Literal upstream interface excerpt; frozen bridges checked. |
| `KAM.Stability.realStrip` (L50) | `bpN:p7:setting` | PASS | Literal upstream interface excerpt; frozen bridges checked. |
| `KAM.Stability.realH` (L53) | `bpN:p7:setting` | PASS | Literal upstream interface excerpt; frozen bridges checked. |
| `KAM.Stability.hessR` (L56) | `bpN:p7:setting` | PASS | Literal upstream interface excerpt; frozen bridges checked. |
| `KAM.Stability.resSpan` (L58) | `bpN:p7:gradient` | PASS | Literal upstream real-span interface. |
| `KAM.Stability.IsOrthProj` (L61) | `bpN:p7:resonance-data` | PASS | Literal upstream interface excerpt. |
| `KAM.Stability.resSpace` (L65) | `bpN:p7:resonance-data` | PASS | Literal upstream interface excerpt. |
| `KAM.Stability.IsCloseToRes` (L67) | `bpN:p7:resonance-data` | PASS | Literal upstream interface excerpt. |
| `KAM.Stability.IsQuasiConvex` (L70) | `bpN:p7:resonance-data` | PASS | Literal upstream interface excerpt. |
| `KAM.Nekhoroshev.CoverParams` (L83) | `bpN:p8:covering` | PASS | Unchanged raw record; P1 early interface owns it. |
| `KAM.Nekhoroshev.CoverParams.Valid` (L92) | `bpN:p8:covering` | PASS | Unchanged source-only fields; no geometry dependency. |
| `KAM.Nekhoroshev.Lattice` (L103) | `bpN:p8:lattice` | PASS | Subgroup, real span, Euclidean cutoff and orthogonal resonance; zero rank included. |
| `KAM.Nekhoroshev.lattice` (L104) | `bpN:p8:lattice` | PASS | Subgroup, real span, Euclidean cutoff and orthogonal resonance; zero rank included. |
| `KAM.Nekhoroshev.latticeDim` (L105) | `bpN:p8:lattice` | PASS | Subgroup, real span, Euclidean cutoff and orthogonal resonance; zero rank included. |
| `KAM.Nekhoroshev.integerReal` (L106) | `bpN:p8:lattice` | PASS | Subgroup, real span, Euclidean cutoff and orthogonal resonance; zero rank included. |
| `KAM.Nekhoroshev.eBall` (L107) | `bpN:p8:lattice` | PASS | Subgroup, real span, Euclidean cutoff and orthogonal resonance; zero rank included. |
| `KAM.Nekhoroshev.resonance` (L108) | `bpN:p8:lattice` | PASS | Subgroup, real span, Euclidean cutoff and orthogonal resonance; zero rank included. |
| `KAM.Nekhoroshev.basisMatrix` (L109) | `bpN:p8:lattice-basis` | PASS | Exact integer bases, real independence, unimodular changes and equal-rank inclusion. |
| `KAM.Nekhoroshev.lattice_basis` (L112) | `bpN:p8:lattice-basis` | PASS | Exact integer bases, real independence, unimodular changes and equal-rank inclusion. |
| `KAM.Nekhoroshev.integer_independent_real` (L119) | `bpN:p8:ext-indep` | PASS | Explicit new scalar-extension obligation; no assumed external closure. |
| `KAM.Nekhoroshev.lattice_resonance` (L122) | `bpN:p8:lattice` | PASS | Subgroup, real span, Euclidean cutoff and orthogonal resonance; zero rank included. |
| `KAM.Nekhoroshev.latticeBasis` (L126) | `bpN:p8:lattice-basis` | PASS | Exact integer bases, real independence, unimodular changes and equal-rank inclusion. |
| `KAM.Nekhoroshev.lattice_basis_change` (L129) | `bpN:p8:lattice-basis` | PASS | Exact integer bases, real independence, unimodular changes and equal-rank inclusion. |
| `KAM.Nekhoroshev.lattice_basis_sub` (L136) | `bpN:p8:lattice-basis` | PASS | Exact integer bases, real independence, unimodular changes and equal-rank inclusion. |
| `KAM.Nekhoroshev.gram` (L141) | `bpN:p8:volume-def` | PASS | Integer Gram determinant square root, empty determinant 1; basis choice auxiliary. |
| `KAM.Nekhoroshev.volume_def` (L144) | `bpN:p8:volume-def` | PASS | Integer Gram determinant square root, empty determinant 1; basis choice auxiliary. |
| `KAM.Nekhoroshev.projection_exists_unique` (L148) | `bpN:p8:projection` | PASS | Unchanged general projector characterization; source matrix/distance coverage now supplied. |
| `KAM.Nekhoroshev.proj` (L152) | `bpN:p8:projection` | PASS | Unchanged general projector characterization; source matrix/distance coverage now supplied. |
| `KAM.Nekhoroshev.compProj` (L155) | `bpN:p8:projection` | PASS | Unchanged general projector characterization; source matrix/distance coverage now supplied. |
| `KAM.Nekhoroshev.projection` (L157) | `bpN:p8:projection` | PASS | Unchanged general projector characterization; source matrix/distance coverage now supplied. |
| `KAM.Nekhoroshev.projection_zero` (L167) | `bpN:p8:projection` | PASS | Unchanged general projector characterization; source matrix/distance coverage now supplied. |
| `KAM.Nekhoroshev.resonanceDistance` (L169) | `bpN:p8:projection` | PASS | Unchanged general projector characterization; source matrix/distance coverage now supplied. |
| `KAM.Nekhoroshev.projection_distance_subspace` (L173) | `bpN:p8:projection / stepN:p8:pr-dist` | PASS | PASS F1: arbitrary real subspace; orthogonality, attained distance and all-competitor bound. |
| `KAM.Nekhoroshev.projection_distance` (L179) | `bpN:p8:projection` | PASS | Unchanged lattice corollary, compatible with the general theorem. |
| `KAM.Nekhoroshev.projection_matrix` (L187) | `bpN:p8:projection` | PASS | PASS F1: arbitrary independent real columns; exact column span and Gram inverse. |
| `KAM.Nekhoroshev.projection_matrix_lattice` (L194) | `bpN:p8:projection` | PASS | Old integer-basis formula retained verbatim under this name. |
| `KAM.Nekhoroshev.addVector` (L198) | `bpN:p8:lattice-volume` | PASS | Correct sum lattice, basis-independent volume, index, cyclic and Hadamard formulas. |
| `KAM.Nekhoroshev.lattice_volume` (L201) | `bpN:p8:lattice-volume` | PASS | Correct sum lattice, basis-independent volume, index, cyclic and Hadamard formulas. |
| `KAM.Nekhoroshev.lattice_volume_index` (L214) | `bpN:p8:lattice-volume` | PASS | Correct sum lattice, basis-independent volume, index, cyclic and Hadamard formulas. |
| `KAM.Nekhoroshev.lattice_volume_cyclic` (L219) | `bpN:p8:lattice-volume` | PASS | Correct sum lattice, basis-independent volume, index, cyclic and Hadamard formulas. |
| `KAM.Nekhoroshev.lattice_volume_hadamard` (L222) | `bpN:p8:lattice-volume` | PASS | Correct sum lattice, basis-independent volume, index, cyclic and Hadamard formulas. |
| `KAM.Nekhoroshev.klattice` (L226) | `bpN:p8:klattice / maximal` | PASS | Weaker K-lattice maximality preserved; no saturation or short-basis premise. |
| `KAM.Nekhoroshev.maximalK` (L229) | `bpN:p8:klattice / maximal` | PASS | Weaker K-lattice maximality preserved; no saturation or short-basis premise. |
| `KAM.Nekhoroshev.maximal` (L233) | `bpN:p8:klattice / maximal` | PASS | Weaker K-lattice maximality preserved; no saturation or short-basis premise. |
| `KAM.Nekhoroshev.zone` (L249) | `bpN:p8:blocks` | PASS | Strict zones, zero-rank whole space, empty out-of-range strata. |
| `KAM.Nekhoroshev.zoneStratum` (L252) | `bpN:p8:blocks` | PASS | Strict zones, zero-rank whole space, empty out-of-range strata. |
| `KAM.Nekhoroshev.blocks` (L255) | `bpN:p8:blocks` | PASS | Strict zones, zero-rank whole space, empty out-of-range strata. |
| `KAM.Nekhoroshev.blocks_cover` (L258) | `bpN:p8:blocks-cover` | PASS | Finite family and covering for arbitrary frequency; n=0 extension is true. |
| `KAM.Nekhoroshev.sqrt` (L263) | `bpN:p8:sqrt` | PASS | Both inequalities retained; positivity follows from lower bound 1. |
| `KAM.Nekhoroshev.geom_formula` (L266) | `bpN:p8:geom-formula` | PASS | Stronger arbitrary-real-subspace formulation; all projection identities retained. |
| `KAM.Nekhoroshev.geometric` (L274) | `bpN:p8:geometric` | PASS | Exact positive parameters, ratio range, two nonresonance conclusions. |
| `KAM.Nekhoroshev.CoverParams.lam` (L284) | `bpN:p8:covering` | PASS | Exact source parameters; arbitrary carrier/map; no Hamiltonian assumptions. |
| `KAM.Nekhoroshev.CoverParams.radius` (L287) | `bpN:p8:covering` | PASS | Exact source parameters; arbitrary carrier/map; no Hamiltonian assumptions. |
| `KAM.Nekhoroshev.CoverParams.alpha` (L290) | `bpN:p8:covering` | PASS | Exact source parameters; arbitrary carrier/map; no Hamiltonian assumptions. |
| `KAM.Nekhoroshev.CoverParams.delta` (L292) | `bpN:p8:covering` | PASS | Exact source parameters; arbitrary carrier/map; no Hamiltonian assumptions. |
| `KAM.Nekhoroshev.actionBlock` (L294) | `bpN:p8:covering` | PASS | Exact source parameters; arbitrary carrier/map; no Hamiltonian assumptions. |
| `KAM.Nekhoroshev.covering` (L297) | `bpN:p8:covering` | PASS | Exact source parameters; arbitrary carrier/map; no Hamiltonian assumptions. |
| `KAM.Nekhoroshev.cutoffs` (L313) | `bpN:p8:cutoffs` | PASS | Correct inclusions and Kg >= sqrt(n) Ka direction; zero-rank closeness true. |
| `KAM.Nekhoroshev.Theorem1Setting` (L326) | `bpN:p9:setting` | PASS | Unchanged S1-S4 record; Poschel.Setting owns it. |
| `KAM.Nekhoroshev.setting` (L345) | `bpN:p9:setting` | PASS | Unchanged alias; Poschel.Setting owns it. |
| `KAM.Nekhoroshev.thmA` (L347) | `bpN:p9:setting / bpN:p9#data / bpN:p9:s-blocks#data` | PASS | Unchanged constants; explicit owner Poschel.Elementary; no late geometry dependency. |
| `KAM.Nekhoroshev.thmEps0` (L348) | `bpN:p9:setting / bpN:p9#data / bpN:p9:s-blocks#data` | PASS | Unchanged constants; explicit owner Poschel.Elementary; no late geometry dependency. |
| `KAM.Nekhoroshev.thmK` (L349) | `bpN:p9:setting / bpN:p9#data / bpN:p9:s-blocks#data` | PASS | Unchanged constants; explicit owner Poschel.Elementary; no late geometry dependency. |
| `KAM.Nekhoroshev.theoremCover` (L351) | `bpN:p9:setting / bpN:p9#data / bpN:p9:s-blocks#data` | PASS | Unchanged constants; explicit owner Poschel.Elementary; no late geometry dependency. |
| `KAM.Nekhoroshev.m_le_M` (L359) | `bpN:p9:m-le-M` | PASS | Unchanged true stronger type; all premise drops now disclosed (N1 closed). |
| `KAM.Nekhoroshev.elementary` (L366) | `bpN:p9:elementary` | PASS | Unchanged joint type; early-interface dependency probe passes (F2 closed). |
| `KAM.Nekhoroshev.local_real_regularity` (L380) | `stepN:p9:om-max#local-real-regularity` | PASS | Actual frozen realPart/frequencyMap; correct real restriction of Hessian. |
| `KAM.Nekhoroshev.FrequencyBall` (L389) | `bpN:p9:omega0 / ext-compact` | PASS | Guarded compact nonempty exact Euclidean ball; attained supremum and M-radius bound. |
| `KAM.Nekhoroshev.FrequencyBall.points` (L396) | `bpN:p9:omega0 / ext-compact` | PASS | Guarded compact nonempty exact Euclidean ball; attained supremum and M-radius bound. |
| `KAM.Nekhoroshev.FrequencyBall.maximum` (L399) | `bpN:p9:omega0 / ext-compact` | PASS | Guarded compact nonempty exact Euclidean ball; attained supremum and M-radius bound. |
| `KAM.Nekhoroshev.frequency_maximum` (L402) | `bpN:p9:omega0 / ext-compact` | PASS | Guarded compact nonempty exact Euclidean ball; attained supremum and M-radius bound. |
| `KAM.Nekhoroshev.omega0_radius` (L409) | `bpN:p9:omega0 / ext-compact` | PASS | Guarded compact nonempty exact Euclidean ball; attained supremum and M-radius bound. |
| `KAM.Nekhoroshev.omega0Ball` (L412) | `bpN:p9:omega0 / ext-compact` | PASS | Guarded compact nonempty exact Euclidean ball; attained supremum and M-radius bound. |
| `KAM.Nekhoroshev.omega0` (L416) | `bpN:p9:omega0 / ext-compact` | PASS | Guarded compact nonempty exact Euclidean ball; attained supremum and M-radius bound. |
| `KAM.Nekhoroshev.full_rank_zone` (L425) | `stepN:p9:t1-b#full-rank-zone` | PASS | Correct top-lattice identity and strict frequency threshold equivalence. |
| `KAM.Nekhoroshev.block_hyp` (L434) | `bpN:p9:block-hyp` | PASS | Exact singleton restrictions and every Part-7 numerical premise; no orbit conclusion assumed. |
| `KAM.Nekhoroshev.block_frequency_radius` (L465) | `bpN:p9:block-stab#frequency-size` | PASS | Exact rLambda/2 ball; strict guard follows from rLambda <= r0 and r0 > 0. |
| `KAM.Nekhoroshev.blockBall` (L471) | `bpN:p9:block-stab#frequency-size` | PASS | Exact rLambda/2 ball; strict guard follows from rLambda <= r0 and r0 > 0. |
| `KAM.Nekhoroshev.blockAdm` (L480) | `bpN:p9:block-stab` | PASS | Exact stopped statement; max/Euclidean distinction, full rank and Omega=0 handled. |
| `KAM.Nekhoroshev.local_field` (L486) | `bpN:p9:block-stab#local-field` | PASS | Open singleton tube; indicator and total Hamiltonian fields agree locally. |
| `KAM.Nekhoroshev.block_stab` (L496) | `bpN:p9:block-stab` | PASS | Exact stopped statement; max/Euclidean distinction, full rank and Omega=0 handled. |
| `KAM.Nekhoroshev.thm1` (L512) | `bpN:p9:thm1` | PASS | Joint branches and constants retained; hI supplies nonempty P; no containment assumed. |

## Consumers, frozen objects, definitions

**Consumers: PASS.** Rechecked the p8/p9 source and graph consumers and searched I/P literal `\Nref{bpN:p8:` and `\Nref{bpN:p9:` uses (none directly). Their earlier Part-3 ODE uses are unchanged by this revision. The general geometry remains Hamiltonian-free and accepts arbitrary action carriers/maps. Part 11's `block-data` (p11c:146–151) can still use b=1/32 and A=40M1/m1, the singleton frequency map, unchanged `covering`/`cutoffs`, and the retained lattice projection corollaries. Part 10's `hypotheses-check` and `cf-orbit/cf-branch` still instantiate the unchanged joint `thm1` with the frozen real field and two-sided derivatives, period-one h,f, width s/2, and the exact paired-2π cancellation. There is no new containment or frequency-lower-bound premise. Parts 7 and 12 have no newly affected consumer contract.

**Frozen objects: PASS.** Re-read `KAM.frequencyMap`, `hamiltonianVectorField`, `realHamiltonian`, and Nekhoroshev `realPart`/`IsSolutionOn`. Their direct use and the upstream real-field/frequency bridges are unchanged. The new projection theorems involve only the existing abstract projector and explicit real dot product; no parallel frozen object is introduced. No provider or frozen theorem is imported or closed by the design.

**Definitions/totality: PASS.** The only moved structures are unchanged source-only numerical data. The new public statements are the two general projection contracts; they add no definitions or global instances. Canonical projection choice, basis-independent volume, guarded exact frequency maxima, strict exceptional threshold, and multiplication-form full-rank/zero-frequency time semantics are unchanged. Empty and zero-rank carriers remain handled as before. No new constant dependence, weakened stability conclusion, or source premise was found in the delta.

## Independent validation

All Lean-related commands were sequential, under `LEAN_NUM_THREADS=1`, through the existing gate, which uses `nice -n 5 lake env lean` against the shared `/root/code/KAM-inp` build. No resource-budget override or production rebuild was used.

1. **Fresh original-signature check (one invocation):**

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-n89 .drafts/scratch/N89Signatures.lean
   ```

   Exit **0**, exactly **35** `declaration uses sorry` warnings, no other Lean diagnostics. The scratch copy is byte-identical to the original and Appendix A.

2. **Reordered dependency/API/axiom probe:** same gate with `.lake/abi-scratch/N89R2AuditProbe.lean`. The final run exits **0**, with 35 sorry warnings and the single N3 import-deprecation warning, no errors. The first audit-generated version left an orphaned declaration docstring after moving its declaration; it failed with `unexpected token 'section'; expected 'lemma'`. Removing orphaned docstrings in the probe fixed that audit harness error. Neither the original signatures nor the required scratch copy was changed to obtain success.

   The probe checked these **16 Mathlib declarations** with their actual types: `Submodule.basisOfPid`, `Pi.basisFun`, `AddSubgroup.toIntSubmodule`, `Matrix.PosDef.conjTranspose_mul_self`, `Matrix.PosDef.det_pos`, `Matrix.det_mul`, `Matrix.det_transpose`, `Matrix.det_fromBlocks₁₁`, `Matrix.isUnit_iff_isUnit_det`, `Int.isUnit_iff`, `Module.Basis.invertibleToMatrix`, `LinearIndependent.iff_fractionRing`, `Matrix.rank_eq_finrank_span_cols`, `IsCompact.exists_isMaxOn`, `Real.rpow_natCast`, `Real.rpow_mul`. These are compatible proof ingredients; scalar extension, basis-span identification and Gram/index work remain actual proofs to write.

   `#print axioms` for `projection_matrix`, `projection_distance_subspace`, `projection_matrix_lattice`, `elementary`, `geometric`, `covering`, `block_hyp`, `block_stab`, `thm1` each returns exactly:

   ```text
   [propext, sorryAx, choice, Quot.sound]
   ```

   This does not certify proof closure. The audit probe is deleted after validation.

3. **Repository lint**, with the designer's existing unmodified PATH adapter serializing its internal ABI check through the gate:

   ```sh
   LEAN_NUM_THREADS=1 PATH="$PWD/.drafts/scratch/gated-bin:$PATH" scripts/lint_sources.sh
   ```

   Exit **0**, exact output:

   ```text
   check_lean_modules: PASS (412 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

4. **Inventory and hygiene:** 83/83 source-file-selected graph nodes; 88 signature rows; 15/15 literal upstream excerpts; declaration-level delta limited to the intentional projection generalization and two additions; hashes and Appendix equality checked. Final whitespace/status receipts follow below.

`git diff --check` and `git diff --no-index --check /dev/null /root/code/KAM-inp-design-n89/docs/tracks/N/design/DESIGN-N89-design-audit-2.md` both exit **0**. Final `git status --short` lists the pre-existing untracked audit-1 report and the newly authored audit-2 report only; no tracked file is modified. The requested scratch refresh remains byte-identical to the original. The temporary audit probe has been deleted.

## Handoff limits and errata

File authored: `/root/code/KAM-inp-design-n89/docs/tracks/N/design/DESIGN-N89-design-audit-2.md` only, plus the explicitly requested scratch refresh and temporary probe (deleted). The audit-1 report, design, original signatures, production code, source blueprints, graph, manifest, frozen files and generated files were not edited. No state-changing git command was used.

No new suspected mathematical source defect or numerical misprint is asserted. The inherited Pos93 maximality ambiguity, omitted volume/dimension arguments, strengthened radius repair, sqrt(n) norm adaptation, and strict exceptional-branch deviation remain recorded in the design and were not silently changed. PDFs were not independently re-audited. The upstream Part-6/7 design remains an implementation dependency, and any later change to its exact types requires another consumer check. The present PASS WITH NOTES closes this revision's design-audit blockers while leaving every proof obligation unpaid.
