# N11-L2 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the scoped N11-L2 implementation. The sole public export,
`KAM.Nekhoroshev.energy_free`, has the exact signed type and establishes every graph node assigned to
Energy. The notes concern the permitted stale generated root and inherited dependency warnings.
No proof, signature, carrier, or completeness failure was found.

This is an infrastructure-package verdict. No frozen anchor is proved by this slice; in particular
`KAM.Nekhoroshev.partialConvex_nekhoroshev` is not seal-ready on the strength of this audit.
Its frozen body remains `by sorry`; provider/frozen equality and seal-body probes are inapplicable to
this helper-only package. The corresponding signed-helper type and application-body probes were run.

## Scope and evidence

- Worktree/report: `/root/code/KAM-inp-n11l2`; the user's exact local report destination overrides the
  generic brief's main-worktree output instruction.
- Audited HEAD: `b19962d03977264ce867dd14badd15e4c032604a`.
- Compared `inp`: `eff45716c45678ce9fbb21a346ab5821d70a823b`.
- Read the package brief, AGENTS.md, PLAN.md, DECISIONS.md, N11-L2 handoff, N11 design and both design
  audits, signed interface, relevant track statement/frozen theorem and definitions, and p11c L78–119.
- Inspected `git diff inp...HEAD`: two additions, Energy (535 lines) and inherited EnergyIdentity
  (429 lines). The four L2 commits are `1fd97529`, `4a1c509f`, `1d47762a`, `b19962d0`.
  Only `KAM/Nekhoroshev/Partial/Energy.lean` receives a package verdict. L1 statements and their use
  were inspected as dependencies; this does not re-audit every L1 body.
- Energy SHA-256: `4484ca88b8907700575d0bded02efd64a7dd32e8e7c854078928296cc91ff19a`.
- Signed delivery `/root/code/KAM-inp/.drafts/design/N11Signatures.lean` SHA-256:
  `23bd2cc2645243b3357acccda6e04ff69fad4d055963010025c582f3c886a0e4`.
- Design SHA-256: `f0fd0d111b6abd5c335a5ea144135a07b28be326f3d699f3c2761c46ad097609`.
- p11c SHA-256: `5d6fe7fc6b09459b6bf307596832695fcda1b62bf5292bd926d84bf216f7b7ea`.

## Signed statement and consumer fit

Energy L509–523, up to the proof separator, equals the delivery's L583–597 byte for byte.
A fresh declaration copied from that signature, with a proof applying `energy_free` to every explicit
binder in order, elaborated. Both directions of `type_of%` assignment elaborated as well.

`RealFastConvex` carries the real-slice upper Hessian bound only. The proof uses `hessian_real` through
Cauchy–Schwarz and a real mean-value argument; it never asks for the complex upper Hessian bound,
a frequency upper bound, a normal-form theorem, or a stability conclusion as a premise. This closes
the implementation concern corresponding to design audit 1 F1. The lower convexity and upper Hessian
hypotheses apply on the ordinary maximum-norm real ball; all Euclidean segments used in the proof
are shown to lie there. The drift and projection estimates use the literal `euclid` function.

All interval, endpoint, initial strictness, support, slow margin, and numerical assumptions are retained.
`WBound` allows numerical majorants rather than requiring the parameters to equal the norms, which
also admits the source's actual norms. `NearResonance` is the dual projection bound; the projection
argument at L61–71 realizes its needed norm consequence. There is no added premise or weakened
conclusion. No unsigned public export is presented as a graph node.

The intended N11-M2 consumer obtains this same real bundle via `FastConvex.toRealFastConvex`, as
required by design L367 and audit 2. Its p11c L119 use requires precisely radius r/4 and time
`s*m*r/(20*M*ζ)`, which this export supplies. No deliberate signature narrowing needs a further
consumer repair here. Actual future Resonant integration is outside this slice.

## Complete graph-node ledger

Names below are in `KAM.Nekhoroshev`. Line references without a filename refer to Energy.lean.
All nine internal steps assigned by design L250–258, together with the parent, are covered below
(the three energy substeps are listed separately).

| Node | Lean declaration / proof location | Verdict | Evidence |
|---|---|---|---|
| `bpN:p11:energy-free` | `energy_free`, L509–531 | PASS | Exact signed theorem; first exit followed by contradiction, valid for positive and negative t. |
| `stepN:p11:ef-tube` | `ef_mem_realDom_of_tube`, L211; `ef_contra.hτI/hτdom/hseg`, L411–426 | PASS | Strict fast distance <r/2 and explicit slow witness give the smaller real tube; all Taylor segments stay in the fast ball. |
| `stepN:p11:ef-adm` | `ef_freq_lip`, L269; `ef_contra.hB4`, L429–445 | PASS | Real Hessian implies M-Lipschitz frequency; orthogonal projection contraction gives 5δ/4. |
| `stepN:p11:ef-en` | `ef_contra`, L455–503 | PASS | Taylor, conserved energy, split pairing and endpoint norm bounds give hmain with all displayed constants. |
| `stepN:p11:ef-en-energy` | `ef_energy`, L277–291; `hen/hg1/hg0/hf1/hf0`, L467–471 | PASS | Actual extended Hamiltonian's real energy is constant; indicator restriction is removed only at orbit points inside its domain. |
| `stepN:p11:ef-en-taylor` | `ef_taylor_segment`, L102–162; `htay/hconv`, L455–463 | PASS | Lagrange Taylor remainder at an interior segment point, with lower bound mΔ²/2. |
| `stepN:p11:ef-en-split` | `ef_contra.hsplit/hPd`, L472–487 | PASS | Self-adjointness gives the exact longitudinal/transverse split and 5δΔ/4 estimate. |
| `stepN:p11:ef-id` | imported L1 `energy_identity_re`; used within `transverse_pairing` at EnergyIdentity L372–373 | PASS | Identity is proved upstream and consumed, not assumed; the real scalar form is sufficient for the energy proof. |
| `stepN:p11:ef-C` | `ef_theta_bound`, L299; `ef_bracket_bound`, L307; `hpair`, L447–453 | PASS | Supplies all four bounds to L1 `transverse_pairing`: 5ηε/(rs), η/(es), Mr/4, 5δ/4. |
| `stepN:p11:ef-contra` | `ef_arith`, L333–372; application L504–505 | PASS | Exact rational contradiction using e≥2; no decimal approximation or strengthened smallness premise. |

The bracket estimate applies `bracket` with losses r/2,s/2 and `bracket_dominated` with
`16*k*b.c*s ≤ r`. At real points the auxiliary fixed width in `realDom` is harmless: the proof's
real-domain characterization L204–208 and the positive-width bounds give the required complex-strip
membership. The angular derivative estimate holds already at real points of the full domain.

The arithmetic differs harmlessly from the blueprint's sharper decimal bounds. With E=mr²,
η≤ε/2, the non-projection terms total at most
`(19/4)/4096 + 21/2560 = 767/81920 < 3/256` times E.
The projection term is at most `5E/256`; the left side is `E/32`, leaving exactly `3E/256`.
Thus replacing the blueprint's estimate of 1/e by 1/2 still proves the source conclusion.

## Private declaration inventory

Every private helper is local to Energy, with an `ef_` prefix. None is a new public contract.

| Declaration (line) | Verdict | Role |
|---|---|---|
| `ef_euclid_nonneg` (37) | PASS | Nonnegative square root. |
| `ef_euclid_le_sum` (39) | PASS | Euclidean size bounded by coordinate absolute sum. |
| `ef_orth_sq` (44) | PASS | Projection quadratic identity. |
| `ef_le_of_sq_le` (48) | PASS | Scalar cancellation, nonnegative comparison. |
| `ef_orth_euclid_le` (54) | PASS | Orthogonal projection contraction. |
| `ef_proj_freq_le` (61) | PASS | Dual near-resonance to projected-frequency bound. |
| `ef_realPart_contDiffOn` (75) | PASS | Holomorphic regularity restricted to actual realPart. |
| `ef_hess_abs_le` (88) | PASS | Real Hessian bilinear bound via Cauchy–Schwarz. |
| `ef_taylor_segment` (102) | PASS | Real segment Taylor formula. |
| `ef_hess_lipschitz` (165) | PASS | Mean-value inequality tested against the gradient difference. |
| `ef_mem_realDom_iff` (204) | PASS | Removes the automatic real-angle strip condition. |
| `ef_mem_realDom_of_tube` (211) | PASS | Literal base witness from S, coordinatewise smallness. |
| `ef_fast_continuousOn` (245) | PASS | Continuous projection of the actual solution. |
| `ef_seg_mem` (253) | PASS | Euclidean length bounds imply maximum-norm ball membership. |
| `ef_freq_lip` (269) | PASS | Instantiates the real Hessian mean-value bound. |
| `ef_energy` (277) | PASS | Extended real energy conservation. |
| `ef_re_abs_le` (293) | PASS | Weighted bound controls the real value. |
| `ef_theta_bound` (299) | PASS | Correct η/(es) Euclidean angular derivative bound. |
| `ef_bracket_bound` (307) | PASS | Half-tube bracket majorant. |
| `ef_arith` (333) | PASS | Conditional arithmetic helper; hmain is derived at its use. |
| `ef_abs_le_of_mem_uIcc` (375) | PASS | Two-sided time restriction. |
| `ef_exp_one_ge_two` (380) | PASS | Elementary e≥2. |
| `ef_contra` (385) | PASS | Conditional first-exit helper; exit conditions are proved by exit_ball. |

## Definitions and import classification

There are **no new `def`, `abbrev`, `structure`, or instances** in Energy. Local `set` bindings are
literal gradients, differences, one-variable segment restrictions and the positive time majorant;
none introduces junk or a fallback. The module adds one public theorem and 23 private theorems.
There is no reused public helper short name or root-level shadow.

The existing objects consumed here are literal coordinate projections/real inclusions (`fastAction`,
`slowPair`, `extCx`), the weighted domain and Fourier bounds (`Dom`, `InClass`, `WBound`, `coeff`),
the real source bundle (`RealFastConvex`), the dual resonance predicate (`NearResonance`), and the
actual extended weighted Hamiltonian orbit (`ExtOrbit`). The off-domain zero in the existing
`realHamiltonianExt` is never used to infer an on-domain energy or orbit fact: membership is
supplied at every such use. Empty S cannot create a spurious proof because hslow supplies an S
witness, and h0/hy supply a genuine orbit point. Degenerate dimensions do not change any carrier.

Direct imports are Bracket, EnergyIdentity and Stability.Setting. A recursive source-import check
found 100 KAM modules, 26 frozen definition modules, all manifest `SEALED`; no provider or frozen
theorem module occurs in this closure, hence no `DRAFT_SORRY` theorem dependency. The sole result's
axiom check independently confirms absence of sorryAx.

## Independent verification

All audit Lean commands were serialized and used `LEAN_NUM_THREADS=1` and `nice -n 5`.
No resource override, clean, update, cache fetch, or frozen/manifest/generated-root edit was made.

1. **Targeted build**, exact command:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 \
     /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
     /root/code/KAM-inp-n11l2 KAM.Nekhoroshev.Partial.Energy
   ```

   Exit **0**. Output included `[inp-gate] slot 2 acquired 20:41:53 for
   KAM.Nekhoroshev.Partial.Energy` and `Build completed successfully (3280 jobs).`
   Replayed warnings came from Gradient, Coordinates and RealSystem; none came from Energy.

2. **Fresh exact-signature/application probe**:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11L2Audit.lean
   ```

   Exit **0**. The probe copied the signed theorem under `audit_energy_free`, proved it by
   `exact energy_free b hr hs hh hg hf hgb hfb hsupp hε hη hζ hηζ hζε hsmall hSL hδ hδr hnr
   hJ h0 hy hinit hslow`, and checked both assignments:

   ```lean
   example : type_of% @audit_energy_free := @energy_free
   example : type_of% @energy_free := @audit_energy_free
   #print axioms energy_free
   ```

   Exact output:

   ```text
   'KAM.Nekhoroshev.energy_free' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. **Kernel replay**, exact command:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
     KAM.Nekhoroshev.Partial.Energy KAM.Nekhoroshev.Partial.EnergyIdentity
   ```

   Exit **0**. Complete verbose output:

   ```text
   replaying KAM.Nekhoroshev.Partial.EnergyIdentity
   replaying KAM.Nekhoroshev.Partial.Energy
   ```

4. **Source lint**, exact command:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely the brief-permitted generated-root exception. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (939 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No other lint failure occurred. The generated root was left untouched as required.

5. **Static integrity**: `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.
   `git diff --check inp...HEAD` exits **0**, with no output. A scoped forbidden-token/resource
   scan found no matches. Energy has **535 lines**, maximum **100 Unicode characters per line**,
   and the required copyright/module/public imports/module docstring/public section structure.
   Probe files and audit logs under `.lake/abi-scratch/` were removed after checking.
   `git diff --no-index --check /dev/null docs/tracks/N/audits/N11-L2-audit-1.md` also exits **0**.
   Final status has only this new report and the pre-existing untracked handoff.

## Notes, uncertainties, errata and deviations

- No suspected pinned-source or blueprint defect was discovered in the audited energy slice.
  The known design-audit open-ball/adjoint-locator notes concern other nodes and remain outside
  this verdict; no source/graph/manifest was silently repaired.
- The e≥2 rational arithmetic is a valid alternative proof, with the same signed statement and
  constants. It is an implementation difference from the blueprint's decimal route, not an
  additional assumption or source correction.
- This audit certifies Energy and its checked dependency use, not the whole N11 chain, the planned
  M2 integration, N11-G's separate geometry dispatch gate, or the frozen root.
- Only this report was added by the auditor. The pre-existing untracked N11-L2-handoff.md was
  preserved. No state-changing git operation was performed.
