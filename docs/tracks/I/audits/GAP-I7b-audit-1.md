# GAP-I7b independent audit 1

Overall verdict: **PASS WITH NOTES**. All four scoped exports pass the source/signature,
premise, proof and hygiene audit. The sole lint exception is the expressly permitted stale
generated `KAM.lean`; it is not a package finding. No frozen theorem is proved or sealed by
this infrastructure package, so a provider-to-anchor seal verdict is not applicable.

Audited checkout: `/root/code/KAM-inp-gi7b`, HEAD
`a2e38a9c097d412f4fc9f73c1c7798ad02f08907`; comparison ref `inp` was
`ab3459def1182c7cf70d8b920eded286c93b2737`.
The complete `git diff inp...HEAD` adds only `KAM/Iso/TransferStepNodes.lean` (251 lines).
The existing untracked handoff was read and left untouched. This report is the only
repository edit made by the auditor; temporary Lean probes were confined to
`.lake/abi-scratch/` and removed after checking.

## Authority and scope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the absolute audit brief
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the local
`docs/tracks/I/audits/GAP-I7b-handoff.md` including AUDIT FOCUS and the 05:10 ruling,
`docs/tracks/I/statement.md`, and the GAP-I7b section of
`/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-I.md:316`.
The user's explicit report destination overrides the generic brief's MAIN-worktree destination.
Only the new module is under audit; landed modules and frozen definitions were inspected
as dependencies to interpret its statements.

No declaration in this slice is marked SIGNED and no separate signature file is assigned
by the design or handoff. The design's three exports and the ruling's extra square-root
clause are all present. No additional graph node is assigned to this module. The parent
`bpI:p7:orbit-maps-e` is audited here only for the explicitly assigned missing k clause;
its existing periodicity/reality/general-orbit exports are outside the change.

## Node and declaration results

Every row was compared with its complete NODE record, especially SOURCE_HYPOTHESES,
SOURCE_QUANTIFIERS and SOURCE_CONCLUSION, and the cited blueprint text.
All Lean declarations below are in namespace `KAM.Iso`.

| Node; graph record; blueprint location | Declaration; Lean location | Verdict | Fidelity and premise analysis |
|---|---|---|---|
| `stepI:p7:he-smooth`; `docs/graph/I/DEPGRAPH.md:8797`; `blueprint-I/parts/p7-delaunay.tex:59` (enclosing result 51–57) | `he_smooth`; `KAM/Iso/TransferStepNodes.lean:43` | PASS | Arbitrary real μ, then both primaries, then all phase points / collision-free points. Explicit quadratic identity, global analyticity of that quadratic, positivity on Wμ, and real analyticity of radius and inverse radius on Wμ. Remaining terms are the displayed quadratic polynomial and are proved analytic on all phase space. Final C∞ assertion is included. No local output is assumed. |
| `bpI:p7:orbit-maps-e` (k clause only); graph 9180; blueprint 170–179 | `orbitMapC_k_holomorphic`; Lean 94 | PASS | Only 0 < e₁ < 1 precedes the coordinates. Uses exactly `orbitDomC e₁`, i.e. (ℓ,e) in the source tube and L ≠ 0, with g,k unrestricted. Proves positive real part, holomorphy of principal k, k² identity, agreement with real sqrt, and holomorphy after replacing coordinate 4 by k. Real-sqrt equality holds for every real e with e² < 1, a stronger auxiliary conclusion than restriction to the tube. |
| `stepI:p7:tr-cf`; graph 10653; blueprint 457 (setting 430–454) | `tr_cf`; Lean 146 | PASS | K and its compact/nonempty/cone premises, radial safety, arbitrary B ⊆ 2πK, μ small, arbitrary J and curve, solution premise, then every t ∈ J, in source order. Exports action membership, deDom, U(δ₂), collision freedom. Reality is enforced by the real carrier and `phaseToC`. No openness/nonemptiness condition is added to B or J. |
| `stepI:p7:tr-chain`; graph 10719; blueprint 461 (setting 430–454) | `tr_chain`; Lean 170 | PASS | Same source-only ordered premises as tr-cf; arbitrary J. Exports the original derivative, equality of Hamilton fields, chain derivative with DQ(Sz̃)(S X̃), equality to the physical Hamilton field and the frozen restricted field, exact radius, elements, and energy identity. D(Q∘S)X is represented by DQ(Sz̃)(S X), using the genuine linear S; this is the design's required form. No proved dependency output occurs as a premise. |

`SafeAction K` unpacks to compactness, nonemptiness and `0 < G < L` on K
(`KAM/Iso/ComplexDomain.lean:46`), exactly the source standing data. The constants
`exactDelta K`, `exactMu2 K` and perturbation `tildeF K μ` instantiate the already chosen
exact-ham/period-one data, rather than introducing new dependencies on B, J, μ or the curve.
The radius formula uses the physical Euclidean `planeLength`, definitionally the frozen
`radius`, while the phase carriers retain `Fin 2 → ℝ` and their stipulated ambient norms.

For he-smooth, polynomiality is represented by the explicit coordinate polynomial rather
than a separate polynomial-witness predicate. Its radiusSq identity is reproved by the
finite sum, and its remaining expression is quadratic by unfolding radiusSq. This matches
the design's explicit analytic export and establishes the literal polynomial fact.

## Definitions, soundness and consumers

There are **no new def, abbrev, structure, instance or other public declarations** beyond
the four theorems. Definition classification: empty. Local `have` bindings introduce no
new objects or bundled assumptions.

Inspected the frozen radiusSq/radius, primaries, CollisionFree, restrictedHamiltonian,
restrictedVectorField, IsHamiltonianSolutionOn and the ordinary definitions used in the
exports. The total extension `restrictedHamTotal` agrees by rfl with the subtype Hamiltonian
at collision-free points (`KAM/Iso/RestrictedHam.lean:54`). Neither its values at collisions
nor the fallback zero in `exactDelta` is used: positivity/existence is recovered internally
from hK and hρ, and every physical evaluation/derivative has established collision freedom.
The principal complex power is differentiated only on the slit plane, obtained from
Re(1-e²) > 0. Replacing coordinate 4 preserves both defining conditions of orbitDomC.

The transfer proof first derives membership from the actual solution premise. In tr-chain,
Hamiltonian agreement is established on an **open neighborhood** via `periodOne_real`, not
only on the orbit or on B; this justifies equality of derivatives. The proof then uses the
linear conversion and the genuine Delaunay derivative/symplectic field identity. Radius,
elements and energy are recovered internally. The proofs do not assume analyticity,
collision freedom, field agreement, chain-rule conclusions, or energy identities as inputs.

The recursive local import audit finds 51 frozen imports, all definitions, all manifest
state SEALED. There is no frozen theorem import (including no DRAFT_SORRY anchor), and no
provider import anywhere in the KAM import closure. Production imports obey quarantine.
No helper export reuses an existing short name: repository search outside this module
returns no occurrences of any of its four names. All exports live in KAM.Iso; no root-level
shadow or new instance is introduced. Existing consumers are not changed by this module.

## Independent checks

All Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The build wrapper itself supplies `nice -n 5`. No heartbeat, recursion or synthesis override
was used. No clean, cache fetch, dependency update, generated-root rewrite or git mutation
was performed.

1. Full diff and protected paths:

   ```text
   git diff inp...HEAD
   git diff inp...HEAD --name-status
   A  KAM/Iso/TransferStepNodes.lean
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   [empty; exit 0]
   git diff --check inp...HEAD
   [empty; exit 0]
   ```

2. Targeted default-budget build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gi7b KAM.Iso.TransferStepNodes
   [inp-gate] slot 1 acquired 05:19:37 for KAM.Iso.TransferStepNodes
   Build completed successfully (9116 jobs).
   exit 0
   ```

   Only replayed dependency warnings: `KAM/Kepler/Energy.lean:106:35` unused `hm`
   and `:106:48` unused `hκ`. No warning in the audited module.

3. Kernel replay (single invocation; this package has one lemma module and no provider):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.TransferStepNodes
   replaying KAM.Iso.TransferStepNodes
   exit 0
   ```

4. Fresh-name type/application and axiom probe:

   `.lake/abi-scratch/GAPI7bAudit.lean` imported the audited module and reproduced each
   complete declaration signature under a fresh `audit_…` name. Its proof applied the
   corresponding export to all explicit binders in order: `μ`, `h0 h1`, or
   `hK hρ hB hμ hz`. All four elaborated. There is no frozen provider signature or seal
   body to compare for this package; the probe does not purport to perform an anchor seal.

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPI7bAudit.lean
   'KAM.Iso.he_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Iso.orbitMapC_k_holomorphic' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Iso.tr_cf' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Iso.tr_chain' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

5. Hygiene: the new file has 251 physical lines, maximum line width 100 characters,
   copyright, `module`, public imports, module documentation and exposed public
   noncomputable section. Searches for forbidden proof tokens, EuclideanSpace and
   any set_option returned no matches. No duplicate public helper name was found.

6. Repository lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1267 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1 (sole diagnostic: the expressly permitted generated-root staleness)
   ```

## Errata, deviations and limits

No suspected source/blueprint defect or introduced mathematical deviation was found in
this slice. The explicit k-clause export resolves the scoped omission identified in the
handoff's ruling; it does not independently re-audit every claim of the parent node.
The audit uses the pinned local graph/blueprint contracts and does not assert a new external
source verification. No frozen anchor, campaign theorem, or unrelated graph gap is closed
by this report. KAM.lean regeneration remains the orchestrator's stated merge responsibility.
