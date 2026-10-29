# GAP-I3T independent audit 2

Date: 2026-10-29. Worktree: `/root/code/KAM-inp-gi3t`.
Audited HEAD: `0ec235cb0b298325da7df3a3eccce6f43d2d35f6`.
Comparison `inp`: `74976f317ab6852d2a7222801accf8ce39ba0615`.

## Verdict

**FAIL for literal closure of `stepI:p3:tori-ig1` under the AUDIT FOCUS.**
The repair fixes audit 1's output-premise failure for the new `tori_ig1_node`:
it constructs its torus internally. Its fixed-ray conclusion is sound and substantially
stronger than the previous helper. However, it remains a local, one-ray theorem rather
than the node's both-sign conclusion with the proposition's quantifier structure.
The required source-level bundle is still absent. This is an interface/completeness
failure, not a kernel or mathematical proof failure.

The parent `bpI:p3:tori`'s missing real-analyticity and real-energy properties are now
available for its actual witnesses through the first two helpers. That narrow over-claim
can be replaced with explicit references to these consequences. This does not by itself
close the stronger literal-node requirement in the audit focus.

No frozen anchor is supplied or changed by this package; seal readiness is not applicable.
Tracks N/P have no changed Lean modules.

## Authorities and scope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the handoff, and audit 1.
The user's exact worktree report destination overrides the generic brief's main-worktree
output instruction. No production repair or state-changing git operation was performed.

Controlling contracts: `docs/graph/I/DEPGRAPH.md:6331–6371` and `:6434–6466`;
`blueprint-I/parts/p3-iso-local-charts.tex:371–405`, especially `:394–397`.
Also inspected the track-I statement, `PART123-LEAN-DESIGN.md` (node table, D16–D18,
Part 5 consumers and signatures), GAP-I3T in the offload plan at lines 306–314,
the frozen `IsoenergeticKam` statement and relevant frozen definitions, and the
patch/application, torus-output and real-restriction dependencies.

The full `git diff inp...HEAD` contains:

- `KAM/Iso/Charts/ToriIG1.lean`: new 181-line module, the audit's production scope.
- `KAM/Iso/Charts/Tori.lean`: `@[expose]` added to `ApplyOut` and `ApplyLocal`, plus
  wrapping; their binders and bodies are unchanged. Recorded as an additional package
  change outside the handoff's named scope, not silently ignored or expanded into a new audit.
- The handoff and audit 1. The handoff describes commit `2167804f`, not current HEAD.

The worktree was clean initially. All five declarations in `ToriIG1` are unsigned;
there is no new provider or signed theorem requiring frozen-type/seal-body matching.
No existing signed type is changed by the two exposure annotations.

## Declaration ledger

| Node / clause | Declaration (namespace prefix as shown) | Verdict | Reason |
|---|---|---|---|
| T1 real restriction | `KAM.Iso.Confinement.TorusOutput.realRestriction_analyticOnNhd`, line 39 | PASS as helper | Positive strip width and holomorphy imply real analyticity on all real angles. |
| T3 real energy | `KAM.Iso.Confinement.TorusOutput.realHamiltonian_realRestriction_eq`, line 48 | PASS as helper | Reality identifies the restriction with the complex torus; strip energy and real part yield `E`. |
| Conditional T1/T2/T3/T5 | `KAM.Iso.Charts.ToriSide.ig1_literal`, line 64 | PASS as conditional helper only | Still assumes the output `ToriSide`, now explicitly documented as a helper. Cannot independently count as node closure. |
| Fixed-ray clause definition | `KAM.Iso.Charts.Ig1Clauses`, line 97 | PASS as definition | Faithful T1/T2/T3/T5 predicate for one fixed `γ, ωs, I, K, st`; includes the base energy and exact norm identity. |
| `stepI:p3:tori-ig1` | `KAM.Iso.Charts.tori_ig1_node`, line 115 | FAIL as full literal node; PASS as local theorem | Constructs one torus on one supplied patch/ray, under per-ray constant bounds. Does not state the proposition's both-sign, common-uniform-constant conclusion. |
| Parent's omitted real clauses | First two helpers applied to both existing `tori` witnesses | PASS as consequences | They preserve each witness; no replacement torus is needed. A strengthened source-level bundle remains unstated. |

## Remaining contract gap, and what was repaired

`DEPGRAPH.md:6442` requires **“SOURCE_QUANTIFIERS: as in the proposition”**.
The proposition at `:6338–6340` and blueprint `:372–374` fixes patches and both rays,
then common uniform constants, then quantifies over the perturbation and initial data,
and returns a patch and tori **for each sign**. The audit focus requires one declaration
stating the node, and explicitly distinguishes unsigned node exports from deliberately
narrowed signed interfaces.

Current `ToriIG1.lean:115–128` instead has the shape:

```text
HeadData → B'.Nonempty → IG1Statement → IsPatch … → IsRay … → |m| < δm →
  ∃ C₁ C₂ C₃ > 0, ∀ C_K ε₁, [bounds for this ray] →
    ∀ f ε, PerturbData … → ε < ε₁ →
      ∀ I₀ ∈ closure B', ‖I₀ - c‖ < ρc → ∀ E, [energy window] →
        ∃ K st, Ig1Clauses … γ ωs (Ψ (E,m)) K st
```

This preserves the important local order: ray and constants precede `f, ε, I₀, E`.
It also fixes the old output-premise problem: `applyLocal_exists` is called at line 130,
`hA` produces `Kinf, sinf` at lines 143–144, and `toriSide_of_applyOut` is used inside
the proof at lines 145–146. No `ToriSide` or `ApplyOut` is an input of this new theorem.
`HeadData`/`PerturbData` are source-data bundles, patches/rays are the already fixed
geometric setup, and the `IG1Statement` premise is the explicit D18 quarantine convention.
Do not retain audit 1's old F1 against this new theorem.

Nevertheless there is only one `ωs`, one `m`, and one returned pair `K, st`. There is
no both-sign conclusion, patch-cover selection, or common positive uniform-threshold
existence statement. The theorem existentially chooses its own per-ray `C_i`; it is
not stated for the previously chosen family used by the parent uniform construction.
Instantiating this local result twice and proving a common uniform choice is a valid
possible assembly, but that assembly is not a declaration in this module. D17 explicitly
permits a one-ray specialization for `points`; it does not provide a signed narrowing
of this new unsigned node export. No signature or ruling found changes this node's
“as in the proposition” requirement to a one-ray contract.

The remaining failure is therefore literal completeness under the requested contract.
The code establishes the local analytic content, so this is not evidence that the
source result is false. A source-ordered both-sign theorem, preserving the fixed rays
and supplying the strengthened clauses for the same witnesses, would resolve it.
The name `tori_ig1` is optional; an equivalent declaration with that statement is needed.

The offload plan at lines 311–314 calls the source-level bundle “Optional” and prescribes
output-taking helpers. The handoff's more specific audit focus imposes the literal-node
condition. The omitted bundle remains unacceptable for that condition when no other
export has the complete statement. This conflict was already noted in audit 1.

## Proof and definition review

`Ig1Clauses` is the only new definition. Its whole body is a conjunction of the intended
properties, with the supplied ray retained across T2 and T5. It introduces no fallback,
junk value, hidden hypothesis, or weakened real/complex carrier. It uses max norms on
`Fin 2 → ℝ` / `Fin 2 → ℂ`. `st • ωs ≠ 0` is explicit; nonresonance follows from positive
`γ`, the Diophantine inequality and `st > 1`. The base-frequency identity uses the same
`ωs` and a scalar greater than two.

Existing `realRestriction` is `Re ∘ K ∘ realInclusion` throughout its carrier;
`IsRealOnReals` identifies its inclusion with `K` at real points.
The frozen `realHamiltonian` is the real part of `h + f` evaluated at real inclusions.
The new real-energy helper uses exactly these bodies. Real points lie in the strip by
`rhoInf_pos hd.hs`. There is no loss of the real-theta quantifier.

The local node proof derives the energy window using `hp.ball_h`, derives the margin
from the uniform bound, obtains the base point/frequency from `points`, and proves
`ωs ≠ 0` from its ray norm lower bound and `mh > 0`. Lines 155–170 explicitly pay
`C₃ F₁ ε/(γ²ρ⁴) ≤ C_K ε`; denominator positivity and `ε ≥ 0` are justified.
Lines 176–177 prove the exact norm identity by `sub_smul` and `norm_smul`.
No unsound proof, extra conclusion-shaped input to `tori_ig1_node`, or mathematical
source defect was found.

## Independent checks

All Lean/Lake operations, including lint's ABI elaboration, were sequential, with
`LEAN_NUM_THREADS=1` and `nice -n 5`. No clean, update, cache fetch, resource override,
or package mutation was used. Probe files were confined to `.lake/abi-scratch/`.

### Build

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gi3t KAM.Iso.Charts.ToriIG1
[inp-gate] slot 2 acquired 05:28:45 for KAM.Iso.Charts.ToriIG1
Build completed successfully (3264 jobs).
exit 0
```

The only warning replayed was the inherited unused `[NormedSpace ℝ E]` section variable
in `KAM.ODE.gen_exit`, `KAM/ODE/Exit.lean:36`. No audited-module warning was printed.

### Axioms and elaborated interface

Probe `.lake/abi-scratch/GAP_I3T_audit2.lean` imported the audited module, printed axioms
of all four public theorems, checked `@tori_ig1_node`, and printed `Ig1Clauses`.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAP_I3T_audit2.lean
'KAM.Iso.Confinement.TorusOutput.realRestriction_analyticOnNhd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Iso.Confinement.TorusOutput.realHamiltonian_realRestriction_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Iso.Charts.ToriSide.ig1_literal' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Charts.tori_ig1_node' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

The elaborated type confirmed the one-patch/one-ray interface reproduced above;
printing the predicate confirmed its exact fixed-ray conjunction. The probe was deleted.

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.Charts.ToriIG1
replaying KAM.Iso.Charts.ToriIG1
exit 0
```

No provider module belongs to this package. A recursive project-import scan found
106 reachable project modules and no provider or frozen theorem module. In particular,
there is no imported DRAFT_SORRY anchor. The contextual I-G1 anchor is SEALED in
`manifest/frozen-anchors.json:1649`; this module uses the D18 premise, not that import.

### Static and protected-path checks

The audited file is 181 lines, maximum width 99 characters, no lines over 100.
It has copyright, `module`, public imports, module documentation and `public section`;
`Ig1Clauses` has `@[expose]`. Forbidden-token/override and `EuclideanSpace` scans are
empty. A repository declaration scan found each of the five new public short names
only at its declaration. The two `_root_` declarations extend the intended
`KAM.Iso.Confinement.TorusOutput` namespace; no harmful root shadow was found.

```text
git diff --check inp...HEAD
exit 0; no output
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
exit 0; no output
```

### Repository lint

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1267 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The only reported failure is the stale generated root, explicitly permitted by the
brief. It was not regenerated. Hygiene is PASS WITH NOTES independently of the
literal-node completeness FAIL. Final `git diff --check` passed; only this report
was left untracked, and HEAD remained the audited commit.

## Errata, deviations and limits

No new suspected pinned-source mathematical erratum or frozen-statement defect.
The remaining issue is the unsigned node's narrower interface and the previously
recorded offload-plan/audit-focus conflict. The module documentation at lines 25–27
and 111–114 overstates its compliance with the full node's source quantifiers:
it describes the implemented local order correctly but does not expose both signs.

The handoff is stale: lines 4 and 18–22 omit the round-2 theorem/definition and the
exposure edits in `Tori.lean`. Its claim that the original three exports alone state
literal node closure remains too strong. The parent real clauses are derivable;
that narrower fact is independently verified above.

Audit edits are limited to this report and the temporary scratch probe. The graph
node should remain open under the stated literal-export acceptance rule.
