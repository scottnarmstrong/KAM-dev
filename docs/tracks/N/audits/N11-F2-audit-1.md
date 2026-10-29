# N11-F2 independent package audit 1

Overall verdict: **FAIL for consumer-complete integration**. The two F2 modules implement their amended signed contracts correctly, with no proof-soundness defect found. The remaining failure is a design/consumer edge: the signed standalone `iterative` contract cannot always supply the new `hc : 0 < b.c` required by `canonical_map`. This is not a counterexample to `canonical_map` or to the frozen headline.

## Scope and immutable inputs

Audited HEAD: `1d5683c5c28952f72babc8c760c22b4221b0b2cd`; comparison `inp` at inspection: `4a5b757e944936d0ae6e9269a1170dc7098e4240`.
The literal requested `git diff inp...HEAD` warns of multiple merge bases and selects
`eedc66febf1e2749337a502351ab1515c1779c15`; the other merge base is
`c198ff11a966d692e9ba3fd91709b4de7a6740d5`.
The full diff adds five files (1254 lines): F2's `ExtFlow.lean` and `CanonicalMap.lean`, plus E1's
`Flow.lean`, `Symplectic.lean`, `SymplecticLinear.lean`. Only the two F2 modules receive an independent
package verdict here. E1 is a dependency under separate audit, as explicitly directed in the handoff.

Read repository rules, PLAN, DECISIONS, the external package-audit brief, the handoff and its 21:15
ruling, N11 design row F2 and graph inventory, both N11 design audits, the Part-11 canonical-map
blueprint and iterative consumer, the N track statement, the partial-convex frozen anchor and relevant
frozen definitions. The controlling external signature file is
`/root/code/KAM-inp/.drafts/design/N11Signatures.lean`, SHA-256
`fe33b7d1689fdfb8ea66242b975d2b44002039fc4aa25378313afc4bd59a8aeb`.
The user's exact report destination overrides the audit template's main-worktree destination.
Only this report is a persistent auditor edit; probes are confined to `.lake/abi-scratch/` and removed.
No git state-changing command, production edit, generated-root edit or frozen/manifest edit was made.

## Declaration and node ledger

All short names below are in `KAM.Nekhoroshev`.

| Node / declaration | Lean location | Verdict | Reason |
|---|---|---|---|
| Shared signed flow definition `extFlow` | `Partial/ExtFlow.lean:27` | PASS | Entire definition, including body, equals the signed definition modulo whitespace; actual Part-5 flow, same weighted field, domain and time. |
| `bpN:p11:canonical-map`, full signed `canonical_map` | `Partial/CanonicalMap.lean:286` | PASS WITH NOTES | Exact amended signature, including binder order and hc; all signed clauses proved. Standalone iterative consumer gap below prevents consumer-complete acceptance. |
| Auxiliary `canonical_map_core` | `Partial/CanonicalMap.lean:179` | PASS | Distinct auxiliary name, explicitly excludes canonicity and proves every other signed clause without hc. It does not substitute for the signed graph-node theorem. |
| Canonical-map (a): both holomorphic maps and both images | `Partial/CanonicalMap.lean:228` | PASS | Positive- and negative-time `flow_b`; same intermediate U and loss domain. Audit-1 F2 inverse-image omission is repaired. |
| Canonical-map (a): angle, fast, slow displacement | `Partial/CanonicalMap.lean:236` | PASS | Component MVT along actual trajectories; bounds V/ρ, V/(eσ), b.c*V/ρ, with no changed constants. |
| Canonical-map (b): equivariance and reality | `Partial/CanonicalMap.lean:244`, `:278` | PASS | Integer translation invariance from differentiated periodicity and generic flow uniqueness; actual real-locus field transport and E1 flow_real. |
| Canonical-map (c): derivative estimate | `Partial/CanonicalMap.lean:273` | PASS | Generic flow_c on the full gauge interior; exact constant 2V/(ρσ). |
| Canonical-map (d): canonicity | `Partial/CanonicalMap.lean:326` | PASS | E1 symplectic instantiated at hc and restricted to U. No canonicity premise. |
| Canonical-map (e): inverse identities and smaller-domain image | `Partial/CanonicalMap.lean:263` | PASS | Both inverse identities from flow_c; explicit displacement argument places Φz back in U. |
| Consumer edge `canonical_map → iterative`, `stepN:p11:it-map` | external signatures `:367`; blueprint p11b `:136` | FAIL | Arbitrary PartialBlock in iterative, no positive block radii or hc. See F2-C1. |
| Frozen `partialConvex_nekhoroshev` | `KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean` | NOT A SEAL AUDIT | No F2 provider exists or is assigned. Anchor remains DRAFT_SORRY; package validation cannot seal it. |

The design inventory maps exactly one graph theorem to CanonicalMap: `bpN:p11:canonical-map`
(design line 209; source p11b lines 108–113). No separately assigned step node is omitted.
ExtFlow is the disclosed module split shared with F1, not a second implementation of the flow.
No further public F2 declarations exist. No duplicate public short name or root shadow was found for
`extFlow`, `canonical_map`, or `canonical_map_core` in KAM.

## F2-C1: positivity ruling is faithful, but does not cover every signed consumer

The ruling adds a legitimate source positivity premise, with no hidden analytic content.
The standing block paragraph at `blueprint-N/parts/p11b-partial-nf.tex:4–5` explicitly fixes a
“starting radius r_B>0” and a “physical slow width w>0”, then defines λ=w/r_B and c=2π/λ².
`PartialBlock.c = 2*Real.pi/(b.w/b.rB)^2` (`Setting.lean:79–80`); positive w and rB imply positive c
by elementary arithmetic. `ExtNFHyp.radius_pos` and `.slow_width_pos` (`Setting.lean:110–111`;
external signatures lines 347–348) supply precisely these facts for normal-form applications.
A fresh Lean probe checks this implication.

However, external signatures lines 367–379 state `iterative` for an arbitrary `PartialBlock`, with
positive *local losses* ρ,σ and bounds relative to R,s, not with positive b.w or b.rB. Its `slowLoss`
premise is merely `16*k*b.c*σ ≤ ρ`; when b.w=0, c=0 and this is automatic. The analytic, divisor,
perturbation and finite-family premises do not force a positive block width either: take k=1,
n=2, b.rB=1, b.w=0, b.S=∅, R=s=4, ρ=σ=1, K=0, α=1, p=2, δ=0, h=f=0,
Λ=univ and N=0. Holomorphy of h is automatic, the divisor set is empty, and every remaining
function-class/norm/family premise is vacuous or immediate. Neither positive R nor positive ρ forces
positive b.rB, which is a different parameter. A probe checks b.w=0 implies b.c=0 and that slowLoss
at c=0 permits positive losses.

The literal consumer proof says “Proposition canonical-map” at
`blueprint-N/parts/p11b-partial-nf.tex:136` (`stepN:p11:it-map`). Thus the handoff's claim that
“all consumers have it via ExtNFHyp.radius_pos, slow_width_pos” is too broad: that describes the
normal-form bundle, not the standalone iterative signature. The preceding design audits predate the
21:15 extra premise, so their PASS does not validate this amended edge.

Required owner/design resolution: either authorize corresponding source-scale positivity data in
`iterative` and propagate/check its callers, or provide the degenerate c=0 canonicity branch so that
iterative retains its current exact type. Do not silently add a premise to the signed consumer or
claim its proof is supplied by the current positive-c theorem. This finding does not establish
falsity of the c=0 canonical identity, and no frozen-statement defect is alleged.

## Definition classification and proof review

| New definition | Classification over whole carrier |
|---|---|
| Public `extFlow` | Literal signed wrapper around generic `KAM.Canonical.flow`; the inherited choice-of-solution / identity fallback is exactly the existing flow convention (`KAM/Canonical/Flow.lean:54`). F2 proves SmallField and appropriate gauge-interior membership before using flow theorems, so it never relies on the fallback as a trajectory. |
| Private `extGauge` (`CanonicalMap.lean:46`) | Genuine continuous linear equivalence diag(σ⁻¹,ρ⁻¹); positive losses ensure both units are invertible. Norm equality is proved, with the ordinary product max norm. |
| Private `fastCLM` (`:150`) | Literal real-linear projection to the fast-action coordinates, valid on the full carrier. |
| Private `slowCLM` (`:155`) | Literal real-linear projection to the ordered slow q,p pair, valid on the full carrier. |

No other new def/abbrev/structure occurs in F2. No global instance or norm is installed.
All twelve private lemmas/definitions have local visibility; no reused public helper is introduced.
The proof derives SmallField from vf and holomorphy, derives gauge-interior inclusions from the
polydisc geometry, and obtains the component bounds through Cauchy and MVT rather than assuming them.
Reality uses the actual real restriction on its open real domain. Empty base sets cause only the
usual vacuous domain assertions. Fixed b.c and b.lam never change with iterative R.
The signed contract uses an upper norm bound V; using actual norm ≤V is stronger than requiring
an equality. The blueprint's additional scaled displacement and SL-derived slow upper bound follow
from the generic flow estimate/component bounds and SL; the explicit signed export is the previously
audited narrowed interface. Required map, inverse, derivative, reality and slow-component consumers
receive its stated conclusions, subject to F2-C1.

## Independent verification

All Lean/Lake invocations below were serialized and used `LEAN_NUM_THREADS=1`; Lean execution
used `nice -n 5` (the build gate itself runs `nice -n 5 lake build`). No resource override was used.

1. **Targeted build**, exact command:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n11f2 KAM.Nekhoroshev.Partial.CanonicalMap
   ```

   Exit **0**. Gate output: `[inp-gate] slot 3 acquired 21:36:30 for KAM.Nekhoroshev.Partial.CanonicalMap`.
   Final output:

   ```text
   ✔ [3244/3244] Built KAM.Nekhoroshev.Partial.CanonicalMap (35s)
   Build completed successfully (3244 jobs).
   ```

   The dependency closure replayed upstream unused-variable/tactic/simp warnings in
   `Stability/Gradient.lean`, `Partial/Coordinates.lean`, and `Partial/RealSystem.lean`.
   No warning in the two F2 files and no sorry warning was reported for them.

2. **Fresh signed-type/body/positivity probe**, exact command:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11F2Audit.lean
   ```

   Exit **0**, no errors or warnings. The probe copied the external amended declaration under a
   fresh name and proved it by `exact canonical_map b hk hc hρ hρR hσ hσs hSL hV hsmall hφ hb`;
   it then checked `example : type_of% @audit_signed_canonical_map := @canonical_map`.
   It also checked literal flow-body equality by rfl, positive c from positive b.rB,b.w,
   zero c and failure of positive c when b.w=0, a zero-c slowLoss with positive losses,
   and the vacuous Λ=univ divisor premise. Mechanical source comparison additionally found
   equality modulo whitespace for the complete signed `canonical_map` type and entire `extFlow`
   definition, including its body. No signed declaration or frozen theorem was assumed as a draft.

   Complete axiom output for the new public theorems:

   ```text
   'KAM.Nekhoroshev.canonical_map' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.canonical_map_core' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. **Kernel replay**, exact command:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Partial.ExtFlow KAM.Nekhoroshev.Partial.CanonicalMap
   ```

   Exit **0**, complete output:

   ```text
   replaying KAM.Nekhoroshev.Partial.CanonicalMap
   replaying KAM.Nekhoroshev.Partial.ExtFlow
   ```

4. **Source lint**, exact command:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely the brief-permitted generated-root exception. Complete substantive output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (953 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No forbidden-token, resource-override, overlong-line or oversize-file finding occurred.
   The generated root was left untouched as required.

5. **Import, size and protected-path checks.** Recursive KAM import traversal found 89 modules,
   no provider, and exactly 23 frozen modules, all manifest-SEALED definitions; no frozen theorem
   or DRAFT_SORRY anchor is imported. Both F2 files have copyright/module/interface imports,
   module docstrings and exposed public noncomputable sections. `ExtFlow.lean`: 32 lines,
   maximum 98 characters; `CanonicalMap.lean`: 333 lines, maximum 100 characters.
   A forbidden-token/override/EuclideanSpace scan of both files emitted no match. The public
   declaration search found exactly one production definition of each F2 public name.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` was empty (apart from the
   disclosed merge-base warning). `git diff --check` passed. The report's own
   `git diff --no-index --check /dev/null /root/code/KAM-inp-n11f2/docs/tracks/N/audits/N11-F2-audit-1.md`
   passed. The temporary probe was deleted. Final status contains only this untracked report
   plus the pre-existing untracked handoff; tracked files are unchanged by the auditor.

## Errata, deviations and limits

No new pinned-publication erratum is claimed. F2-C1 is a live design/consumer defect, with exact
locations and quoted consumer text above. The authorized positive-c premise is a disclosed amendment,
not an undisclosed deviation. ExtFlow's extra module is a benign shared-definition split; F1 must
import it rather than redefine extFlow. The generated-root lint exception, if reported below, is
separate from substantive source hygiene. E1's source correspondence remains under its own audit;
its imported proof terms are included in axiom closure and kernel replay here.
