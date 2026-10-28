# E3 independent package audit 1

Audit date: 2026-10-28. Scope: **only** `KAM/Planetary/Exponential/RealDomain.lean`, branch `inp-p14-e3`, HEAD `940c6b4edf1efae445ccc2df3e9a74b4869bf618`. Comparison: `git diff inp...HEAD`, with `inp` at `d9183adae208ecf2e726620694b69c8168e33006`. The committed delta is one new 175-line Lean file. The pre-existing untracked `E3-handoff.md` was read and left unchanged. This report is deliberately in the exact package-worktree path required by the user, overriding the generic brief's main-worktree output instruction.

## Verdict and scope

**Overall: PASS WITH NOTES.** Both `KAM.Planetary.real_domain` and `KAM.Planetary.original_cylinder_subset` pass source/signature fidelity, proof review, axiom checks and kernel replay. No blocking finding. Notes are the permitted stale generated root and the harmless unused signature premise. There is no frozen anchor assigned to E3; no anchor seal-readiness verdict is asserted.

E3 is an infrastructure package, with no provider and no frozen anchor to seal. Its results are `KAM.Planetary.real_domain` and `KAM.Planetary.original_cylinder_subset`. The downstream `KAM.Planetary.planetaryExponentialSafety` anchor is outside this package and remains `by sorry`; E3 verification does not close that theorem. Provider/frozen-type equality and a frozen seal-body probe are therefore inapplicable here. Instead, both complete authoritative helper signatures are independently elaborated under fresh names with bodies applying the corresponding proved export to `B hB hd`, and checked with `type_of%` examples.

Read: AGENTS.md, PLAN, DECISIONS, the package audit brief and E3 handoff; P14 design row E3, node rows 139–143, signature appendix 789–804, proof/reuse discussion and design audits 1–2; blueprint `p14a-amd-expsafe.tex` 160–192; graph packet `docs/graph/P/packets/P-p14a2.nodes.md` 90–242; P track statement's P-EXP-SAFE section; relevant frozen definitions and the downstream frozen anchor. Design audit 1 finding F3 (missing quantitative pair margin) is closed in the revised signatures and in this implementation.

## Declaration and node ledger

Line numbers below refer to `KAM/Planetary/Exponential/RealDomain.lean`.

| Node / declaration | Lean implementation | Verdict | Evidence |
|---|---|---|---|
| `bpP:p14:real-domain` | `KAM.Planetary.real_domain`, 122–162 | PASS | Exact signature; enlarged closed cylinder maps into chartSafe, with eccentricity < e and radial and all-distinct-pair distance ≥ d/2. Last source assertion is supplied by the separate required signature below. |
| `stepP:p14:rd-o` | private `rd_action_data`, 33–58; private `rd_mem_dom`, 60–70; `rd_body` 92–93 | PASS | Lower action window, positivity, and Γ_i < Λ_i(1−sqrt(1−e²)); nonnegative sqrt implies Γ_i < Λ_i and product chart membership. The packet's 3ℓ_i/4 lower bound follows directly from the actual `hd.small` and window; the k_i > sqrt inequality is implemented in equivalent multiplied form `hc` with Λ_i>0. These are internal steps by design, not omitted public contracts. |
| `stepP:p14:rd-ecc` | private `rd_body`, 73–120 | PASS | E1 gives prograde ellipticity, action/axis/cross identities. A1 gives exact eccentricity-square identity and inner/outer Kepler radial inequalities. Positive action and `hc` give `hc2`, then eccentricity² < e² and eccentricity < e. Squared action-window comparisons and e<1 give the full annulus bounds. |
| `stepP:p14:rd-sep` | `real_domain` local `hsep`, `hrad`, `hsep'`, 135–162 | PASS | Reverse triangle inequality, upper radius at i, lower radius at j and `hd.gaps` prove d/2 separation for i<j; symmetry covers i>j. `hd.radii` gives the solar margin. Admissibility gives d>0, hence both NoCollision clauses and chartSafe membership. |
| `stepP:p14:rd-last` | `KAM.Planetary.original_cylinder_subset`, 164–172 | PASS | Exact signature; κ>0 enlarges each closed action interval, and chartAMD≤outerAMD<A proves the slow bound. |
| private helper `rd_action_data` | 33–58 | PASS | No additional premise; nonnegative summands give Γ_i≤chartAMD≤A, then the supplied strict deficit and nonnegative multiplier give its conclusion. |
| private helper `rd_mem_dom` | 60–70 | PASS | Literal positive action and Γ_i<Λ_i conditions for every block; no fallback branch. |
| private helper `rd_body` | 73–120 | PASS | Literal physical eccentricity and radial bounds; no alternate carrier or hidden all-planet conclusion premise. |

All four step nodes mapped to E3 are accounted for. The chain through a_i(1±e_i) is present through A1's `hlow`/`hhigh`, E1's `hax`, and squared-window comparisons, even where `nlinarith` composes intermediate inequalities without separately naming them. The two public statements retain their complete conclusions; in particular, qualitative collision freedom has not replaced the quantitative pair margin.

## Definitions, premises, imports and names

**Definition classification:** no new `def`, `abbrev`, structure, instance, notation or coercion. The only declarations are the two public theorems and three private theorems listed above. Imported chartAMD is the sum of nonnegative quadratic slow actions; enlargedCylinder is the closed action/AMD cylinder with free angles; chartSafe is the product-chart domain intersected with the preimage of the literal collision-free domain. EnlargedData's fields are the geometric source inequalities E1–E3 plus their positivity/enlargement conditions. They contain no analytic, orbit, or collision-free conclusion assumed as a premise. Physical element formulas are used only after E1 supplies positive mass/radius, negative energy and positive cross product. The sqrt identity uses 0<e<1, so no zero-division or negative-radicand fallback is used to establish a geometric conclusion.

The fresh-source signature comparison reports `statement text EXACT MATCH` for both public declarations (entire text from `theorem` through the type, before `:=`). The implicit dimension and all binder orders agree, with no new n≥2 restriction, altered constant dependence or weakened conclusion. The unused `hB` in `original_cylinder_subset` is retained from the exact signature; its proof needs only κ>0 and outerAMD<A. This harmless redundancy is not an extra implementation premise.

A recursive local import scan finds 72 transitive KAM dependencies (excluding RealDomain), including 54 frozen modules, all under `Defs`. There are **no** provider imports or frozen theorem imports, direct or transitive, so no DRAFT_SORRY dependency and no sealed-theorem state exception to invoke. Ambient coordinates and planar vectors use `Fin → ℝ`; no EuclideanSpace, shadow instances, root namespace exports or public short-name collisions were found. A repository search for declarations of `real_domain` and `original_cylinder_subset` finds only this module, both under `KAM.Planetary`.

## Independent validation

Checks are run serially with `LEAN_NUM_THREADS=1` and `nice -n 5`; the targeted build uses the required compile gate. No dependency-cache repairs, generated-file edits, git mutations, or production edits were performed.

1. Targeted build (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e3 KAM.Planetary.Exponential.RealDomain
   ```

   Wrapper runs `nice -n 5 lake build KAM.Planetary.Exponential.RealDomain`. Gate output: `[inp-gate] slot 2 acquired 17:09:37 for KAM.Planetary.Exponential.RealDomain`. Final output: `Build completed successfully (9119 jobs).` E3 warning: `KAM/Planetary/Exponential/RealDomain.lean:164:49: Variable name hB is not explicitly referenced.` Existing supplier warnings replayed for unused variables in `KAM.Kepler.Energy`, `KAM.Planetary.Poincare.Chart`, and `KAM.Kepler.Mass`; no errors or heartbeat failures.

2. Signature and axiom probe (exit **0**):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/E3Audit.lean
   ```

   Fresh declarations copy the exact two signatures from `/root/code/KAM-inp/.drafts/design/P14Signatures.lean`, without importing its admitted declarations. Bodies are `by exact KAM.Planetary.real_domain B hB hd` and `by exact KAM.Planetary.original_cylinder_subset B hB hd`. Two `example : type_of% @audit_<name> := @KAM.Planetary.<name>` checks also elaborate. Complete output:

   ```text
   'KAM.Planetary.real_domain' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.original_cylinder_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay (exit **0**), one invocation covering the only new module (there is no provider module in E3):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Exponential.RealDomain > .lake/abi-scratch/E3-kernel.log 2>&1
   ```

   Complete output:

   ```text
   replaying KAM.Planetary.Exponential.RealDomain
   ```

4. Repository lint (exit **1**, solely the explicitly permitted generated-root exception):

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (804 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The root was not regenerated, as required by the audit brief and AGENTS.md. All other lint stages passed; no forbidden proof escapes/resource overrides, overlong Lean files or module failures were reported.

5. Diff and static hygiene:

   ```sh
   git diff --stat inp...HEAD
   git diff --check inp...HEAD
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   wc -l KAM/Planetary/Exponential/RealDomain.lean
   rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option' KAM/Planetary/Exponential/RealDomain.lean
   rg -n '(^| )(theorem|def|abbrev|structure) (real_domain|original_cylinder_subset)\b' KAM
   ```

   Stat: one new file, 175 insertions. Whitespace and protected-path diffs: empty (exit 0). Line count: 175. Forbidden-token/resource scan: no matches (rg exit 1). Name scan: only RealDomain lines 122 and 164 (exit 0). Copyright, module, public imports, docstring and public section are present. No production root shadow or duplicate public declaration found.

Production source SHA-256: `147e10234dbf3831f81713d6412c951fad35c5ba9971c5ff6dbbb6f67d92f811`.
Authoritative signature file SHA-256: `24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`.

## Uncertainties, errata and deviations

No suspected blueprint/source defect or implementation deviation was found in the E3 slice. This is a review against the pinned blueprint/design contracts and current suppliers, not a fresh source-PDF audit. Imported supplier proofs were not independently re-audited in full; their exact consumed statements, import closure, resulting public axioms and E3 kernel replay were checked. No heartbeat-budget failure or override occurred.

The graph packet still records `LEAN_STATUS: NOT_STARTED`; it was read as the contract and left unchanged under the report-only scope. E3 does not implement or certify later analytic enlargement, complex tube, stopped estimates, or P-EXP-SAFE assembly. The eventual frozen theorem remains outside this report's proof-closure claim.

Only this report persists from the audit. Audit scratch probe and kernel log were deleted after recording the results; no state-changing git or source edits were made. Final tracked diff is still precisely the original one-file E3 delta, and the pre-existing untracked handoff is unchanged.
