# P23-01 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the scoped infrastructure module. Both public
lemmas pass statement, axiom and kernel checks. No mathematical or hygiene defect was
found in the submitted module. No frozen anchor is claimed or sealed by P23-01; hence
there is no per-anchor seal-ready verdict or provider/frozen-type obligation here.

Audited HEAD: `d3ac2209b7065ed2b8061c31646d0602b2893224`.
Comparison ref `inp`: `25c512a9ce353b8bac0852b616784748063a4cfb`;
merge base: `29dbfb0f19abb6c634f7ce97adf459363f8ba243`.
`git diff inp...HEAD` adds only `KAM/Planetary/Averaging/Setting.lean` (118 lines).
Scope follows the handoff's AUDIT FOCUS: only `Setting*`, not N6-1 or future P23 proofs.
The explicit user output path supersedes the generic brief's main-worktree destination.

Read AGENTS.md, PLAN, DECISIONS, the package audit brief, handoff, revision 2 design
(including Appendix A and proof/package boundaries), both design audits, the P track
statement, and the relevant P2 blueprint, frozen definitions and imported infrastructure.
Current frozen definitions and design govern over historical draft-status wording in the
track statement. This is an independent proof/package audit, not a fresh CP10 PDF audit.

## Declaration and node verdicts

All declarations below are in `KAM.Planetary`; line numbers refer to the submitted module.
A comparison of every command with revision 2 Appendix A, ignoring whitespace and
replacing only the two theorem bodies, gives **14/14 MATCH**. Binder order, structure
fields and definition bodies are unchanged.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| P2 conventions / carrier | `CPhase` (40) | PASS | Complex angle/action product; Pi max norms. |
| P2 conventions / carrier | `CHam` (41) | PASS | Total complex scalar Hamiltonian on that product. |
| `bpP:p2:conv#data` | `geometricWidth` (43) | PASS | Exact coefficient-to-geometric conversion `σ/(2π)`. |
| `bpP:p2:conv#data` | `realBase` (44) | PASS | Image under the existing real inclusion. |
| `bpP:p2:conv#data` | `coefficientDom` (46) | PASS | Existing weighted domain with converted width. |
| `bpP:p2:conv#data` | `realTube` (48) | PASS | Real preimage of the frozen complex action tube. |
| P2 block conventions | `firstBlock` (51) | PASS | First coordinates for any scalar carrier, including integers/complex numbers. |
| P2 block conventions | `lastBlock` (53) | PASS | Last coordinates using the frozen indexing convention. |
| `bpP:p2:conv#data` | `block_bridge` (56) | PASS | Both real restrictions definitionally equal frozen `fast`/`slow`; no premises. |
| `bpP:p2:conv#data` | `conv_data` (59) | PASS | Exact set equalities for arbitrary dimensions, sets and real radii; no positivity premise needed. |
| `bpP:p2:setting` | `setting` (73) | PASS WITH NOTES | Exact full-neighbourhood `DivisorBound` with threshold `α/q`; dependency note below. |
| `bpP:p2:setting`, inputs to `direct`/`split` | `DirectHyp` (78) | PASS | Positivity, holomorphy, direct divisor, class and finite norm bound only. |
| `bpP:p2:split`, `bpP:p2:a1` | `TwoDiv` (92) | PASS WITH NOTES | Every nonzero cutoff mode at every complex point; fast-zero modes use `α₂/q`, others `α₁/q`; dependency note below. |
| `bpP:p2:nfb`, A1/A2 | `AvgHyp` (98) | PASS | Geometric widths, `6 ≤ 2πKs`, ordered positive divisors, realness and `E ≤ α₂r/(128K)` preserved. |

These are the P23-01-owned adapters and inputs; this verdict does not assert all of
`conv#data`'s inherited estimates have been reproved here. `direct`, `split`, `nfb`, `avg`,
oscillator and P1 fixture declarations are outside this package.

## Definition classification and hypothesis review

- `CPhase`, `CHam`: carrier abbreviations, with frozen phase order (angle, action).
- `geometricWidth`, `realBase`, `coefficientDom`, `realTube`: literal numerical/set
  adapters to existing objects. Their bodies have the intended meaning on the entire
  carrier, including empty sets and nonpositive radii. No fallback or choice is used.
- `firstBlock`, `lastBlock`: total coordinate restrictions, valid also for empty blocks.
- `setting`, `TwoDiv`: raw source divisor predicates. They do not themselves impose
  positivity/holomorphy; the source bundles supply these. Division at `q=0` is Lean's
  total real division, but no scoped theorem exploits it: `DirectHyp` has `1 ≤ q` and
  `AvgHyp` uses `q=1`. Frequencies are the imported derivative, used under holomorphy.
- `DirectHyp`, `AvgHyp`: source-premise propositions, not output certificates. The
  divisor field is precisely the source nonresonance assumption, not an assumed solve.
  `InClass` supplies holomorphy and period one; `WBound` requires summability at each
  parameter point as well as a bound. Thus no junk `tsum` or sum-of-suprema substitution
  occurs. `E` and `δ` are upper bounds rather than assertions of attained exact norms,
  as explicitly designed; this supports empty bases and cutoff choices without choice.

`AvgHyp.real_h` expresses realness on real phase points of the positive-width product.
Since `sbar+s>0`, angle zero is available for every real action in the tube, so this
is the blueprint's realness of `h` on the real action slice. `sbar ≥ 0` matches P2 nfb
(the coefficient-width corollary is a later wrapper). No derived Lipschitz, generator,
flow, symplecticity, normal-form or remainder conclusion is assumed by either bundle.

`block_bridge` is two reflexivities. `conv_data` identifies the two existential tube
representations by set extensionality and then unfolds the domain and width adapters.
Both conclusions are exact equalities, stronger than any positive-radius specialization.
No constants acquire extra dependence and no frozen object is replaced.

## Integration note N1

The handoff says N6-1 is not on `inp`. That statement is now stale: current `inp`
contains `KAM/Nekhoroshev/NormalForm/Setting.lean`, introduced by `2fd6a16`.
The untracked file in this package worktree is byte-identical both to current `inp`
and to `inp-n61`. However it is absent from this package's HEAD and merge base.
Thus the successful local build uses an untracked upstream dependency; a checkout of
this package HEAD alone is not self-contained. Integrate onto current `inp` (or the
same landed N6-1 version) before release. No need to commit a duplicate N-owned file.
This is a disclosed integration precondition, not a mathematical failure of P23-01.
The wider N6-1 theorem proofs were not re-audited here.

## Independent hygiene and validation

All audit Lean invocations were serial with `LEAN_NUM_THREADS=1`, nice level 5,
and default heartbeat/recursion/synthesis budgets. No library cleanup, cache fetch,
package modification or frozen edit was performed.

1. Targeted build through the prescribed gate:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2301 KAM.Planetary.Averaging.Setting
   ```

   Exit **0**. Output:

   ```text
   [inp-gate] slot 1 acquired 06:17:50 for KAM.Planetary.Averaging.Setting
   Build completed successfully (9085 jobs).
   ```

   The gate runs `nice -n 5 lake build`; this is a targeted build using the existing
   build snapshot, not a clean rebuild. See N1 for the dependency provenance.

2. Probe `.lake/abi-scratch/P2301Audit.lean` imported only the submitted module,
   re-stated both exact public theorem signatures as `example`s with bodies
   `block_bridge v` and `conv_data D r σ`, and printed both axioms:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2301Audit.lean
   ```

   Exit **0**, output exactly:

   ```text
   'KAM.Planetary.block_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.conv_data' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   These are all new public theorems. Provider type equality and fresh frozen seal-body
   probes are **not applicable**: there is no provider or frozen theorem in the diff.

3. Kernel replay, one invocation for the only scoped module:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.Setting
   ```

   Exit **0**. Output: `replaying KAM.Planetary.Averaging.Setting`.

4. Full source lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely the expected generated-root warning. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (417 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No over-100-character line or other source-lint complaint was emitted. The
   orchestrator owns generated-root refresh; the auditor did not edit it.

5. Static review: 118 lines, longest line 92 Unicode characters; copyright, `module`,
   public imports, module docstring and exposed public section all present. No forbidden
   proof escape or resource override. The KAM import closure contains 39 modules and
   **no provider or frozen theorem module**; only frozen definitions are used, so no
   DRAFT_SORRY theorem enters through a transitive import. Consequently no manifest
   theorem-state exception is needed.

6. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty.
   `git diff --check`: exit **0**, no output. No state-changing git command used.

## Defects, uncertainties and audit changes

No suspected blueprint or pinned-source defect was found in this scoped module; no
source repair or mathematical deviation was introduced. The raw `setting` abbreviation
is deliberately just the divisor clause of the blueprint definition, while `DirectHyp`
supplies its standing assumptions, exactly as in the approved design. No proof closure
for P-G, P-PLANAR, P-FIXED or any I/N anchor follows from this package.

Only this report was written as a repository artifact. The temporary audit probe was
removed after checking. The pre-existing untracked N6-1 directory and handoff remain
untouched. The remaining release qualification is N1, the branch-base dependency.
