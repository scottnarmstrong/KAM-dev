# N12-17 independent package audit 1

Overall: **PASS WITH NOTES** for the scoped N12-17 implementation. The only new public theorem, `KAM.Nekhoroshev.averaging_most_core`, passes statement and proof review. This package is an implementation assembly, not a provider or a frozen-anchor seal; N12-18 still owns that assembly. No proof or statement repair is requested.

## Scope and comparison

Audited 2026-10-28 in `/root/code/KAM-inp-n1217` at HEAD `9a99daab12c6717ff8fd3e872a9c62577cb80c7f`. Read AGENTS.md, PLAN, DECISIONS, the common audit brief, the handoff's AUDIT FOCUS, the design row N12-17 and proof plan, both design audits, the authoritative signatures at `/root/code/KAM-inp/.drafts/design/N12Signatures.lean`, the track statement, Part 12 blueprint, and the relevant frozen anchor/definitions and dependency interfaces.

The explicit user destination overrides the common brief's main-worktree destination. Only this report is a repository edit. Temporary probes are confined to this worktree's `.lake/abi-scratch/` and removed at closeout. No delegation or state-changing git.

Comparison note: `git diff inp...HEAD` warns `multiple merge bases, using fdd44199ddea0cb6007c938ddf930ee3e6eefc24`. At inspection, `inp` was `722ad4a37de68b025a0c690051afff665dcb1176` and `inp-n1215` was `6a23b0c269645b924295c60ac91075648d058761`. Both three-dot comparisons include unrelated merged development. Thus the handoff's “No other file changed” holds for `git diff HEAD^ HEAD` (exactly Most.lean, 92 insertions), not for either complete branch comparison. The focus-file addition is identical in both requested comparisons. Unrelated modules were not audited.

`git diff inp...HEAD -- KAM/Frozen manifest README.md` is empty. The same comparison for `KAM.lean` is **not empty** (76 inherited additions), so the brief's whole-branch protected-path check is not literally satisfied. `git diff HEAD^ HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. This is a baseline/integration note rather than an N12-17 proof defect; no generated file was edited by this auditor.

Audited source SHA-256: `29e6ab694843b2905de9c1c1958339a09770e008d440d898f98db04fb286b30d`.

## Declaration and node ledger

| Node / obligation | Lean declaration | Verdict | Evidence |
|---|---|---|---|
| `bpN:p12:s-most#data` / N12-17 | `KAM.Nekhoroshev.averaging_most_core` | PASS | Most.lean:31–38 equals the authoritative signature text exactly, including implicit carrier parameters, telescope, quantifier order, constants, absolute volume, Hamiltonian and interval. |
| `stepN:p12:mo-E` | same theorem, :39–68 | PASS | Uses N12-15 `bad` to construct positive A before ε and η; `good` supplies measurable E; Markov is applied to a globally measurable majorant under volume restricted to K. |
| `stepN:p12:mo-z` | same theorem, :69–88 | PASS | Constructs an actual solution for every good initial point on all of the closed time interval; no supplied-flow or future-confinement premise. |
| N-AVERAGING-MOST frozen anchor | `KAM.Nekhoroshev.averaging_most` | PASS WITH NOTES | N12-17 supplies its core only. No provider export or seal is delivered here; direct provider/type and seal-body checks belong to N12-18 and are not claimed. |

There is exactly one new public declaration and no new public definitions or private helper theorems. The signature's fixed bounds ε≤1 and η≤R/8 implement the design's chosen existential thresholds; they do not replace a stronger promised signature. `AveragingData.hn` is 1≤n, allowing a stronger dimension range than the frozen 2≤n. All other bundled fields are the source positivity, analyticity, size-one perturbation and frequency-rank premises. No field assumes a stopped estimate, future existence or confinement. The design audits explicitly approved this core signature.

## Proof review

For the exceptional set, `E = K \ avgGood` is measurable by `good` and is contained in K. `bad` supplies M₂≥0, A₁>0, the stopped integral bound and η≤avgStopped on E, uniformly for the requested ε,η. The auxiliary `g = avgStoppedExt` is measurable. The proof transfers both threshold and integral from avgStopped to g only at points whose actions belong to B(R/2), using hKI and `avgStopped_eq_ext`. Therefore off-domain extensions are not used as trajectory estimates. Markov under `volume.restrict K` yields the absolute volume bound after using E⊆K. η>0 ensures its ENNReal image is nonzero and division agrees with `ofReal (A₁√ε/η)`. The finite integral bound precludes a vacuous infinite RHS at any fixed allowed ε,η.

For x∈K\E, set algebra gives x∈avgGood. Its omega guard is actual membership of (T,x) in the maximal flow domain. `avgMaximal_spec` gives the initial value and genuine solution; `mem_flowDomain_of_omega` uses the interval containing zero to put every t∈[0,T], including endpoints, in that open maximal interval. Restriction via `IsSolutionIn.mono` preserves genuine derivatives; `ham_reduction` supplies precisely the frozen `IsSolutionOn`, including visited action-domain membership and differentiability of the Hamiltonian. There is no endpoint derivative weakening.

The displacement function is continuous along the valid flow on the compact interval. Its image is bounded above, so `le_csSup` is legitimate. Membership of each t gives displacement≤sSup<η, hence the required ≤η. This does not exploit the arbitrary value of a real supremum of an unbounded set. ε>0 also makes [0,1/ε] nonempty. The unused local hT is harmless.

Constant dependence is exactly the design signature: A precedes ε and η, and may depend on the fixed data and K. The actual witness is the A₁ obtained from the existing stopped-bound API, whose stronger uniform-in-size-one-f contract is inherited. No extra premise, different norm or changed normalizer is introduced.

## Definition classification and quarantine

No `def`, `abbrev` or `structure` is introduced by Most.lean. Its proof-local g denotes the existing stopped majorant extension; E is the intended exceptional set; z is the actual maximal flow on the full claimed interval.

The relevant inherited objects were checked at their use sites: AvgPhase is the real Pi-product with its max norm; avgH unfolds to the frozen real Hamiltonian with εf; avgGood has both the full-time flow-domain guard and strict supremum guard. The fallback in avgMaximal is excluded by `avgMaximal_spec` at x∈avgDomain. Arbitrary flow values outside the maximal interval are never used to assert a solution. The action-ball indicator in avgStoppedExt is removed only under `avgStopped_eq_ext` with the verified inner-ball hypothesis.

A recursive local KAM import scan starting at Most found 90 modules, **zero provider import edges and zero frozen theorem import edges**. Direct imports are GoodSet and FlowRegular. Frozen definitions are allowed; there is no DRAFT_SORRY theorem contamination. The explicit axiom check below independently checks the new theorem's logical dependencies.

## Source/blueprint findings and limits

No new suspected source erratum, blueprint contradiction, frozen-statement defect or mathematical deviation was found. Blueprint `p12-averaging.tex:269` prescribes exactly E=K\Γη and Markov; :270 prescribes the maximal solution with genuine endpoint derivatives. Both are implemented. The slightly weaker final ≤η rather than <η is the literal approved signature and frozen target; the proof establishes the strict intermediate bound.

The track statement's illustrative smaller η₀ choices are explicitly proof choices, not frozen restrictions; the current design and blueprint select R/8. No new pinned-PDF audit is claimed. Earlier packages' proofs were inspected only where needed for interface meaning; this audit does not replace their independent audits or assert root/campaign closure.

## Independent checks

The following checks were independently rerun, with audit-owned Lean/lake executions serialized. No heartbeat, recursion-depth or synthesis-budget override was used.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n1217 KAM.Nekhoroshev.Averaging.Most
   [inp-gate] slot 2 acquired 12:08:32 for KAM.Nekhoroshev.Averaging.Most
   Build completed successfully (3248 jobs).
   ```

   Exit 0. The gate runs `nice -n 5 lake build`. Existing dependency warnings were replayed (unused variables/section variables, deprecated names and one style warning); no Most.lean warning or elaboration failure.

2. Full source lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (630 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Exit 1, solely the explicitly permitted stale generated-root exception. No generated file was regenerated. An initial lint invocation was stopped during its Python frozen-anchor guard and replaced by this complete invocation to ensure its later Lean ABI subprocess inherited the requested thread count and niceness. No audit Lean processes overlapped.

3. Mechanical checks: exact raw signature-text comparison returned `True`; scoped `git diff --check` passed; forbidden-token/option scan of Most.lean returned no matches. The file has 92 total lines and all required copyright, module, public-import, module-docstring and public-section components. There are no ambient EuclideanSpace types or budget overrides.

4. Signature and axioms probe, containing an `example` with the exact supplied signature and proof `averaging_most_core d K hK hKI`, plus `#print axioms averaging_most_core`:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N1217Audit.lean
   'KAM.Nekhoroshev.averaging_most_core' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   Exit 0; no warnings. This covers every new public theorem (one). No sorryAx or additional axiom.

5. Kernel replay, single invocation for the one scoped lemma module (no provider exists in this package):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Averaging.Most
   replaying KAM.Nekhoroshev.Averaging.Most
   ```

   **Exit 0.**

Closeout: the audit probe was deleted; the scoped source hash was rechecked unchanged. `git diff --check` and `git diff --no-index --check /dev/null /root/code/KAM-inp-n1217/docs/tracks/N/audits/N12-17-audit-1.md` pass. The pre-existing untracked handoff remains untouched, and this report is the sole new repository artifact from the audit. No uncertainties remain about the scoped statement, Markov step, measurable exception set or full-interval solution proof. The inherited branch-comparison/root note and the separate N12-18 sealing boundary remain as stated above.
