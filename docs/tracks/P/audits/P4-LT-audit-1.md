# Independent package audit 1: P4-LT

Verdict: **PASS WITH NOTES** for package P4-LT. All six declarations pass. The only hygiene exception is the brief-permitted stale generated root; the alternative tail proof is valid. No frozen anchor is sealed or certified seal-ready by this helper package.

Audited HEAD `2001d8f462d2abbb7941d62e44ed5d9d2c0a70b1` against `inp` (`f11c90357967f666b1673409df890dbcec823dff`) using `git diff inp...HEAD`. The complete committed change is the new 178-line `KAM/Planetary/PGMeasure/LatticeTail.lean`; no other production file is in scope. The pre-existing untracked handoff was read and left untouched. This report is deliberately in `/root/code/KAM-inp-p4lt`, as the user's explicit path overrides the generic brief's MAIN-worktree destination.

Read AGENTS.md, PLAN, DECISIONS, the package audit brief and handoff, P45 Revision 3 design (especially row P4-LT, node table and signatures), the three design audits under `/root/code/KAM-inp/docs/tracks/P/design/`, the current shared `.drafts/design/P45Signatures.lean`, P4:95–102, the relevant track-P statement conventions and the frozen P-G anchor for scope. Reviewed the actual upstream `KAM/Measure/Lattice.lean` proofs/interfaces. No web source is needed: the audited contract is the supplied repository blueprint/design and Lean package.

## Declaration review

All names below are in `KAM.Planetary`.

| Node / role | Declaration (module line) | Verdict | Reason |
|---|---|---|---|
| bpP:p4:lattice-tail / weight | `latticeWeight` (29) | PASS | Literal design formula on `Fin n → ℤ`; real l1 size and real exponent. |
| stepP:p4:lt-b / telescoping helper | `rpow_neg_succ_le` (32) | PASS | Bernoulli-based inequality for `q≥1`, `y>0`; distinct helper, no source theorem replaced by an assumption. |
| stepP:p4:lt-b / shell tail helper | `sum_Ioc_rpow_neg_le` (61) | PASS | Every finite interval `J<r≤M`, including `M≤J`; telescopes and discards a nonnegative endpoint. |
| stepP:p4:lt-b / finite lattice tail | `tail_finset_le` (88) | PASS | Any finite subset strictly beyond a real cutoff `m≥1`; exact stated constant, no extra main-theorem premise. |
| bpP:p4:lattice-tail; stepP:p4:lt-a, lt-b | `lattice_tail` (142) | PASS | Exact design telescope and conjunction: summability, full sum bound, every real cutoff tail bound; normalized signature identical. |
| bpP:p4:lattice-tail / constant | `latticeS` (174) | PASS | Literal design constant, no enlarged dependence or changed denominator. |

The full sum applies `KAM.Measure.lattice_sum` with exponent parameter `tau-1` (line 151), using exactly `tau>n`; ring identities preserve both exponents and the explicit constant. The blueprint's second sum `S₂` in dimension `b` is already the upstream `lattice_sum` at `(b,tau)`, as P4:100 says; the approved P4-LT signature does not require a separate new S₂ export.

For the tail, finite sets are partitioned by the integer l1 radius. `sum_sphere_le` (line 118) supplies the designed shell count through `card_l1Sphere_le` and `lattice_count`; no new counting hypothesis is assumed. Set `q=tau+1-n>1`, `J=floor(m)≥1`. The shell exponent is `-(q+1)`, telescoping bounds the sum by `J^(-q)/q`, and `J≥m/2` gives `(2/m)^q/q`. The finite-set proof covers nonintegral cutoffs and empty sets. The final subtype embedding preserves the strict tail predicate and the summand exactly. The finite-set bound and nonnegativity also imply genuine tail summability, so the `tsum` inequality does not exploit a nonsummable series' default value.

**Proof-plan deviation:** P4:101 uses convexity and an integral comparison; this implementation uses Bernoulli and telescoping. Its `q≥1` restriction follows from the existing `tau>n`, and the constant is unchanged. This is a valid implementation deviation, although the prover's handoff says “deviations: none”. It is not a blueprint/source defect.

## Definitions and applicability

The only new definitions are `latticeWeight` and `latticeS`; there are no new abbreviations, structures, instances or bundled specifications. Both are the intended literal formulas on their whole carriers, with Lean's ordinary total real-power/division conventions. `latticeWeight` at the zero mode has the standard real-power value, and `latticeS` has totalized division when `tau=n`; the theorem excludes the zero mode and assumes `tau>n`. No proof relies on an off-domain fallback.

This is infrastructure, not a provider or a frozen seal. There is no `KAM.Provider.*` export, no frozen anchor proved by this package and no seal body to test. The literal-design theorem probe replaces the inapplicable frozen-provider equality check. P-G and other frozen anchors receive **no seal-ready verdict** here; package acceptance does not establish P-G or root closure.

Production imports are exactly `Mathlib` and `KAM.Measure.Lattice`; the latter has no frozen/provider imports. There are no DRAFT_SORRY anchors or other providers in this dependency route, no extra premises in `lattice_tail`, and no conclusion-shaped assumptions. The helper's `hF` is ordinary finite-tail membership data, discharged internally when the main theorem is applied.

## Independent execution checks

All Lean/Lake commands below are serialized, with `LEAN_NUM_THREADS=1` and `nice -n 5`; the build uses the prescribed compile gate. No clean, update, cache download, root regeneration, protected-file edit or state-changing git command was run.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p4lt KAM.Planetary.PGMeasure.LatticeTail
```

Exit 0, output:

```text
[inp-gate] slot 1 acquired 08:29:58 for KAM.Planetary.PGMeasure.LatticeTail
Build completed successfully (9048 jobs).
```

The gate's script runs `nice -n 5 lake build`; no warnings were emitted. The job count is Lake's reported build summary, not a concurrency setting.

2. Design-type, definition-body and axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P4LTAudit.lean
```

Exit 0. The probe copied the literal current shared `lattice_tail` declaration under a fresh name, with body `by exact lattice_tail hn ht`, and checked `example : type_of% @lattice_tail := @audit_lattice_tail`. Both definition bodies were checked by `rfl` against the literal design formulas. Independent whitespace-normalized signature comparison for `latticeWeight`, `lattice_tail`, `latticeS` returned `True` for all three. Exact axiom output:

```text
'KAM.Planetary.latticeWeight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.rpow_neg_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.sum_Ioc_rpow_neg_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.tail_finset_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lattice_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.latticeS' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. One kernel replay invocation, package plus lattice dependency:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.PGMeasure.LatticeTail KAM.Measure.Lattice > .lake/abi-scratch/P4LT-leanchecker.log 2>&1
```

Exit 0; complete output:

```text
replaying KAM.Measure.Lattice
replaying KAM.Planetary.PGMeasure.LatticeTail
```

4. Full source lint (including its ABI subprocess, under inherited single-thread environment and niceness):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 solely for the explicitly allowed stale generated root. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (479 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No 100-character-line violations or other lint failures were reported. The generated root was left untouched as required.

5. Static and protected-path checks:

```sh
git diff --stat inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check
```

The stat reports one new file, 178 insertions. Protected-path diff: empty, exit 0. Whitespace check: empty, exit 0. An independent Python line-length scan reports 178 lines and maximum length 99. Searches for `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option`, `EuclideanSpace` in the audited file all return no matches. Copyright/license/authors, `module`, public imports, module docstring and exposed public section are present; no heartbeat, recursion-depth or synthesis override is used.

6. Final report/scope verification: `git status --short` contains only the pre-existing untracked handoff and this new report. The probe and replay log created for this audit were deleted from `.lake/abi-scratch/`. The report contains no pending checks.

## Suspected defects, uncertainty and scope

No suspected mathematical defect in the assigned blueprint or package was found. No pinned-source erratum is asserted from this local lattice audit. The valid proof-plan deviation is recorded above. Design-audit findings elsewhere in P45 are outside this package; the final design audit is a signature/design PASS, not evidence of those proofs' completion.

Only this report is a repository edit. The temporary probe is confined to `.lake/abi-scratch/` and is removed after validation.
