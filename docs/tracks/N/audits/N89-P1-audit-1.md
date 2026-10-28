# Independent N89-P1 package audit 1

Overall verdict: **PASS WITH NOTES**. The three-module infrastructure package meets its exact design contract. The sole hygiene exception is the explicitly permitted stale generated `KAM.lean`. No frozen anchor is proved or seal-ready by this package; provider/frozen-type and seal-body checks are therefore inapplicable. In particular this does not close N-HEAD-C, Part 8 covering, or the later Part 9 stability theorem.

## Scope and authority

Audited HEAD `181e07e8f4a07026e5dbb87963320645de4017ed` against local `inp` `46bfbcb5e40e5540583d781ad736c36bd2abd4ab` with `git diff inp...HEAD`. The complete diff adds only CoverParams (47 lines), Setting (55), and Elementary (159). The pre-existing untracked handoff is outside that committed diff. No S7-5 implementation was re-audited.

Read AGENTS.md, PLAN.md, DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the package handoff and AUDIT FOCUS, N89 design row/ownership/proof plan/Appendix A, both design audits (under `docs/tracks/N/design/`), the original signatures in `/root/code/KAM-inp/.drafts/design/N89Signatures.lean`, blueprint p8:184–201 and p9:25–53, and the track-N statement. Consulted the downstream frozen N-HEAD-C statement and the upstream definitions actually used. Original signature SHA-256: `01270a67c964001a1f6f86a2416ce572fee94f326c34cec43fcef7de0fea4b88`.

The user's exact report path overrides the generic brief's instruction to write in the main inp worktree. Only this report was authored; a temporary probe under this worktree's `.lake/abi-scratch/` was used and deleted. No production, frozen, manifest, generated, or source file was edited. No state-changing git command was run.

## Declaration and node assessment

Names below are in `KAM.Nekhoroshev`. All nine explicit public declarations match the original design signatures, including structure field order and the complete elementary conjunction. Comparison ignored comments/whitespace only. Private arithmetic helpers are implementation details, not replacement public contracts.

| Node / component | Declaration and production locator | Verdict | Reason |
|---|---|---|---|
| p8:covering, raw data only | `CoverParams`, Interfaces/CoverParams.lean:27 | PASS | Seven named real fields in exact order; phantom dimension preserved; no geometry/Hamiltonian dependency. |
| p8:covering, source premises only | `CoverParams.Valid`, Interfaces/CoverParams.lean:37 | PASS | Exactly n≥1, positive p,b,r0,M,m, K≥1 and A≥pM/(bm)+√2. No covering conclusion bundled. |
| p9:setting | `Theorem1Setting`, Poschel/Setting.lean:34 | PASS | Exactly the positive standing data and S1–S4; m≤M and strengthened radius bound are explicit source-route premises. |
| p9:setting | `setting`, Poschel/Setting.lean:53 | PASS | Literal alias of the setting, with unchanged binders. |
| p9:setting, constant A | `thmA`, Poschel/Elementary.lean:34 | PASS | Exactly 11M/m. |
| p9:setting, threshold | `thmEps0`, Poschel/Elementary.lean:36 | PASS | Exactly mr0²/(2¹⁰A^(2n)); dependence only on n,r0,m,M. |
| p9:setting, cutoff | `thmK`, Poschel/Elementary.lean:38 | PASS | Exactly (ε0/ε)^(1/(2n)), reusing `HeadParams.expo`. |
| p8/p9 covering specialization | `theoremCover`, Poschel/Elementary.lean:41 | PASS | Raw record with p=9/8, b=1/8, geometric K and correct M,m order. |
| p9:elementary; el-a, el-b, el-c | `elementary`, Poschel/Elementary.lean:105 | PASS | All blueprint clauses (a)–(c), plus proved Valid conjunct; exact design statement, no extra premise. |

The table covers only the raw interface portion of p8:covering. The covering theorem itself belongs to G7. Likewise p9:setting's guarded maxima belong to later packages. `m_le_M` and `local_real_regularity` belong to P2; their absence is not a P1 defect.

## Semantic and proof review

`CoverParams` is raw data on its entire carrier. `Valid` is an exact numerical predicate, independent of lattices, projections, maps, and eventual trajectories. `Theorem1Setting` is a source-premise bundle, with no conclusion-shaped field. Its complex Hessian bound is expressed in the explicit Euclidean size of directional derivative coordinates; no ambient max-norm operator bound was substituted. Holomorphy on the open tube supplies derivative regularity where needed. `RealOn` for angle-independent h agrees with real action reality since s>0 allows a real angle. `IsQuasiConvex` is the logically equivalent strict-disjunction formulation of the blueprint implication. `InClass`, `RealOn`, and `HasFiniteWNorm` retain the period-one, reality and actual summability guards of S4.

`setting` is an exact alias. `thmA`, `thmEps0`, `thmK` and `theoremCover` use ordinary total real arithmetic on all inputs. Zero denominators and n=0 have Lean's total arithmetic semantics outside the intended hypotheses; no theorem exploits these values. Under the setting and ε hypotheses, m,M,r0,A,ε0,K and √n are positive and n≥2. There is no choice-based fallback, surrogate norm, or new instance.

The arithmetic proof follows the blueprint: M/m≥1 gives A≥11 and 9M/m+√2≤A; the radius premise implies r0≤4ell/m. Positive ε and its threshold bound give K≥1. `K_pow` converts the real power to exponent 2n and cancels the nonzero dimension denominator. The reciprocal power identity uses a nonnegative base. The exact ε identity follows by expanding powers and division, with positive denominators available; the ε0 upper bound uses A^(2n)≥1. The three analytic-cutoff claims use √n≥1. Finally 9/8·M/(1/8·m)=9M/m proves the last Valid field. No orbit, frequency lower bound, block geometry, or stability conclusion enters this proof.

The import graph contains no G7 `ResonanceGeometry.Covering`, no provider, and no frozen theorem. All 27 transitively imported frozen definition modules have matching manifest entries in state SEALED. This independently checks the design audit's F2 fix. The production sqrt import uses `Mathlib.Analysis.Real.Sqrt`, resolving design audit 2's deprecated-import note N3.

## Independent checks

Commands ran from `/root/code/KAM-inp-n89p1`. Lean-related commands used `LEAN_NUM_THREADS=1` and `nice -n 5`; no heartbeat, recursion, or synthesis budget was changed. The compile gate internally applies `nice -n 5` to lake build. No clean, cache operation, or library-wide rebuild was requested.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n89p1 KAM.Nekhoroshev.Interfaces.CoverParams KAM.Nekhoroshev.Poschel.Setting KAM.Nekhoroshev.Poschel.Elementary
```

Exit 0. Output:

```text
[inp-gate] slot 2 acquired 07:18:44 for KAM.Nekhoroshev.Interfaces.CoverParams KAM.Nekhoroshev.Poschel.Setting KAM.Nekhoroshev.Poschel.Elementary
Build completed successfully (3218 jobs).
```

2. Exact statement / axioms probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N89P1Audit.lean
```

Exit 0. The probe copied the original design's complete `elementary` declaration type under `audit_elementary`, with body `by exact elementary S heps heps0`. This tests its actual binders and full conclusion independently of the implementation's statement spelling. Output:

```text
'KAM.Nekhoroshev.elementary' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.audit_elementary' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Nekhoroshev.theoremCover' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`elementary` is the only new explicit public theorem. No provider/frozen ABI probe is appropriate because P1 exports no provider and claims no frozen proof.

3. Kernel replay, one invocation:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Interfaces.CoverParams KAM.Nekhoroshev.Poschel.Setting KAM.Nekhoroshev.Poschel.Elementary
```

Exit 0. Exact output:

```text
replaying KAM.Nekhoroshev.Poschel.Elementary
replaying KAM.Nekhoroshev.Poschel.Setting
replaying KAM.Nekhoroshev.Interfaces.CoverParams
```

4. Repository lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely the permitted generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (442 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

All three modules have copyright, `module`, public interface imports, module docstring, and exposed public noncomputable section. File lengths are 47/55/159; maximum line lengths 100/98/96 respectively. No forbidden proof escape or option override occurs. `git diff --check` exits 0. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. The generated root was not regenerated.

## Notes, errata, and limits

No new suspected blueprint or pinned-source defect was found; no deviations were introduced. The existing disclosed radius strengthening is preserved: blueprint p9:146 quotes Pöschel's “r0≤4l/m” and explains why full-rank stability needs the stronger r0≤ell/(2M). P1 assumes precisely that corrected blueprint/design premise and proves the weaker inequality. It does not claim the two assumptions are equivalent. The inherited max-norm/Euclidean cutoff adaptation K_a=K/√n is also preserved, rather than presented as a source misprint. The original PDF was not independently re-audited in this arithmetic package audit.

There is no blocking uncertainty for N89-P1. Later geometry, local regularity, dynamical estimates, consumer instantiation, and frozen-root closure remain outside this audit's scope. Final report validation and temporary-probe removal are recorded below.

Final validation: `git diff --check` and `git diff --no-index --check /dev/null /root/code/KAM-inp-n89p1/docs/tracks/N/audits/N89-P1-audit-1.md` exit 0. The temporary probe is absent. `git status --short` lists only this new report and the pre-existing untracked N89-P1 handoff.
