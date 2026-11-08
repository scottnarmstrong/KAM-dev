# B4-TCHECKCHAIN independent audit 1

Overall verdict: **PASS WITH NOTES** for `checkTorusChain_sound` and the two smoke
results. No blocking statement, proof, computability, or hygiene defect found in the package.
There is no frozen anchor or provider here: this is ordinary Track B infrastructure,
not an authorization to seal an I/N/P anchor or to claim completion of all B4 applications.

## Scope and authority

Audited on 2026-11-03 in `/root/code/KAM-inp-b4tckchain`.
HEAD: `65e8bfa22fa62ead3ac93acef879b3a9dba63840`.
Comparison ref `inp`: `8c4ccc73102acb696ed39882984eb34cf037eebd`.
Merge base: `dfcfe1a17425f7c0a66cb73cb40715caa0d04e18`.
`git diff inp...HEAD` adds only the 182-line module
`KAM/EffectiveStability/TorusChainCheck.lean` and the 31-line handoff.
The module is unchanged between prover commit `0d9553dcf` and audited HEAD, including
merge `a8a48d91f`. Module SHA256:
`5245400e1e8105796b29eb2f83ca0c49759360bfd5b366d652d35e0897223839`.

Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, handoff/AUDIT FOCUS,
B4-TCHECKCHAIN and B1-common briefs, B SPEC/FREEZE-PROPOSAL/OWNER-DECISIONS,
packages.json and program-b-plan §3.2–3.3; compared the OscillatorChainCheck and
TorusCheck templates and the TorusChain/Basic/Smoke contracts and reused FT primitives.
The applicable node contract is the Track B brief (OD-B11/12); no blueprint-B or
Track B statement.md exists, and unrelated I/N/P anchors are not this package's target.
The user's exact report destination overrides the generic brief's main-worktree destination.
No production file was edited. No state-changing git command was run.

Provider/frozen type equality and seal-body probes are not applicable. In their place,
a scratch probe copied the conclusion of `torusChain_confinement` directly from its
source and specialized H, l, T, a, η to certificate data; `checkTorusChain_sound` elaborated
against that independent expected conclusion, retaining every clause and quantifier.

## Declaration review

All names below are in namespace `KAM.EffectiveStability`.

| Node / location in TorusChainCheck.lean | Declaration | Verdict | Reason |
|---|---|---|---|
| Data, 27 | `TorusChainCert` | PASS | H/Nact/P, finite step list, rationals and rational lists only; no proof fields. |
| Step Bool, 52 | `tchStepOKB` | PASS | Mirrors all 12 TChStepOK fields; two component bounds are checked for every i < n. |
| Step soundness, 60 | `tchStepOKB_sound` | PASS | Only Bool acceptance assumed; FTFits obtained by ftFits_of_check. |
| Chain Bool, 68 | `tchChainOKB` | PASS | Empty case Q = Nact + P by ftEqCheck; cons checks step, correct Lie identity, then recurses from s.out. |
| Chain soundness, 73 | `tchChainOKB_sound` | PASS | Structural induction, exactly TChChainOK; no assumed analytic identity. |
| Domain Bool, 82 | `tchDomOKB` | PASS | Both coordinate budgets, angle budget, and tail recursion match TChDomOK. |
| Domain soundness, 89 | `tchDomOKB_sound` | PASS | Order of real predicate fields is restored correctly; Rat casts preserve strict and weak inequalities. |
| Main Bool, 107 | `checkTorusChain` | PASS | Every target premise is checked or definitionally instantiated; total finite rational computation. |
| Main result, 117 | `checkTorusChain_sound` | PASS WITH NOTES | Exact target conclusion; only hc and initial chart-box hypothesis, besides data/typing binders. No frozen seal in scope. |
| Smoke data, 155 | `torusChainSmokeCert` | PASS | n=1, H=Nact=J₀²/2, P=0, exactly two zero-generator steps, T=1, η=0. |
| Smoke acceptance, 168 | `torusChainSmokeCert_check` | PASS | decide +kernel; independently reevaluated in scratch. |
| Smoke drift, 172 | `torusChainSmokeCert_zeroDrift` | PASS WITH NOTES | Applies main soundness and extracts its zero-drift clause; standalone corollary discards other solution clauses. |

Structure projections/constructor/recursors are generated data operations, not hidden
mathematical premises. No extra public handwritten declaration is omitted above.

## Premise and conclusion fidelity

`torusChain_confinement` at TorusChain.lean:46–78 is the comparison target.

| Target premise | Checker payment |
|---|---|
| hH, hP, hA | ftFitsCheck H/P and ftActOnly Nact. No FTFits Nact premise exists in target. |
| hok | tchChainOKB, including every step's fits_gen/fits_out and exact Lie/final identities. |
| hδc, hεb, hT | Rational δc > 0, εb > 0, T ≥ 0; exact casts. |
| a, b, η, r and hbl | Fin n coordinate functions read with getD i 0; bl=c.b; hbl is rfl. |
| hbr | b.getD i 0 ≤ r.getD i 0 for each i in range n. |
| hdom | tchDomOKB recursion at the same inner tail l. |
| hη | η.getD i 0 ≥ 0 at each coordinate. |
| hdrift | ftAngleDriftBound P i ftPiUB b + tchChainBound n steps H / δc ≤ η_i. |
| hmargin | a_i + T*η_i < b_i at each coordinate. |
| w₀, hw₀ | Explicit point binder and initial box hypothesis of main soundness. |

Step checks retain σ′>0, ρ′>0, σ′<σ, 0≤ε≤1/2, order≥1,
fits_gen/out, 2*ftPiUB*σ<1, the reciprocal lower bound on lam, and both derivative
majorants. Domain checks retain b+εb+tailJ+ρ′≤ρ, δc+tailA+σ′/2<σ,
r+δc+tailJ+ρ′/2<ρ and the recursive predicate. No inner displacement is omitted.
List.range n is converted to Fin n by i.2. Empty chains and n=0 have the same vacuous
cases as the target, not additional premises.

Rational division is total even for invalid data, but acceptance includes δc>0 and
step strip denominators positive. Rat.cast_le/lt with push_cast transports exactly
the rational drift/domain expressions, rather than changing their denominators.
Fixed ftPiUB matches the target; no extra π-bound premise is needed.

The conclusion preserves T₁>T, physical initial point tchChainMap steps w₀,
Hamiltonian solution on Ioo (-T₁) T₁, uniqueness for every order-connected interval
containing zero, chart-image recovery, and both action bounds for |t|≤T including
endpoints. No constants acquire additional dependence.

## Definition classification and smoke limits

All six new handwritten data definitions have their intended meaning on their whole
carrier: TorusChainCert is unconstrained finite data; tchStepOKB/tchChainOKB/tchDomOKB
are finite predicates; checkTorusChain combines them; torusChainSmokeCert is concrete
data. The recursive functions decrease on the step list. No choice, real evaluation,
ODE, inverse map, or analytic remainder is computed by a Bool definition.

The noncomputable section does not make these definitions noncomputable: an ordinary
`def auditComputable {n : Nat} (c : TorusChainCert n) : Bool := checkTorusChain c`
outside that section compiled successfully. The smoke acceptance and step count were
also independently proved by decide +kernel. Zero-generator smoke establishes the
requested two-step integration, not numerical performance or nonzero-normalization coverage.
The smoke drift proof actually calls checkTorusChain_sound; it does not construct an
unrelated constant function to satisfy the weaker corollary statement. Its initial
box is inhabited (zero actions, arbitrary lifted angles).

List padding is explicit intended semantics, shared with the theorem and FT library.
Missing entries are zero and surplus entries do not change Fin n coordinates; no
length equality is claimed or needed. Negative initial bounds can make hw₀ impossible,
but do not yield a false confinement conclusion.

## Verification

All Lean/Lake-bearing commands below were sequential and used this exact prefix:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

1. Targeted gated build (prefix above, then):

```sh
/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b4tckchain KAM.EffectiveStability.TorusChainCheck
```

Exit 0; output:

```text
[inp-gate] slot 1 acquired 03:24:13 for KAM.EffectiveStability.TorusChainCheck
Build completed successfully (3004 jobs).
```

This targeted build reused cached imports; no clean or whole-library rebuild was requested.

2. Scratch probe (prefix above, then):

```sh
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false .lake/abi-scratch/B4TCheckChainAudit.lean
```

Exit 0, no warnings. In addition to computability, direct-source conclusion matching,
acceptance and step count, it ran #print axioms for every new public theorem:

```text
'KAM.EffectiveStability.tchStepOKB_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchChainOKB_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.tchDomOKB_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.checkTorusChain_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChainSmokeCert_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.EffectiveStability.torusChainSmokeCert_zeroDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay, one invocation (prefix above, then):

```sh
lake env leanchecker --verbose KAM.EffectiveStability.TorusChainCheck
```

Exit 0; output: `replaying KAM.EffectiveStability.TorusChainCheck`.
The package has one changed lemma module and no provider module.

4. Full source lint (prefix above, then `sh scripts/lint_sources.sh`):

Exit 1, solely for the generated-root staleness explicitly permitted by the audit brief.
Complete output (collected from the same sequential, memory-capped invocation):

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)
check_lean_modules: PASS (4543 Lean files, 0 comparator configurations)
.........................
----------------------------------------------------------------------
Ran 25 tests in 3.844s

OK
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (314 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

Disposition: PASS with the permitted stale generated-root exception. No root was
regenerated or edited. The ABI receipt explicitly excludes a built replay of the two
KAMLunarBand declarations; this audit does not claim application validation.
Final verdict remains **PASS WITH NOTES**; no blocking finding.

5. Naming:

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b4tckchain KAM.EffectiveStability.TorusChainCheck
```

Exit 0; `short-name check OK (no reused public short name)`.

6. Source inspection/width scan: 182 lines; width violations `[]`; forbidden tokens `[]`.
Copyright, module, public imports, docstring, exposed public section present.
Correct Fin n product carriers, no heartbeat/depth overrides or native evaluation.
A recursive source import scan found 92 KAM modules in the closure, no provider imports,
no frozen theorem modules, and no DRAFT_SORRY anchor paths. There is no imported theorem
whose seal state needs an exception under D58.
`git diff --check inp...HEAD` exited 0 with no output.

7. Protected paths:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md lakefile.lean
```

Exit 0, empty output. Prover-to-HEAD module diff also empty.

## Notes, errata, deviations and uncertainty

- N1: TorusChainCheck.lean:48 describes r as “coordinate radii of the oscillator ball”.
  Here r is the torus action-polydisc/Cauchy coordinate radius. This inherited template
  wording does not alter any expression or proof; documentation correction is optional.
- N2: The smoke zeroDrift corollary intentionally projects away the solution and uniqueness
  clauses, but the main theorem and the independently checked full conclusion contain them.
  The smoke is integrable, with a=0, and is not a nonzero-generator physical application.
- The handoff's approximate 215-line count is stale; the audited file has 182 lines.
- No suspected pinned-source or blueprint mathematical defect found. No new proof premise,
  statement change, or production deviation introduced by this audit. OD-B12 explicitly
  leaves divisor solving on the untrusted producer side; its absence is not a checker gap.
- This audit checks the new wrapper against the existing chain contract, not a fresh
  source-level re-audit of every imported analytic proof. No frozen statement is modified.
  Measured standalone kernel time in the prover handoff was not independently benchmarked;
  acceptance and kernel replay were independently rechecked under the prescribed memory cap.

Only this report remains as an audit-owned repository change; the scratch probe was removed.
