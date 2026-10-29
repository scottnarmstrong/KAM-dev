# P14-SEAL independent audit 1

Anchor: `KAM.Planetary.planetaryExponentialSafety` (`planetary.d25.planetaryExponentialSafety.v1`).
Audit checkout: `/root/code/KAM-inp-p14-seal`, HEAD `77102dfddf4dae4c6650cbad8db9990c674c5193`;
assembly commit `4c9d3335`. Comparison: `git diff inp...HEAD`; merge base
`b09cc13973973e2b5848066267c34d14e744eaba`. The diff contains Stopped, Safety, the provider,
and the three handoffs (six paths). The provider extends an existing 15-line stub.

**Verdict: PASS WITH NOTES (seal-ready).** The notes concern the permitted generated-root
lint exception, harmless internal constant choices, and stale explanatory prose. No additional
mathematical premise remains in the assembled provider. The real anchor remains DRAFT_SORRY;
this report certifies its prospective seal, and does not change its manifest state.

The exact seal body independently elaborated in a scratch copy is:

```lean
by exact KAM.Provider.Planetary.planetaryExponentialSafety hn B hB
```

## Scope and statement fidelity

Read AGENTS.md, PLAN, DECISIONS, the package brief, P14-SEAL/E11/E12Q handoffs,
P14-LEAN-DESIGN (especially the binder/assembly table at line 439), the signed
`/root/code/KAM-inp/.drafts/design/P14Signatures.lean`, blueprint-P Part 14a,
P-EXP-SAFE in the track statement, the frozen anchor and its frozen definition closure,
and the sealed N-PARTIAL-CONVEX statement and relevant erosion/solution definitions.
The user's exact report destination overrides the generic brief's main-worktree destination.
All new Lean declarations in the full three-dot diff were reviewed, including E11.

The `stopped`, `expsafe`, and provider telescopes are **byte-identical** to the signed
ones, from `theorem <name>` through the statement before `:=` (signature lines 363–369,
547–572, 666–691). Independent Lean examples also checked the helper types against
propositions constructed from those signed telescopes: `hstop` is precisely signed stopped
universally quantified over B/hB, and `hexpsafe` precisely signed expsafe universally
quantified over B/hB. Binder names/indentation of the enclosing helper differ; the propositions
are definitionally identical. No additional premise appears.

The final applications are literally:

```lean
expsafe_of_stopped hn (stopped hn) B hB
planetaryExponentialSafety_of_expsafe hn (KAM.Planetary.expsafe hn) B hB
```

The separately named conditional helpers are the explicitly authorized parametric pattern.
They do not stand in for an unpaid source theorem: the two actual results discharge their
premises in the assembled exports. The frozen telescope fixes `{n}`, `hn`, `B`, `hB` before
`∃ muStar c C`; positive `mu < muStar` and every initial datum in the inner region follow.
No exceptional set, Diophantine restriction, or assumed drift/confinement is introduced.
The physical/Newton/uniqueness/geometric clauses and the all-planets axis estimate remain intact.

## Declaration review

Names in the table are in `KAM.Planetary` unless qualified `Provider.Planetary`.
Locators refer to this worktree. PASS denotes statement/proof fidelity for that row.

| Node / location | Declaration | Verdict | Reason |
|---|---|---|---|
| E11 domain support, Stopped:48 | `fastBox_eq_pi` | PASS | Literal product of open real intervals; all κ allowed. |
| E11 domain support, Stopped:53 | `isOpen_fastBox` | PASS | Openness of that product. |
| E11 domain support, Stopped:57 | `convex_fastBox` | PASS | Convexity, with no nonemptiness assumption. |
| E11 domain support, Stopped:61 | `isOpen_slowBall` | PASS | Strict quadratic sublevel, all A. |
| E11 domain support, Stopped:64 | `isOpen_workingCylinder` | PASS | Continuous fast/slow projections. |
| p14:index, Stopped:75 | `planetaryTimeExponent_eq_partial` | PASS | Same planet/fast-action count n. |
| p14:index, Stopped:79 | `planetaryDriftExponent_eq_partial` | PASS | Same exponent, algebraically identical. |
| st-thr, Stopped:85 | `planetaryDriftExponent_pos` | PASS | Stronger: every natural n. |
| st-core, Stopped:94 | `stopped_fast_erosion` | PASS | Closed max-norm ball controlled coordinatewise, ε≥0 and ε<κ. |
| st-core, Stopped:110 | `stopped_slow_erosion` | PASS | Cauchy–Schwarz over Fin n ⊕ Fin n; √(2n) max-norm conversion. |
| st-sol, Stopped:180 | `stopped_hamiltonian_neg` | PASS | Exact negative Hamiltonian identity for arbitrary h,P,ν. |
| st-sol, Stopped:192 | `stopped_isSolutionOn_forward` | PASS | Field equality and differentiability proved on open working cylinder. |
| st-sol, Stopped:215 | `stopped_isSolutionOn_reverse` | PASS | Genuine derivative of y(−s), negative Hamiltonian, reversed interval. |
| bpP:p14:stopped, Stopped:245 | `stopped` | PASS | Signed statement; N applied to h and −h, all source hypotheses discharged. |
| es-const, Safety:47 | `safety_timeExponent_pos` | PASS | Stronger: every natural n. |
| es-const, Safety:54 | `safety_driftExponent_pos` | PASS | Stronger: every natural n. |
| es-const, Safety:61 | `amdBox_exists_margin` | PASS | Positive finite minimum and AMD gap/n; fixed B before choices. |
| p14:elements / es-axis, Safety:87 | `keplerAxis_eq_action_div_sq` | PASS | Positive mass/action excludes the sqrt fallback; stronger local hypotheses suffice. |
| es-axis, Safety:98 | `keplerAxis_drift_le` | PASS | Factor difference of squares, actions in (0,u), correct 2u/m² factor. |
| es-const/par/stop/amd/axis/assemble, Safety:120 | `expsafe_of_stopped` | PASS | Exact signed conditional contract, source stopped hypothesis only. |
| bpP:p14:expsafe, Safety:231 | `expsafe` | PASS | Signed telescope; actual `stopped hn` discharges hstop. |
| Q, provider:35 | `Provider.Planetary.planetaryExponentialSafety_of_expsafe` | PASS | Exact frozen conclusion; separately named conditional helper. |
| Q, provider:90 | `Provider.Planetary.planetaryExponentialSafety` | PASS | Exact frozen type; actual `expsafe hn` discharges hexpsafe. |

In `stopped`, B0/ν0 precede μ,T,δ,z0. N uses n fast actions, k=n, G=`fastBox B κ`,
G′=`fastBox B (2κ)`, D=`slowBall n A`, and the collar, holomorphic/C²/reality/Hessian/
definiteness data from `h_data` and `keplerDataNeg_*`. Both thresholds are obtained before
fixing μ or a segment. Slow erosion is proved from outer-region membership on the tested
segment, through the queried time; it is not assumed on a whole target window. Forward
C=r and reverse C=−l are positive in their respective branches. The time-zero branch is
trivial. The physical action identities and coordinate ≤ max-norm inequality transfer the
N conclusion with exactly the signed time prefactor and half-drift.

In `expsafe_of_stopped`, ν=B0μ, δ=ν^b/2, and T=exp(B0^(−a)μ^(−a)). The proof verifies
T≤ν⁻¹exp(ν^(−a)), both action collars and the AMD collar, applies the existing `amd`,
and derives axis drift using positive inner/outer actions. These are proofs, not bundled inputs.

## Definition classification and quarantine

There are **no new def/abbrev/structure declarations** in the three changed Lean modules.
Local `set` witnesses (including εD, b, ν0, ν in Stopped and m0 in Safety) are ordinary explicit
quantities, with positivity proved before inverse/power manipulations. No junk fallback is used.
The frozen definitions remain unchanged: Phase has the required Fin-function carrier;
LowAMDRegion includes prograde ellipticity and the literal action/AMD inequalities;
StoppedActionBound quantifies over arbitrary tested segments; solution predicates retain
DifferentiableAt and two-sided HasDerivAt, including endpoints. The axis helper's positive
mass/action assumptions justify sqrt squaring, so totalized division/sqrt outside the physical
region cannot supply a false proof.

Recursive import inspection visited 278 KAM modules from the three audited modules. The only
imported frozen theorem is `KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev`, manifest
**SEALED**. No transitive DRAFT_SORRY import occurs. The only provider-import edge within that
closure is the permitted sealed N anchor importing its own N provider. The new P provider
imports Safety, which imports no provider. A repository-wide direct-import scan finds the
P provider imported only at frozen PlanetaryExponentialSafety:31. No non-provider module
imports the one remaining DRAFT_SORRY anchor. The generated-root exception in the handoff
is therefore not needed for an existing provider import in this checkout.

## Independent checks

Every audit build/probe/replay used LEAN_NUM_THREADS=1, and these operations were serialized.
All source edits are confined to this report; scratch work is under `.lake/abi-scratch/`.

1. Targeted gate (exit 0):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-seal KAM.Planetary.Exponential.Stopped KAM.Planetary.Exponential.Safety KAM.Provider.Planetary.PlanetaryExponentialSafety
```

The gate runs `nice -n 5 lake build` and printed:

```text
[inp-gate] slot 1 acquired 15:46:08 for KAM.Planetary.Exponential.Stopped KAM.Planetary.Exponential.Safety KAM.Provider.Planetary.PlanetaryExponentialSafety
Build completed successfully (9324 jobs).
```

There were replayed warnings in unchanged dependencies (unused variables/tactics and a
deprecated name); no failure or default-heartbeat design signal in the audited modules.

2. Exact-type / signed-type / all-public-axioms probe (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P14Probe.lean
```

The probe imports the real frozen anchor and provider, and includes exactly:

```lean
example : type_of% @KAM.Planetary.planetaryExponentialSafety :=
  @KAM.Provider.Planetary.planetaryExponentialSafety
```

It also proves fresh copies of the signed stopped/expsafe/provider statements using the actual
exports, and checks both helper contracts against the signed propositions. Exact axiom output:

```text
'KAM.Planetary.fastBox_eq_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_fastBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.convex_fastBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_slowBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.isOpen_workingCylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.planetaryTimeExponent_eq_partial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.planetaryDriftExponent_eq_partial' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.planetaryDriftExponent_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_fast_erosion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_slow_erosion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_hamiltonian_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_isSolutionOn_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_isSolutionOn_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.safety_timeExponent_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.safety_driftExponent_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.amdBox_exists_margin' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerAxis_eq_action_div_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.keplerAxis_drift_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.expsafe_of_stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.expsafe' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Planetary.planetaryExponentialSafety_of_expsafe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'KAM.Provider.Planetary.planetaryExponentialSafety' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Prospective seal (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P14Seal.lean
```

This is a copy of the entire frozen source, with only the declaration renamed to
`planetaryExponentialSafety_auditSeal` and `by sorry` replaced by the seal body above.
It retains the module/import/namespace setup and exact frozen telescope. Output:

```text
'KAM.Planetary.planetaryExponentialSafety_auditSeal' depends on axioms: [propext, Classical.choice, Quot.sound]
```

4. Kernel replay (one invocation, exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Provider.Planetary.PlanetaryExponentialSafety KAM.Planetary.Exponential.Stopped KAM.Planetary.Exponential.Safety
```

```text
replaying KAM.Planetary.Exponential.Safety
replaying KAM.Planetary.Exponential.Stopped
replaying KAM.Provider.Planetary.PlanetaryExponentialSafety
```

The tool's actual interface accepts module names with `--verbose`; `--help` is not a help
interface here (it attempted to find module Kam and exited 1). The required replay above
subsequently succeeded on all three modules.

5. Repository lint (exit 1, solely the explicitly permitted generated-root exception):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1338 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Frozen-anchor and ABI checks pass independently of the generated-root note. The generated
root was not regenerated, as required. Scratch probes and audit logs were removed after their
outputs were copied into this report.

6. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
`git diff --check inp...HEAD`: empty, exit 0. The three changed Lean files are respectively
377 / 261 / 120 lines (Stopped / Safety / provider), with maximum columns 98 / 96 / 98.
All have copyright, module, public imports, module docstring, and public section. Masked-code
scan found no sorry/admit/axiom/unsafe/opaque/native_decide/EuclideanSpace or set_option override.
The short name `stopped` also exists in the distinct Nekhoroshev averaging namespace; no
qualified-name collision occurs. The provider/frozen result sharing a short name is intentional.

## Notes, errata, and limits

- Safety:32–36 and blueprint-P/parts/p14a-amd-expsafe.tex:301–304: C uses the positive sum
  of upperᵢ/mᵢ² instead of the maximum. This only enlarges an existential constant and
  preserves its dependence on (n,B). The internal θ omits κ and εD: those collars are already
  enforced by stopped's ν0, so the final margins need only the action gaps and AMD gap/n.
  Neither change weakens the frozen statement.
- Provider:19–24 says “Until the signed ... is proved (it waits for stopped ...)” and
  “added once expsafe lands.” This is stale staging prose: both theorems are present and
  applied in the current source. No proof gap follows from that prose.
- No suspected mathematical defect in the compared blueprint/frozen statement was found;
  no new pinned-source erratum is asserted. This audit checks the package against its local
  signed/frozen/source-blueprint contract, without a new independent transcription of Nek77.
- No frozen file, manifest, generated file, or implementation source was edited. No commit
  or other state-changing git command was run. The orchestrator still performs actual sealing.

Final validation: the only worktree change is this report; `git diff --check` is clean.
