# N-CLOSE-LEAN independent audit 1

Audited 2026-10-29 in `/root/code/KAM-inp-ncloselean`, HEAD
`0199dcea016a4e773c91203a303df9245884d533`, against `inp`
`24adb6afac052a3bcb089cf72be220a93cd7b5db`, using `git diff inp...HEAD`.
The implementation commit is `e442187e`; HEAD adds the audit request.
The user's exact worktree report path overrides the generic brief's main-worktree destination.

**Overall verdict: FAIL for literal node closure; `bpN:p10:hypotheses-check`: not PROVED
under the requested complete-literal-statement gate.** The proved conjunction omits two
inclusions from source item (a). This is a narrow statement-completeness failure, not a
counterexample to the mathematics or a failure of Lean's proof checking. The wrapper
`head_theorem1_setting` passes. No frozen anchor or provider is added or changed; seal
readiness of existing anchors is outside this package's scope.

## Finding F1: item (a) omits the intermediate set inclusions

Authority: `blueprint-N/parts/p10-assembly.tex:62` and
`docs/graph/N/DEPGRAPH.md:13009` literally require
“U ⊂ B(0,5R/8) ⊂ B(0,R) ⊂ 𝓑_s(R)”.

`KAM/Nekhoroshev/Assembly/HypothesesFull.lean:37-39` instead quantifies only
`I` whose real inclusion belongs to `V`, and concludes membership in all three sets.
This states `U ⊆ B(0,5R/8)`, `U ⊆ B(0,R)`, and `U ⊆ 𝓑_s(R)`.
It does not state either

```lean
actionBall n (5 * p.R / 8) ⊆ actionBall n p.R
actionBall n p.R ⊆ realActionDomain n p.R p.s
```

The first missing claim quantifies over every point in `B(0,5R/8)`, and the
second over every point in `B(0,R)`; the existing antecedent restricts both to `U`.
Replacing the chain by three consequences on `U` omits source conclusions.
Both missing inclusions follow easily from `hp.hR` and `hp.hs`; their truth does
not make them components of the exported conjunction. An independent scratch
probe verifies those inclusions from standing premises alone (see checks below).
This is a package deviation from the literal contract, not a suspected source erratum.

Required repair: add the two inclusions to item (a) of the same exported proposition
and prove them from the existing standing parameters, then re-audit that statement.
No new premise, frozen change, or analytic work is needed. No repair was made by this auditor.

## Declaration and clause review

All declaration names below are in `KAM.Nekhoroshev`.

| Node / clause | Lean declaration or component | Verdict | Reason |
|---|---|---|---|
| `bpN:p10:hypotheses-check` | `hypotheses_check_full`, lines 31-85 | FAIL for literal closure | F1: two intermediate inclusions in (a) are absent. |
| (a), tubes | Same, lines 36-44 | FAIL for literal completeness | V inclusion, all U memberships, W inclusion, P nonempty, and half-ball inclusion pass; global intermediate inclusions are missing. |
| (b), h and Hessian | Same, lines 46-50 | PASS | Holomorphy and reality on V/U; complex Hessian bound uses explicit Euclidean norm on the source carrier. |
| (c), quasi-convexity | Same, lines 52-55 | PASS | Correct implication for every real direction, plus positive μ and μ ≤ Bc. |
| (d), radius | Same, line 57 | PASS | Literally `p.r0 ≤ p.ell / (2 * p.B)`. |
| (e), perturbation and setting | Same, lines 59-65 | PASS | InClass, RealOn, summable WBound, positive ε′ ≤ ε1, genuine setting, and all four constant identities. |
| (f), exceptional branch | Same, lines 72-73 | PASS | Strict μr0/8 < wmin and Euclidean frequency lower bound for every I0 in the open half-ball. |
| (g), Ω0 and time | Same, lines 67-70 | PASS | Uses the genuine setting's `omega0Ball.maximum`, positive wmin, both Ω0 bounds and the correct time prefactor. |
| (h), real Hamiltonian and field | Same, lines 75-85 | PASS | Reality and equality on W; taking Hlocal = realHamiltonian gives the requested field equality. Local-extension statement is stronger. |
| `stepN:p10:cf-setting` public exposure | `head_theorem1_setting`, Confinement lines 99-104 | PASS | Exact public wrapper of unchanged private `cf_setting`, with the same premises and conclusion. |

The wrapper is the only Confinement change: `git diff inp...HEAD` adds its docstring
and seven declaration/body lines at the former line 98. It does not alter the private
setting theorem, its proof, or its existing consumer.

## Premises, quantifiers, constants and definitions

`HeadParams` contains exactly R,s,M,m,Mc,wmin, with n indexed separately; `p.Pos`
is positivity of those six real data. `HeadHyp` is precisely the five integrable
source premises H1-H5; `hf`, `hε`, `hε0` supply H6-H7. These are not
conclusion-shaped assumptions. Constants are definitions in p, chosen before
h,f,ε; no wider dependence is introduced. The new declarations have no extra
analytic premise or orbit premise.

Moving (g) inside the existential setting, before conjunct (f), changes conjunction
presentation but not its mathematical quantifier scope. S is selected before every
I0, as required. Its proof-valued argument `hP : I0 ∈ P` is redundant on the open
half-ball by item (a), not an additional restriction: every such I0 supplies hP.
No weakened frequency domain was found.

There are **no new def/abbrev/structure declarations** in the audited diff.
Relevant existing objects were inspected to classify their use:

- `Theorem1Setting` (`Poschel/Setting.lean:34-49`) is the actual Part 9 Prop record:
  n ≥ 2, positive radii, 0 < m ≤ M, positive ell, holomorphy, reality, Euclidean
  complex Hessian bound, quasi-convexity, the radius condition, analytic real
  perturbation and finite weighted norm. It has no orbit or confinement field.
  The numerical ε′ bound is correctly supplied outside the record.
- P is the closed maximum-norm half-ball; V is its complex maximum-norm tube;
  U is the real preimage of V and W is univ × U. `Wdom` is the real domain
  univ × B(0,R+s), equal to the source Ws for positive R,s.
- `omega0Ball` (`Poschel/Frequency.lean:391-393`) fixes center I0 and Euclidean
  radius r0/thmA. `FrequencyBall.points` and `.maximum` (lines 270-275) are
  the Euclidean closed ball and supremum of the genuine Euclidean frequency norm.
  `omega0` (lines 395-409) supplies attainment and bounds on a compact nonempty
  ball inside the real tube. No unguarded supremum or junk fallback is used here.
- `WBound` includes the finite/summable weighted norm requirement. The proof
  does not infer a bound from a totalized real norm outside its finite locus.
- `realH` is the existing total real-part restriction. The blueprint Part 9
  definition (line 37) says “and 0 off W”; this existing extension convention
  differs globally from Lean's total real part. All new assertions concern W,
  and the locality statement handles equal local extensions, so this has no
  effect on this package's claims or F1. No off-W equality is asserted.

## Independent checks

All audit-launched Lean/Lake operations were serialized, with
`LEAN_NUM_THREADS=1` and `nice -n 5`. Lint was also serialized because its ABI
check launches Lean internally. No library rebuild, clean, cache download, or
repository source modification was performed.

1. Full diff inspected: two Lean files plus the handoff, 201 insertions.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`:
   empty output, exit 0. `git diff --check inp...HEAD`: empty output, exit 0.

2. Targeted build:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-ncloselean KAM.Nekhoroshev.Assembly.HypothesesFull
   ```

   Exit 0. Output begins with the acquired compile slot and ends:
   `Build completed successfully (3337 jobs).`
   Replayed unused-variable warnings occur in unchanged dependencies Period,
   Gradient, Maximal, Blocks, ODE.Exit, Transfer, Nonresonant and ResonantStabilityCore.
   No warning or heartbeat failure in either audited module.

3. Scratch probe `.lake/abi-scratch/NCloseAudit.lean` imports HypothesesFull,
   copies its entire declaration type as an `example`, and applies
   `hypotheses_check_full hn p hp hh hf hε hε0`. It also prints axioms of both
   new exports. Command:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/NCloseAudit.lean
   ```

   Exit 0; exact axiom output:

   ```text
   'KAM.Nekhoroshev.hypotheses_check_full' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Nekhoroshev.head_theorem1_setting' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   A second run additionally checks both F1 inclusions from `p.Pos` alone.
   No frozen/provider signature or seal-body probe is applicable: no such export
   or body is changed, and importing the existing headline anchor would pull an
   unrelated provider into this helper-only audit.

4. Kernel replay, one invocation:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Assembly.HypothesesFull KAM.Nekhoroshev.Assembly.Confinement
   ```

   Exit 0; exact output:

   ```text
   replaying KAM.Nekhoroshev.Assembly.Confinement
   replaying KAM.Nekhoroshev.Assembly.HypothesesFull
   ```

5. KAM/Mathlib short-name scan:

   ```sh
   python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-ncloselean KAM.Nekhoroshev.Assembly.HypothesesFull KAM.Nekhoroshev.Assembly.Confinement
   ```

   Exit 0: `short-name check OK (no reused public short name)`.
   Forbidden-token scan of both audited files: no sorry, admit, axiom, unsafe,
   opaque, native_decide, EuclideanSpace or resource overrides. Module headers,
   public import/section and documentation present. HypothesesFull: 141 lines,
   longest line 93 characters; Confinement: 178 lines, longest line 100 characters.
   Recursive inspection of 155 project modules reachable by their imports found
   no provider import and no frozen theorem import (hence no DRAFT_SORRY dependency).

6. Lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit 1 solely for the explicitly permitted stale generated root. Exact output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1343 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   Hygiene verdict: PASS WITH NOTES under the brief's explicit generated-root
   exception. The root was not regenerated.

## Limits and disposition

Only HypothesesFull and the Confinement diff received a package verdict. Existing
support definitions and source contracts were read to assess their meaning; no
re-audit of the six sealed N anchors is claimed. No suspected new pinned-source
mathematical defect was found. F1 is an omitted conclusion in this implementation.
The total-extension convention noted above is inherited and harmless on W.
No source, graph, frozen file, manifest, generated root, README, or git state was
changed. The only retained audit artifact is this report; audit scratch probes/logs
are removed after verification.
