# E0 independent package audit 1

Date: 2026-10-28. Scope: **only** `KAM/Planetary/Exponential/Setting.lean`, package E0 of P14. Report destination follows the user's explicit worktree-path instruction, overriding the generic brief's main-worktree destination.

## Verdict

**PASS WITH NOTES.** Completeness, semantic/signature review, build, exact-definition probes, axioms and kernel replay pass. Lint exits 1 solely for the explicitly allowed generated-root staleness condition; all other lint gates pass. No blocking defect found. This is a definitions-only package: no provider export, theorem anchor, theorem seal, or campaign closure is certified. Provider/frozen theorem equality and seal-body probes are therefore inapplicable.

Snapshot: HEAD `785cf323fc4805b3e1c6c2fb4a5ed48f754ff9bd`; inspected comparison ref `inp` = `dca5e7e3ee3a8b0d8f0f2b53a377bf87ac1fc024`. `git diff inp...HEAD` contains precisely the new 73-line Setting module. Initial status contains the pre-existing untracked `docs/tracks/P/audits/E0-handoff.md`.

Read AGENTS.md, PLAN, DECISIONS, the prescribed audit brief and E0 handoff; track-P statement, additions/physical conventions; P14 design row E0, carrier table, relevant node rows and Appendix A; both P14 design audits, particularly their definition ledgers and audit-2 disposition. Applied the definition-body/carrier checks of the lean-statement-audit skill. The untracked signatures are read from `/root/code/KAM-inp/.drafts/design/P14Signatures.lean` because that file is absent from this worktree. Both design audits are under `docs/tracks/P/design/`, rather than `audits/`.

SHA-256 pins:

| Artifact | SHA-256 |
|---|---|
| Setting.lean | `a1f750f26afe47200f62a8a5b6826c027e6a9e6e2499bcd76d92142be08d4d56` |
| Original P14Signatures.lean | `cd28718f0ef82c8da477ff5be2985046d08d795614be4d36fd0b7e267de98dd7` |
| P14-LEAN-DESIGN.md | `a283ad509cb312a6c3ea06b6d94ce031903d7d05a5604d23553c17b9b7050ef7` |
| blueprint-P/parts/p14a-amd-expsafe.tex | `a2735bd6fbc36dc765bafccac43af4e3742b101a7e0f2d97725e70ac37ff8452` |

The design, signatures and blueprint pins agree with the revised design-audit-2 snapshot. All locators below refer to this worktree unless explicitly absolute. Blueprint `a` denotes `blueprint-P/parts/p14a-amd-expsafe.tex`.

## Completeness (additional orchestrator request)

**PASS: 8 required / 8 present; missing declarations: none; extra declarations: none.** Reviewed the entire 755-line original signature inventory (20 definitions/structures and 50 theorem signatures), not just the handoff's summary. The signature file is monolithic; the design's package ownership table and ownership rule determine its module split.

Design row E0 at line 373 assigns chartAMD, chartSafe, boxes, cylinders, EnlargedData and planetaryKeplerC to `Exponential/Setting`. Expanding those groups against signature lines 220–242 and 273–274 gives exactly `chartAMD`, `chartSafe`, `fastBox`, `slowBall`, `enlargedCylinder`, `workingCylinder`, `EnlargedData`, `planetaryKeplerC`. Every required name occurs exactly once in Setting, and the declaration/body comparison and elaboration probe cover every one. The eight structure fields, its constructor and its type are also present and axiom-checked.

The design's node table at line 189 separately names chartSafe/chartAMD for Setting. Its line 191 mentions planetaryKeplerC under the later Hamiltonian consumer; the explicit ownership rule at lines 402–403 assigns definitions to the earliest module, consistent with row E0. No extra theorem is assigned to E0: `enlarge` belongs to E2, `sec_domain_chart_facts` to E1, `real_domain` and `original_cylinder_subset` to E3, and `h_data` to E4. The adjacent later definitions `periodicOrbitSet` and `complexTube` belong to ComplexTube. The other signature definitions concern AMD or SecularBox modules. Frozen blocks are imported inputs, not missing E0 redefinitions. No completeness finding remains.

## Declaration ledger and definition classification

Every name below is in `KAM.Planetary`. A declaration-aware comparison removing comments and normalizing whitespace found **all eight declaration types and complete bodies identical** to both original signatures and Appendix A. This includes binder order, implicit dimension, explicit `slowBall` dimension, field order and inequalities. No alternate implementation or weaker carrier is substituted.

| Node / source object | Declaration and Setting lines | Verdict | Classification and semantic evidence |
|---|---|---|---|
| `bpP:p14:sec-domain#data`, a159–162 | `chartAMD`, 33–34 | PASS | Literal quadratic sum Γ=Σ(ξ²+η²)/2 on all chart phase points. Frozen `slow` extracts the second block from each coordinate vector; neither fast angles nor fast actions enter Γ. General n, with the ordinary empty sum for n=0. |
| `bpP:p14:sec-domain#data`, a159–162 | `chartSafe`, 37–38 | PASS | Literal set W=O_n∩Ψ⁻¹(W_phys), with κ=Gm₀=1. `poincareProdDom` requires Λ_i>0 and Γ_i<Λ_i; `collisionFreeDomain` unfolds to frozen `NoCollision`, including central and pair collisions. The intersection guards the product chart; no larger physical domain is silently accepted. |
| `bpP:p14:enlarge`, a170–178 | `fastBox`, 41–42 | PASS | Literal open product ∏(lower_i−κ,upper_i+κ). Strict endpoints; `fastBox B (2*κ)` is G'. It remains this interval predicate for arbitrary B,κ, including an empty interval; no fallback values. |
| `bpP:p14:enlarge`, a178 | `slowBall`, 45–46 | PASS | Literal strict quadratic sublevel D={Σ(ξ²+η²)/2<A}. For A>0 this is the Euclidean ball of radius √(2A), expressed using permitted Pi coordinates and an explicit sum, not the Pi norm. For A≤0 it is empty, as the literal sublevel requires. |
| `bpP:p14:real-domain`, a184–185 | `enlargedCylinder`, 49–51 | PASS | Literal closed action/AMD cylinder K: lower−2κ≤Λ≤upper+2κ and Γ≤A. Fast angles unrestricted. Closed versus open endpoints deliberately differ from G' and D. |
| `bpP:p14:sec-stopped#data`, a260–262; a178 | `workingCylinder`, 54–55 | PASS | Literal product of unrestricted fast angles, the open G action box, and D slow ball, in chart order ((λ,ξ),(Λ,η)). No restriction to the n=2 secular model. |
| `bpP:p14:enlarge`, a170–178, E1–E3 | `EnlargedData`, 58–67 | PASS | Literal Prop structure of eight geometric source premises. No analyticity, extension, collision-free theorem, existence of trajectories or stopped estimate is assumed as a field. See expanded field audit below. |
| `bpP:p14:ch-split`, a166; `bpP:p14:h-data`, a195–196; design `sec-stopped#data` | `planetaryKeplerC`, 70–71 | PASS | Literal complex rational sum −Σm_i³/(2I_i²), real masses cast to ℂ, κ=1. Source a196 explicitly defines it as **total**, with zero-coordinate values playing no role. There is no added if/default branch or choice. Positive-tube holomorphy is a later theorem, not a claim of this definition. |

For **each of the eight rows**: `BODY_MATCH: OK`; `PUBLIC_CARRIER: OK`; `WELL_DEFINEDNESS: N/A_LITERAL`; `CHARACTERIZATION: N/A_LITERAL`; `CHOICE_INDEPENDENCE: N/A`; `DEFINITION_VERDICT: PASS`. These are literal formulas/sets/premises, not objects defined through a unique characterization. No existence/uniqueness theorem is needed to introduce them. The inherited chart's physical properties and the identity between chartAMD and physicalAMD remain E1 obligations; E0 does not assert those properties.

`Phase d` is the frozen `(Fin d → ℝ) × (Fin d → ℝ)`. Directly relevant manifest identities are `planetary.Phase.v1`, `planetary.fast.v1`, `planetary.slow.v1`, `planetary.NoCollision.v1`, and `planetary.d25.AMDBox.v1`, all SEALED definitions. Read their complete bodies and the reused `poincareProd`, `poincareProdDom`, `planetBlock`, `poincareDom`, `poincareGamma`, `collisionFreeDomain` bodies. The frozen AMDBox fields match the design's m,ℓ,u,e*,A₁,d; no replacement box or alternate norm is introduced.

### Expanded EnlargedData premises

The parameters `{n : ℕ}`, `B : AMDBox n`, `kappa e A : ℝ` are typing/fixed geometric data, not claims that B is admissible. Later results separately supply admissibility; this literal predicate does not promise physical geometry for arbitrary inadmissible boxes.

| Field | Bin | Source / exact content |
|---|---|---|
| `kappa_pos` | SOURCE | a171: κ>0. |
| `ecc_lt` | SOURCE | a171: B.ecc<e, matching e₁∈(e*,1). |
| `ecc_one` | SOURCE | a171: e<1. |
| `amd_lt` | SOURCE | a171: A₁<A⁺. |
| `small` | SOURCE | a173 E1: κ≤ℓ_i/8 for all i. |
| `deficit` | SOURCE | a174 E2: A⁺<(ℓ_i−2κ)(1−√(1−e₁²)) for all i. |
| `radii` | SOURCE | a175 E3: d/2≤r_i⁻ for all i. |
| `gaps` | SOURCE | a175 E3: r_i⁺+d/2≤r_j⁻ for i<j, algebraically the displayed r_j⁻−r_i⁺≥d/2. |

Logical field counts: SOURCE=8, STANDING=0, RULED=0, EXCESS=0. No hidden typeclass or bundled conclusion is present. Source positivity of masses, e and A when needed follows from separately supplied admissibility and these inequalities; it has not been smuggled into a theorem here.

## Independent checks

All Lean-bearing commands are serialized, use `LEAN_NUM_THREADS=1`, and run at `nice -n 5` (the prescribed build wrapper applies nice internally). No clean, update, cache download, source repair, frozen edit, generated-root edit or state-changing git operation is performed.

### Targeted build

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-e0 KAM.Planetary.Exponential.Setting
```

Exit 0. After waiting for a shared slot, output included:

```text
[inp-gate] slot 2 acquired 15:05:18 for KAM.Planetary.Exponential.Setting
Build completed successfully (9110 jobs).
```

Replayed dependency warnings only: unused `hm,hκ` at Energy:106, Chart:212/247; unused `hκ` at Mass:147/157, `hw` at Mass:500, `hm,hκ` at Mass:524. No E0 warning or default-heartbeat failure. The job count is Lake's existing dependency graph, not a clean rebuild.

### Exact-definition and axiom probe

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/E0Audit.lean > .lake/abi-scratch/E0Audit.out 2>&1
```

Exit 0. The transient probe imports only Setting, reproduces each of the eight original signature declarations under `E0Audit`, checks each of the seven definition equalities at the full polymorphic function type with `rfl`, and checks the structure equivalence by passing its eight fields in both directions. This verifies elaborated equality of types/bodies, not just pretty-printed text. Axiom commands cover all eight exports and all constructor/field exports (no new public theorems exist). Exact output:

```text
'KAM.Planetary.chartAMD' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.chartSafe' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.fastBox' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.slowBall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.enlargedCylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.workingCylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.EnlargedData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.planetaryKeplerC' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.EnlargedData.mk' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.EnlargedData.kappa_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.EnlargedData.ecc_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.EnlargedData.ecc_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.EnlargedData.amd_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.EnlargedData.small' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.EnlargedData.deficit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.EnlargedData.radii' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.EnlargedData.gaps' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Thus the axiom sets contain only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or project axiom.

### Kernel replay and lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Exponential.Setting > .lake/abi-scratch/E0Kernel.out 2>&1
```

Exit **0**; complete output:

```text
replaying KAM.Planetary.Exponential.Setting
```

No provider module or lemma module exists in E0, so this single invocation covers the complete package module.

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh > .lake/abi-scratch/E0Lint.out 2>&1
```

Exit **1**; complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (766 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

Only the generated-root staleness line fails, exactly the brief's allowed exception. Generated KAM.lean was not edited or regenerated.

### Static scope and hygiene

- `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
- `git diff --check inp...HEAD` and `git diff --check`: empty, exit 0. The untracked report was also checked separately for trailing whitespace and balanced code fences.
- `wc -l KAM/Planetary/Exponential/Setting.lean`: `73 KAM/Planetary/Exponential/Setting.lean`.
- `rg -n '\b(sorry|admit|axiom|unsafe|opaque|EuclideanSpace)\b|set_option' KAM/Planetary/Exponential/Setting.lean`: no matches, exit 1, the expected absence result. Global lint likewise finds no prohibited construct or size violation.
- Copyright, `module`, public imports, module docstring, `@[expose] public noncomputable section` are present; module lint passes. Definition bodies are exposed through the section attribute.
- A recursive scan of all KAM source declarations finds no second declaration file for any of the eight E0 names. The exact-copy Lean probe also elaborates without any name collision.
- Recursive import review reaches 64 project modules, including 48 frozen modules; every reachable frozen manifest entry is SEALED. No provider module or frozen theorem module is reachable. There is no DRAFT_SORRY dependency.
- At closeout, the shared `inp` ref had advanced to `3444c636bc3b49d0d73986ef0898f7f976454760`; the merge base remains `9d4807385d1ed255c614837eca3e43f347b48dbc`. Repeating `git diff --stat inp...HEAD` still gives only Setting (73 insertions), and protected-path comparison is still empty. This ref movement does not change the audited package bytes.
- All four pinned artifact hashes above were recomputed and remain unchanged. Final worktree status consists only of this new report and the pre-existing untracked E0 handoff. Probe source and captured logs were removed after embedding their outputs here.



## Defects, limitations and deviations

No suspected E0 blueprint/source defect or implementation deviation found. In particular, source a196 says “total; the value at a zero coordinate plays no role”; this is affirmative source authority for the Kepler formula's full carrier. No new off-domain convention is invented in E0.

Design audit 1's F1–F5 concern other theorem/interface packages; design audit 2 resolves their contract changes and leaves these eight definitions unchanged. This report neither reopens those unrelated packages nor claims they are proved. P-EXP-SAFE, P-AMD-CONFINEMENT and all provider seals remain outside this E0 audit. No pinned-PDF re-audit or campaign theorem certification is claimed.

Only this report is a persistent auditor edit. The pre-existing handoff remains untouched. Temporary definition probes are confined to this worktree's `.lake/abi-scratch/` and removed after verification.
