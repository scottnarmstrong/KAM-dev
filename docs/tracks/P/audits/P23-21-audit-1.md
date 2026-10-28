# P23-21 independent package audit 1

**Overall verdict: PASS WITH NOTES — private conditional package.** Both `bpP:p3:meas-actions` and `bpP:p3:meas-torus` pass the scoped statement, proof, constants and same-witness applicability review. No frozen anchor is proved or seal-ready by this verdict. P23-22 must retain the original construction and its displacement output.

## Scope and frozen inputs

Audit date: 2026-10-28. Frozen-v1 HEAD: `03cf7aea5c26c50e21b77c36d1e0c2d035d0e2a3`; comparison `inp`: `4edfdd76ba941faaf07d7c979c8cc92821074160`.

The requested `git diff inp...HEAD` was inspected. Git warns `multiple merge bases, using 003b1db80283ab9f885b58a8e415ba28053b37df`; the other merge base is `0e8f8536a2f3557ed967edeb55956f9cf182484c`. The comparison contains 15 files, including ten inherited LimitMap files. This audit covers ONLY the five new `KAM/Planetary/TwoScale/Measure*.lean` files (679 total lines), as specified by AUDIT FOCUS. Upstream modules were read only to identify consumed outputs and import status; their complete mathematical re-audit is outside scope.

Permission envelope: the user's explicit absolute destination overrides the common brief's main-worktree destination. Only this report and temporary worktree-local `.lake/abi-scratch/` probes may be written; no production repair, git mutation, source fetch, or delegation. Lean/Lake invocations are serialized within this audit, with `LEAN_NUM_THREADS=1` and niceness 5; the build uses the supplied gate.

Read AGENTS, PLAN, DECISIONS, the common package brief, the handoff, design row P23-21, N2 and the private release gate (design L285, L289–305), blueprint P3b L150–189, the track-P conventions, the P23-17 audit and live main-worktree P23-18 round-2 audit. The latter confirms the distinction between private interface release and final consumer closure. Inspected frozen Phase and ActionNbhd and the P-G anchor for boundaries; the P-G body remains `by sorry`. No provider/frozen equality or seal-body probe applies to this helper-only package.

Tier 2 focused audit using the manuscript-audit protocol: immutable snapshot, exhaustive declaration inventory, direct proof reading of all scoped files, adversarial attempts below, then separate verification. No external pinned PDF re-audit is claimed. Current repository evidence controls over the lightweight memory workflow guidance.

| Frozen-v1 file | SHA256 |
|---|---|
| `KAM/Planetary/TwoScale/Measure.lean` | `3f7e615a02c900e65c20c0ea90912f54bfc03f94179ea5d9bbf217ca8fcc7af7` |
| `KAM/Planetary/TwoScale/MeasureActions.lean` | `c7d8ae985d6b1bc2bd9a145407cecac8bee4596c115109d60ea0a2de4ab2a888` |
| `KAM/Planetary/TwoScale/MeasureJoint.lean` | `9a5bab906c94009c047fcd6108cd9947c533802187b4bdfea159724c353deece` |
| `KAM/Planetary/TwoScale/MeasureScaled.lean` | `e7d178e1185e5cd3e07caeb29ba3d960da347e0cfa3d046daf7639ef17470020` |
| `KAM/Planetary/TwoScale/MeasureTorus.lean` | `7164d731cd322a6ca5d911b065d711dc6208a9a7faf73a6f31885829f4d84e6a` |
| `blueprint-P/parts/p3b-two-scale-limit.tex` | `e923c1f3856cd7c27fc73b1a5bdb21139a31d0484e30421c4e0db9cfdff86c1a` |
| `docs/tracks/P/design/P23-LEAN-DESIGN.md` | `618497aa0c1d5114b76905ae2e3bc552c560a5d17f3136b505aec983bd2d5c6a` |
| `docs/tracks/P/audits/P23-21-handoff.md` | `d035fa9625b27f4607520c45967cdffcf4da1f46c0f89cf9a5f9ede62ca145e9` |
| `docs/tracks/P/statement.md` | `06d876320d40f7ae0cb5cdbe7e5b08a00b431125630079a2b3d3abcaac2e0b66` |

## Declaration and obligation ledger

All names are in `KAM.Planetary`. PASS below is scoped to the stated conditional/helper contract, not a frozen theorem promotion. There are 18 explicit public theorems and 3 definitions/structures; the facade has no new declaration.

| Node / obligation | Declaration (file:line) | Verdict | Reason |
|---|---|---|---|
| real tube membership | `mem_realTube_of` (Actions:30) | PASS | Literal real inclusion, max norm, strict radius |
| action input bundle | `ActionsMeas` (Actions:39) | PASS | Six produced fields; no measure assertion |
| ma-ext, ma-meas | `meas_actions_of_limit` (Actions:54) | PASS | Global extension, strict preimage tube, image bound and both complement estimates |
| mt-ext | `scaled_cover` (Scaled:31) | PASS | Transports extension and localized inverse bound through sc/unsc |
| scaling definition | `scaleEquiv` (Scaled:66) | PASS | Product scalar linear equivalence with positive R,s |
| rescaled norm | `norm_scaleEquiv` (Scaled:70) | PASS | Exactly max(2π‖angle‖/s, ‖action‖/R) |
| mt-meas | `lip_image_scaled` (Scaled:81) | PASS | Dimension 2n; nonzero finite determinant cancels |
| phase input bundle | `TorusMeas` (Torus:38) | PASS | Action bundle plus seven produced scalar/map fields |
| cell volume | `volume_box` (Torus:53) | PASS | Half-open Pi box, exponent n, no measurability premise |
| mt-split, mt-shell | `TorusMeas.volume_tube_diff` (Torus:66) | PASS | Outer measure bound (1+(4/3)^n)(a+b) |
| mt-shell | `TorusMeas.shell_subset` (Torus:94) | PASS | Existential closed shell, strict 22ÊR < 32ÊR |
| mt-pre | `TorusMeas.preimage_mem` (Torus:107) | PASS | Both coordinate bounds, enlarged half-open cell, shell exclusion |
| mt-sum | `TorusMeas.meas_torus_of_limit` (Torus:137) | PASS | Covers entire open tube cell; factor 2^n proved |
| numerical applicability | `KamHyp.kam_small_n` (Joint:35) | PASS | Derives 8192nÊ<1 directly from H.small and nonnegativity |
| normalized ratios | `KamHyp.mbar_div_le` (Joint:42) | PASS | H.positive and H.normalized, no new premise |
| action applicability | `actionsMeas_of_limit` (Joint:50) | PASS | Exact clause-shaped block/Lipschitz outputs discharge every field |
| phase applicability | `torusMeas_of_limit` (Joint:78) | PASS | Derived width/smallness and retained three block displacement bounds |
| torus union identity | `ko_eq` (Joint:116) | PASS | Both set inclusions from parameterization and onto inverse locus |
| inverse locus onto | `exists_omega` (Joint:131) | PASS | Uses ω=realFreq h I and the uniqueness clause |
| final measure clause | `meas_torus_final` (Joint:144) | PASS WITH NOTES | Exact design final clause; retains hsup from same construction |
| joint applicability | `meas_of_iterative` (Joint:175) | PASS WITH NOTES | One iterative_steps call, same i and Φinf; exported output forgets step packages |

The abbreviations Actions/Scaled/Torus/Joint mean the corresponding Measure*.lean file. Exact commands and variable contexts are preserved below.

## Expanded bundle and witness audit

These are explicitly conditional helper inputs under the design's authorized private interface contract. Produced estimates are not reclassified as source premises. Their producers are invoked inside the joint proof, whose only logical input is `H : KamHyp D sbar p h f`.

| Expanded field | Producer on the retained witnesses | Disposition |
|---|---|---|
| ActionsMeas.sub: D₀⊆D | `dioBase = D ∩ ...`, `inter_subset_left` | Definitional |
| ActionsMeas.E_nonneg | `H.eHat_nonneg` | Standing scalar consequence |
| ActionsMeas.pos: 0<ÊR | `eHat_pos H`, `H.R_pos` | Standing scalar consequence |
| ActionsMeas.bd: displacement ≤20ÊR | `limit_actions_of_steps S`, its two block bounds; `norm_le_of_blocks`, H.mbar_div_le | Produced, same i |
| ActionsMeas.lip: 2560nÊ | Same `limit_actions_of_steps S` tuple, hLip; h0 transport, Nat.cast_add | Produced, same i |
| ActionsMeas.small: 2560nÊ<1/3 | `H.kam_small_n` | Proved arithmetic |
| TorusMeas.acts | `actionsMeas_of_limit H ...` | All six fields above |
| TorusMeas.R_pos | H.R_pos | Standing scalar consequence |
| TorusMeas.s_pos | H.positive | Standing scalar consequence |
| TorusMeas.s_le: s≤1/4 | H.widths: 4s≤sbar<1 | Proved arithmetic |
| TorusMeas.E_le: Ê≤1/8 | H.eHat_lt_small | Stronger produced bound |
| TorusMeas.lip: 768nÊ | `P.limit_phi_real_of_steps hD`, hL | Produced, same Φinf, same i-image |
| TorusMeas.small: 768nÊ<1/10 | H.kam_small_n | Proved arithmetic |
| TorusMeas.sup: scaled displacement ≤3Ê/2 | Same `P.limit_phi_real_of_steps hD`, hsup; H.mbar_div_le and norm_le_of_blocks | Produced, same Φinf |

No bundle contains a measure inequality, cover/extension existence, image-volume bound, shell inclusion, surjectivity or preimage argument. Those hard steps are proved in the helpers, not bundled assumptions.

Actual shared tuple in Joint L196–214: `Ds, hs, fs, Ψ, Φ, is, h0, S, P := iterative_steps H`; `S : ActionSteps sbar p h Ds hs fs is`, `P : PsiSteps sbar p Ds hs fs Ψ Φ`. The single `limit_actions_of_steps S` produces `i, hconv, hbd, hloc, hLip`. For each j, `hD j` is proved by unpacking a point of `i '' Ds 0` and applying this exact hloc. Then `P.limit_phi_real_of_steps hD` produces `Φinf, hU, hL, hsup` on `univ ×ˢ (i '' Ds 0)`. Rewriting by h0 changes only Ds 0 to dioBase; no witness is reselected. hbd/hLip build hA; hL/hsup build hT; the two measure theorems are invoked on hA/hT. Every private obligation in the ledger has this path to its joint application.

Independent stronger composition probe: copied the Joint variable context and complete `meas_of_iterative` command, renamed it `audit_joint_retains_steps`, inserted `ActionSteps sbar p h Ds hs fs is ∧ PsiSteps sbar p Ds hs fs Ψ Φ ∧` immediately after the output equality `Ds 0 = dioBase D h p ∧`, and inserted `S, P` immediately after h0 in the final constructor. Its successful elaboration demonstrates that the same proof can retain both original recurrence packages alongside all measure conclusions. It calls iterative_steps exactly once.

## Proof, constants and adversarial checks

1. **Action preimage and open endpoint.** Actions L64–76 instantiate cover with λ=2560nÊ and η=20ÊR. From λ<1/3 and ÊR>0, η/(1−λ)<32ÊR (indeed ≤30ÊR). `F.symm y` is in the real tube and outside D₀, otherwise F|D₀=i would put y in i(D₀). L78–105 apply the full ambient Lipschitz bound, monotonicity and subadditivity. No compactness, closure or measurable-set assumption is introduced. Using the whole tube rather than naming a closed shell is a valid enlargement of the blueprint proof.

2. **Rescaling.** Scaled L31–61 use sc/unsc inverses with R,s positive and flatten dimension n+n for cover. The scaled inverse displacement is localized at y∈X exactly where cover provides it. Scaled L81–107 conjugate by the explicit product scalar linear equivalence e. `isUnit_det'` gives det≠0; `ofReal |det|` is nonzero and finite, permitting ENNReal multiplication cancellation even for infinite outer measure. No determinant factor or 2π is dropped.

3. **Closed shell and half-open cell.** Torus L94–103 explicitly use `{I | ∃ J ∈ i '' D₀, ‖I−J‖≤2ÊR}`. Triangle inequality with the 20ÊR action displacement gives ≤22ÊR<32ÊR. In L118–130, the norm bound gives coordinate angle displacement ≤Ês/π and action displacement ≤2ÊR. The upper cell endpoint stays strict because y.angle<1; its lower endpoint is non-strict, as required. If x.action∈Dstar, extension agreement contradicts y outside Φ(univ×Dstar). No unjustified nearest-point attainment occurs.

4. **Constants and final set.** λ′=768nÊ<1/10; ε=Ês/π≤1/96 follows from s≤1/4, Ê≤1/8 and π>3. L186–190 prove `((1+λ′)^2(1+2ε))^n≤2^n`. W=realTube D r\Dstar has measure ≤(1+(4/3)^n)(a+b). The direct split covers the *whole tube* by `(cell×W) ∪ Ψ(enlarged-cell×shell)`, giving `(1+2^n)(1+(4/3)^n)(a+b)`. This is even smaller than `complementConstant n = 1+(1+2^n)(1+(4/3)^n)`. L207–210 prove the final comparison; the constant is not assumed. Natural casts preserve n=a+b. No boundedness or finite-volume requirement is hidden.

5. **Union identification.** Joint L116–137 prove both directions of KO=Φ(univ×i(D₀)); unique source inverse data make I₀ onto D₀. L144–170 match exactly the design's final open-tube, unit-cell clause (design L1234–1236). Omitting hL here strengthens the helper, since no equality L=initialL is used for its local measure argument.

Adversarial pass: attempted to falsify the application by changing Dstar to an unrelated limit image, dropping hsup, admitting zero ÊR at the open boundary, losing a strict cell endpoint, and cancelling a zero/infinite scaling factor. The actual proof excludes these: hD is from the selected i, hsup is from the same Φinf tuple, positive ÊR and positive R,s are proved, the cell proof retains y<1, and the determinant is nonzero finite. No blocker survived these checks. These are direct counterexample searches and term-level checks by this independent auditor, not a claim of a second delegated audit.

## Definitions and release notes

| Definition | Classification | Body/carrier and well-definedness |
|---|---|---|
| ActionsMeas | Private conditional Prop bundle | Exactly six explicit proved-output fields, no choice or fallback; not a new source premise |
| TorusMeas | Private conditional Prop bundle | ActionsMeas plus seven explicit produced-output fields; no measure conclusion or new source premise |
| scaleEquiv | Literal linear equivalence | Product of nonzero scalar multiplications, angle factor 2π/s and action factor 1/R; valid on all Phase n for its positive parameter binders; no choice/default branch |

**N1 — retain derived data in P23-22.** `meas_torus_final` assumes `hsup` (Joint L156–159). It is a proved limit-map output, not a clause of the public two_scale_kam statement. This is permitted only for the distinct conditional helper, and meas_of_iterative actually supplies it. The future joint theorem must retain that output; it cannot use only the public block/Lipschitz clauses and silently add hsup as a source hypothesis. This audit approves the private applicability path, not the future consumer.

**N2 — existential corollary is not the whole joint construction.** The exported `meas_of_iterative` conclusion forgets S and P (hs, fs, Ψ are unused in its type's final proposition). Its body nevertheless uses one original tuple. The stronger scratch theorem demonstrates simultaneous retention without reselecting witnesses. P23-22 should invoke the conditional helpers within its retained iterative proof or export an appropriately complete joint tuple, rather than combine unrelated existential results. This is a downstream boundary, not a blocker for the package's stated contract.

**N3 — source wording and constants.** P3b L173 says “over D” and has coefficient `(1+2^n)(1+(4/3)^n)`, while design L1234–1236 asks for the whole realTube and `complementConstant`, with one extra unit. This implementation proves the stronger whole-tube bound already at the smaller coefficient before relaxing. No source premise or constant was silently weakened. The handoff's possible erratum about closed shells actually concerns P3b `mt-shell` L186, not `mt-ext` L180: L186 already writes `ρ₂+η≤22ÊR<r`, so its strict margin justifies containment in the open neighbourhood. The corresponding ma-ext margin is explicit at L167. **No suspected pinned-source defect established in this scope.** No production deviations introduced.

“Private” describes design status; these names are exported Lean declarations. Whole-library name compatibility is therefore part of the audit.

## Verification receipts

All commands below were run in `/root/code/KAM-inp-p2321`. No overlapping audit Lean/Lake invocation, clean, update, cache fetch, package edit or generated-file edit occurred.

Build command:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2321 KAM.Planetary.TwoScale.Measure
```

Exit **0**. Exact key output:

```text
[inp-gate] slot 1 acquired 14:46:48 for KAM.Planetary.TwoScale.Measure
Build completed successfully (9185 jobs).
```

The gate internally runs `nice -n 5 lake build`. This was a warm replay build, not a forced clean recompilation. Scoped warnings: Joint L176–177 unused hs/fs/Ψ. Replayed upstream unused-variable/deprecation warnings in Diophantine, StepNonres, Inverse, StepPerturb, Finite, LimitActions, LimitMap and Cover; no errors or sorry warnings.

Probe command:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2321Audit.lean
```

Exit **0**, no warnings/errors. Each of the 18 explicit public theorem names in the ledger was queried, plus `audit_joint_retains_steps`; every line has exactly this axiom list:

```text
[propext, Classical.choice, Quot.sound]
```

The probe is reproducible by importing `KAM.Planetary.TwoScale.Measure`, issuing `#print axioms KAM.Planetary.<name>` for each theorem above, and adding the stronger composition command with exactly the two output insertions described earlier. No project axiom or sorryAx occurs.

Static checks: Unicode-aware, comment/string-masked module/namespace declaration scan using `scripts/check_lean_modules.py` in memory (its ASCII identifier fragment extended to Unicode for this scan only): **721 KAM files; 21 exported package declarations; collisions []**. Each requested watch name volume_box, shell_subset, preimage_mem, scaled_cover, scaleEquiv, ko_eq, exists_omega has exactly one source declaration. All five scoped files have proper copyright/module/public imports/docstring/public section, definitions exposed by the section, no forbidden escape/resource override/EuclideanSpace; line counts 20,109,223,111,216, all below 1500.

Project import closure: **139 KAM modules**, no provider or frozen theorem imports. Its 12 frozen imports are manifest-state SEALED definitions: ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm, and planetary Fast, Phase, Slow.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check
```

Exit **0** each; protected-path diff is empty apart from the multiple-merge-base warning above. The initial worktree had only the pre-existing untracked handoff.

Kernel replay command (one invocation for all five modules):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.MeasureActions KAM.Planetary.TwoScale.MeasureScaled KAM.Planetary.TwoScale.MeasureTorus KAM.Planetary.TwoScale.MeasureJoint KAM.Planetary.TwoScale.Measure
```

Exit **0**, exact output:

```text
replaying KAM.Planetary.TwoScale.Measure
replaying KAM.Planetary.TwoScale.MeasureJoint
replaying KAM.Planetary.TwoScale.MeasureTorus
replaying KAM.Planetary.TwoScale.MeasureScaled
replaying KAM.Planetary.TwoScale.MeasureActions
```

## Exact private interface inventory

The following are the full declaration types and bundle fields at frozen-v1. Proof commands are the complete commands at the immutable source locations listed in the ledger; their kernel replay and same-witness composition were independently checked above. Types below omit proof bodies and are not alternative declarations or source statements.

All are under `namespace KAM.Planetary`, with `open Set MeasureTheory Real`; Joint additionally opens `Metric Filter Topology` and `KAM.Weighted KAM.Canonical KAM.NormalForm`. The Action/Torus contexts are:

```lean
variable {n : ℕ} {D D₀ : Set (Fin n → ℝ)}
  {i : (Fin n → ℝ) → (Fin n → ℝ)} {Φ : Phase n → Phase n} {Ehat Rhat s : ℝ}
```

The Joint context is:

```lean
variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}
```

Inside `namespace TorusMeas`, include `variable (T : TorusMeas D D₀ i Φ Ehat Rhat s)` and `include T`; the elaborated helpers therefore explicitly receive T. Scaled uses only `variable {n : ℕ}`. This inventory plus the obligation/producer tables covers every conditional assumption and every local measure obligation.

`MeasureActions.lean`: `ActionsMeas`

```lean
structure ActionsMeas {n : ℕ} (D D₀ : Set (Fin n → ℝ)) (i : (Fin n → ℝ) → (Fin n → ℝ))
    (Ehat Rhat : ℝ) : Prop where
  sub : D₀ ⊆ D
  E_nonneg : 0 ≤ Ehat
  pos : 0 < Ehat * Rhat
  bd : ∀ I ∈ D₀, ‖i I - I‖ ≤ 20 * Ehat * Rhat
  lip : ∀ I ∈ D₀, ∀ J ∈ D₀, ‖(i I - I) - (i J - J)‖ ≤ 2560 * (n : ℝ) * Ehat * ‖I - J‖
  small : 2560 * (n : ℝ) * Ehat < 1 / 3
```

`MeasureActions.lean`: `meas_actions_of_limit`

```lean
theorem meas_actions_of_limit (A : ActionsMeas D D₀ i Ehat Rhat) :
    volume (D₀ \ i '' D₀) ≤ ENNReal.ofReal ((4 / 3 : ℝ) ^ n) *
        (volume (D \ D₀) + volume (realTube D (32 * Ehat * Rhat) \ D)) ∧
      volume (D \ i '' D₀) ≤ volume (D \ D₀) + ENNReal.ofReal ((4 / 3 : ℝ) ^ n) *
        (volume (D \ D₀) + volume (realTube D (32 * Ehat * Rhat) \ D))
```

`MeasureTorus.lean`: `TorusMeas`

```lean
structure TorusMeas (D D₀ : Set (Fin n → ℝ)) (i : (Fin n → ℝ) → (Fin n → ℝ))
    (Φ : Phase n → Phase n) (Ehat Rhat s : ℝ) : Prop where
  acts : ActionsMeas D D₀ i Ehat Rhat
  R_pos : 0 < Rhat
  s_pos : 0 < s
  s_le : s ≤ 1 / 4
  E_le : Ehat ≤ 1 / 8
  lip : ∀ x ∈ (univ ×ˢ (i '' D₀) : Set (Phase n)), ∀ y ∈ (univ ×ˢ (i '' D₀) : Set (Phase n)),
    limitmap_data Rhat s ((Φ x - x) - (Φ y - y)) ≤
      768 * (n : ℝ) * Ehat * limitmap_data Rhat s (x - y)
  small : 768 * (n : ℝ) * Ehat < 1 / 10
  sup : ∀ x ∈ (univ ×ˢ (i '' D₀) : Set (Phase n)),
    limitmap_data Rhat s (Φ x - x) ≤ 3 / 2 * Ehat
```

`MeasureTorus.lean`: `TorusMeas.meas_torus_of_limit`

```lean
theorem meas_torus_of_limit :
    volume (((univ ×ˢ realTube D (32 * Ehat * Rhat) : Set (Phase n)) \
        Φ '' (univ ×ˢ (i '' D₀))) ∩ {z : Phase n | ∀ j, z.1 j ∈ Ico (0 : ℝ) 1}) ≤
      ENNReal.ofReal (complementConstant n) *
        (volume (D \ D₀) + volume (realTube D (32 * Ehat * Rhat) \ D))
```

`MeasureJoint.lean`: `KamHyp.kam_small_n`

```lean
theorem KamHyp.kam_small_n (H : KamHyp D sbar p h f) :
    8192 * ((a + b : ℕ) : ℝ) * eHat p < 1
```

`MeasureJoint.lean`: `KamHyp.mbar_div_le`

```lean
theorem KamHyp.mbar_div_le (H : KamHyp D sbar p h f) :
    p.Mbar₁ / p.Mbar ≤ 1 ∧ p.Mbar₂ / p.Mbar ≤ 1 ∧ p.Mhat / p.M ≤ 1
```

`MeasureJoint.lean`: `actionsMeas_of_limit`

```lean
theorem actionsMeas_of_limit (H : KamHyp D sbar p h f) {i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)}
    (hblk : ∀ I ∈ dioBase D h p,
      ‖firstBlock (b := b) (i I - I)‖ ≤ 20 * (p.Mbar₁ / p.Mbar) * eHat p * rhoHat p ∧
      ‖lastBlock (a := a) (i I - I)‖ ≤ 20 * (p.Mbar₂ / p.Mbar) * eHat p * rhoHat p)
    (hlip : ∀ I ∈ dioBase D h p, ∀ J ∈ dioBase D h p,
      ‖(i I - I) - (i J - J)‖ ≤ 2560 * (a + b) * eHat p * ‖I - J‖) :
    ActionsMeas D (dioBase D h p) i (eHat p) (rhoHat p)
```

`MeasureJoint.lean`: `torusMeas_of_limit`

```lean
theorem torusMeas_of_limit (H : KamHyp D sbar p h f)
    {i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)} {Φ : Phase (a + b) → Phase (a + b)}
    (hacts : ActionsMeas D (dioBase D h p) i (eHat p) (rhoHat p))
    (hlip : ∀ x ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
      ∀ y ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
      limitmap_data (rhoHat p) p.s ((Φ x - x) - (Φ y - y)) ≤
        768 * (a + b) * eHat p * limitmap_data (rhoHat p) p.s (x - y))
    (hsup : ∀ x ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
      ‖firstBlock (b := b) ((Φ x - x).2)‖ ≤ 3 / 2 * (p.Mhat / p.M) * eHat p * rhoHat p ∧
      ‖lastBlock (a := a) ((Φ x - x).2)‖ ≤ 3 / 2 * eHat p * rhoHat p ∧
      2 * π * ‖(Φ x - x).1‖ ≤ 3 / 2 * eHat p * p.s) :
    TorusMeas D (dioBase D h p) i Φ (eHat p) (rhoHat p) p.s
```

`MeasureJoint.lean`: `meas_torus_final`

```lean
theorem meas_torus_final (H : KamHyp D sbar p h f)
    {i I₀ : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)} {Φ : Phase (a + b) → Phase (a + b)}
    {K : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ) → Phase (a + b)}
    (hblk : ∀ I ∈ dioBase D h p,
      ‖firstBlock (b := b) (i I - I)‖ ≤ 20 * (p.Mbar₁ / p.Mbar) * eHat p * rhoHat p ∧
      ‖lastBlock (a := a) (i I - I)‖ ≤ 20 * (p.Mbar₂ / p.Mbar) * eHat p * rhoHat p)
    (hlipI : ∀ I ∈ dioBase D h p, ∀ J ∈ dioBase D h p,
      ‖(i I - I) - (i J - J)‖ ≤ 2560 * (a + b) * eHat p * ‖I - J‖)
    (hlipΦ : ∀ x ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
      ∀ y ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
      limitmap_data (rhoHat p) p.s ((Φ x - x) - (Φ y - y)) ≤
        768 * (a + b) * eHat p * limitmap_data (rhoHat p) p.s (x - y))
    (hsup : ∀ x ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
      ‖firstBlock (b := b) ((Φ x - x).2)‖ ≤ 3 / 2 * (p.Mhat / p.M) * eHat p * rhoHat p ∧
      ‖lastBlock (a := a) ((Φ x - x).2)‖ ≤ 3 / 2 * eHat p * rhoHat p ∧
      2 * π * ‖(Φ x - x).1‖ ≤ 3 / 2 * eHat p * p.s)
    (hI₀ : ∀ ω ∈ omegaSet D h p, I₀ ω ∈ dioBase D h p ∧ realFreq h (I₀ ω) = ω ∧
      ∀ I ∈ dioBase D h p, realFreq h I = ω → I = I₀ ω)
    (hK : ∀ ω ∈ omegaSet D h p, ∀ θ, K ω θ = Φ (θ, i (I₀ ω))) :
    volume (((univ ×ˢ realTube D (32 * eHat p * rhoHat p) : Set (Phase (a + b))) \
        ⋃ ω ∈ omegaSet D h p, range (K ω)) ∩ {z : Phase (a + b) | ∀ j, z.1 j ∈ Ico (0 : ℝ) 1}) ≤
      ENNReal.ofReal (complementConstant (a + b)) *
        (volume (D \ dioBase D h p) + volume (realTube D (32 * eHat p * rhoHat p) \ D))
```

`MeasureJoint.lean`: `meas_of_iterative`

```lean
theorem meas_of_iterative (H : KamHyp D sbar p h f) :
    ∃ (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
      (fs : ℕ → CHam (a + b)) (Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b))
      (is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)),
      Ds 0 = dioBase D h p ∧
      ∃ i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ),
        TendstoUniformlyOn (actionChain is) i atTop (Ds 0) ∧
        ∃ Φinf : Phase (a + b) → Phase (a + b),
          TendstoUniformlyOn (fun j => psiR (Φ j)) Φinf atTop (univ ×ˢ (i '' Ds 0)) ∧
          ActionsMeas D (dioBase D h p) i (eHat p) (rhoHat p) ∧
          TorusMeas D (dioBase D h p) i Φinf (eHat p) (rhoHat p) p.s ∧
          volume (D \ i '' dioBase D h p) ≤ volume (D \ dioBase D h p) +
            ENNReal.ofReal ((4 / 3 : ℝ) ^ (a + b)) *
              (volume (D \ dioBase D h p) +
                volume (realTube D (32 * eHat p * rhoHat p) \ D)) ∧
          volume (((univ ×ˢ realTube D (32 * eHat p * rhoHat p) : Set (Phase (a + b))) \
              Φinf '' (univ ×ˢ (i '' dioBase D h p))) ∩
              {z : Phase (a + b) | ∀ j, z.1 j ∈ Ico (0 : ℝ) 1}) ≤
            ENNReal.ofReal (complementConstant (a + b)) *
              (volume (D \ dioBase D h p) +
                volume (realTube D (32 * eHat p * rhoHat p) \ D))
```

Exact axiom output from the successful probe:

```text
'KAM.Planetary.mem_realTube_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.meas_actions_of_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.KamHyp.kam_small_n' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.KamHyp.mbar_div_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.actionsMeas_of_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.torusMeas_of_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.ko_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.exists_omega' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.meas_torus_final' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.meas_of_iterative' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.scaled_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.norm_scaleEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.lip_image_scaled' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.volume_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.TorusMeas.volume_tube_diff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.TorusMeas.shell_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.TorusMeas.preimage_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.TorusMeas.meas_torus_of_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'audit_joint_retains_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Lint and closeout

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, exact combined output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (723 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The only lint failure is the generated-root exception explicitly allowed by the brief. KAM.lean was not regenerated or edited. ABI verification ran after the axiom probe and kernel replay, with no other audit Lean/Lake job in flight. The handoff's earlier file count was 722; this independent current receipt is 723.

Final validation: snapshot HEAD and all five source hashes were rechecked unchanged; the report inventory contains exactly 21 declaration rows, 18 theorem queries plus the stronger composition query, balanced code fences and no trailing whitespace. `git diff --check` exits 0. `git diff --no-index --check /dev/null <absolute-report-path>` emits no whitespace diagnostics (exit 1 for the new-file comparison). The audit-owned P2321Audit.lean probe was deleted. Final `git status --short` contains only this report and the pre-existing handoff. No tracked file was edited.

Closeout: all scoped declarations and definitions classified; all ma/mt obligations mapped to actual helpers and same-witness applications; permitted axiom closure and kernel replay pass; targeted build passes; lint passes apart from its authorized generated-root exception; no scoped blocker or established erratum remains. Uncertainties are the explicitly unaudited upstream mathematics, external PDF correspondence and future P23-22 consumer integration. This audit neither seals P-G nor proves the full two_scale_kam theorem.

**Final disposition: PASS WITH NOTES, P23-21 private conditional package.**
