# W1-WEIGHTED independent audit 2 — tight delta

**Verdict: PASS WITH NOTES for the repaired infrastructure delta. F1, F2 and F4 are resolved. F3 remains PARTIAL as mathematics; its documentation is corrected. The complete `bpW:w1:coordinatewise` Hamiltonian-field specialization is still not proved by this package.** This verdict accepts the explicitly conditional helper, not completion of that source sentence. No provider or frozen anchor is supplied or sealed. `wave.nlw2.v1` / `KAM.Wave.nlw2` remains `DRAFT_SORRY` (FROZEN_UNPROVED); seal readiness is N/A.

## Scope and snapshot

- Worktree and report: `/root/code/KAM-inp-wpa`, report at the exact user-specified absolute path. User instructions override the generic brief's main-worktree destination.
- HEAD: `3a8280943c627d3c7289e30a3af70cbf187faa42`; initial `inp`: `d600c634e77f75013abaa6c27c985139e888f8c5`; merge-base: `fa002b432ee0a320a0c96c0654b083ce8bd3b00d`. Initial working tree clean.
- Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, round-1 report, and handoff including AUDIT FOCUS and Round 2. Applied lean-statement-audit and the local KAM refute-first audit workflow within this delta's scope.
- Comparison: `git diff inp...HEAD` establishes the package envelope; mathematical re-review is restricted to F1–F4 and `git diff a5b601ec HEAD -- KAM/Wave/Seq`, including consequences of changed interfaces. Unchanged statements and earlier not-done items were not re-audited. Source references below use this HEAD.
- Eight sequence modules changed since `a5b601ec`; the range also contains the earlier `diagCLM` → `weightedDiagCLM` rename at `84358bc9`, already present at round 1, and the repair commit `f937bb2d`. `Coordinatewise` code is unchanged after removing comments. `Diag` and `Flow` code is identical after removing comments/whitespace and normalizing that rename. Their HEAD hashes equal the round-1 hashes.
- Report-only repository edit; temporary probes/logs under `.lake/abi-scratch/`, removed after recording receipts. No source repair, generated-root regeneration, commits, or parallel audit-launched Lean/Lake commands. Every Lean/Lake invocation used `LEAN_NUM_THREADS=1` and `nice -n 5` (the gate supplies `nice` for builds). Other sessions on the shared host were outside this audit's control.

## Findings F1–F4

| Finding | Verdict | Evidence and boundary |
|---|---|---|
| F1: norm carrier | RESOLVED | `Transport.lean:151–170`: `ellNorm a p w hw := ‖tauLp a p w hw‖`, with explicit `hw : IsEll a p w`; series characterization and coefficient norm identity proved. Raw operations have distinct `ellTsumSq` / `ellTsumNorm` names and explicit off-domain documentation. |
| F2: Lipschitz codomain and sign | RESOLVED | `Linfty.lean:63–98`: source predicate now includes `0 ≤ L`, value membership for every point in `Dom`, and the difference bound. The weaker difference predicate is distinctly named. `Tails.lean:181–194` produces the repaired predicate, including value membership. |
| F3: actual Hamiltonian-field specialization | PARTIAL retained; documentation correction PASS | `Coordinatewise.lean:20–23` and handoff:99–101 explicitly mark the specialization PARTIAL. The declaration/proof at `Coordinatewise.lean:61–90` is unchanged. No actual `X^w` producer/composition has been added. |
| F4: package lint failures | RESOLVED | Original offending lines rewrapped; independent scan of all eight files finds no line over 100 characters. Prescribed SLIM lint receipt below controls the hygiene verdict. |

F1 refutation check: the old sequence `w_j = 1`, `a = p = 0` still makes the explicitly raw `ellTsumNorm` zero, and is still not `IsEll`. It cannot be passed to the source norm without proving the impossible membership. A negative elaboration test rejects treating `ellNorm 0 0 w` without `hw` as a real number. The universal source identity `ellNorm a p w hw = sqrt (Σ (ω‖w‖)²)` checks for arbitrary `RCLike K`. Proof irrelevance makes the value independent of the membership proof. This is a carrier repair with an actual series characterization, not merely a rename of the old purported norm. All remaining raw norm estimates in the delta retain `IsEll` output or use `coeffW` whose membership is produced. Source-facing product and embedding wrappers consume those produced proofs.

F2 refutation check: the old map `Ω ξ j = j` at `p = L = 0` still satisfies the distinct difference helper, but the source predicate is now provably false because its values are unbounded. Negative `L` is rejected even on the empty domain. Membership is required only on `Dom`, matching a map from `Π`; arbitrary ambient values outside `Dom` are irrelevant. The new pointwise equivalence retains both source conditions, and the tails consumer supplies each conjunct without assuming the desired Lipschitz result.

F3 first missing bridge: supply a defined `X^w : WaveSpace → WaveSpace`, produced from `bpW:w1:hamfield` (v), and prove its two coefficient identities before applying `frozen_invariance_iff`. In particular the second identity needs nonlinear representability/summability. Merely supplying `v`, `hv₁`, `hv₂` or relabeling them does not prove this existence. Round 1's conclusion that they are not circular invariance hypotheses is retained, not re-audited. The exact source sentence at `blueprint-W/parts/w1-sequences.tex:164–167` remains unclosed: “if ... X^w is the field of Proposition ... (v) ... is equivalent to ...”. Documentation resolves the overclaim, not this proof obligation. No new theorem-strengthening or hidden premise was introduced in this documentation-only change.

## Changed declaration ledger

Names below have prefix `KAM.Wave.`. PASS means the literal infrastructure interface, not frozen/campaign closure. Unchanged theorems affected solely by rebuilding their dependencies are outside the statement re-review.

| Node / file | Declarations | Verdict / reason |
|---|---|---|
| transport, `Transport:70,75,153` | `ellTsumSq`, `ellTsumNorm`, `ellNorm` | PASS; raw series separated from membership-carrier norm; F1 resolved. |
| space, `Transport:140,156,161,166` | `norm_tauLp_sq`, `ellNorm_eq_ellTsumNorm`, `ellNorm_coeffW`, `ellTsumNorm_coeffW` | PASS; same series identity and norm preservation, explicit source-facing characterization. |
| space (iv), `Transport:224,230` | `norm_prod_eq_max_ellTsumNorm`, `norm_prod_eq_max_ellNorm` | PASS; max product norm; `coeffW 1 1 = coeff` is unchanged, so the source wrapper represents the same frozen coefficients. |
| multiplier, `Multiplier:45,67,71,77,81,86,108` | `weightedDiagCLM`, `weightedDiagCLM_apply`, `norm_diagCLM_le`, `weightedDiagCLM_eq`, `norm_diagCLM_le'`, `norm_diagCLM_apply_of_norm_eq_one`, `norm_le_norm_diagCLM` | PASS; rename and wrapping only; multiplier formula, norm bound, and independence of bound unchanged. |
| embed, `Multiplier:186` | `isEll_coeffW_of_ratio_le` | PASS; prior bound under raw series names, membership still proved in the same conjunction. |
| embed, `Embed:49,58` | `ellTsumNorm_coeffW_le_of_le`, `ellTsumNorm_coeffW_le_of_lt` | PASS; prior estimates preserved, with membership output. |
| embed, `Embed:66,74` | `ellNorm_coeffW_le_of_le`, `ellNorm_coeffW_le_of_lt` | PASS; source norm wrappers; same losses and constant `(σ/(e(a−a′)))^σ`; target membership produced by the raw theorem. |
| coordinatewise, `Coordinatewise:20–23` | documentation for `frozen_invariance_iff` | PASS as scope correction; full specialization remains PARTIAL, F3. |
| diag / flow | `lamMul`, `rotCLM`, `cosCLM`, `sinCLM` | PASS for changed references; bodies unchanged modulo multiplier rename. |
| linfty, `Linfty:66,72` | `IsLinftyDiffLipschitz`, `IsLinftyLipschitz` | PASS; separately named raw difference condition and exact source map predicate. |
| linfty, `Linfty:76,90` | `isLinftyDiffLipschitz_iff`, `isLinftyLipschitz_iff` | PASS; former preserves old conditional difference characterization, latter includes sign and value membership. |
| tails, `Tails:181` | `isLinftyLipschitz_tildeOmegaSeq` | PASS; same explicit constant, now also proves source codomain and nonnegative constant. |

### Definition classification

| Definition | Classification / whole-carrier assessment |
|---|---|
| `ellTsumSq`, `ellTsumNorm` | Literal raw `tsum` and square root on arbitrary sequences, deliberately not source norms. Zero on a nonsummable squared series is disclosed; no theorem treats that fallback as a source norm. |
| `ellNorm` | Literal transported norm on `(w, hw : IsEll a p w)`; full finite source carrier. No choice, default, or deferred semantics. |
| `IsLinftyDiffLipschitz` | Literal pure difference predicate; it is explicitly not the source map-to-ℓ∞ predicate. |
| `IsLinftyLipschitz` | Literal source predicate: sign, on-domain codomain membership, and norm difference inequality. Not an assumed theorem bundle: these are exactly the defining conditions from `w1-sequences.tex:254–261`. |
| `weightedDiagCLM`; changed references in `embedCLM`, `lamMul`, `rotCLM`, `cosCLM`, `sinCLM` | Existing audited constructions under rename, with no changed formula or branch. No new semantics to audit. |

For each literal definition above: **BODY_MATCH: OK; PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: N/A_LITERAL; CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS.** For `ellNorm`, the additional source series characterization is proved by `ellNorm_eq_ellTsumNorm` and independently instantiated. Unchanged `IsEll`, `tauLp`, and `IsLinfty` are bound to the round-1 audited definitions, not reconstructed in this round.

### Binder check for the new source-facing interfaces

The following expanded inputs are the only binder families in the new/repaired norm wrappers. The `IsEll` proof argument is membership of the source domain, not an assumed norm estimate. No structure, typeclass, or Prop alias adds an unproduced analytic result.

| Binder | Bin | Source meaning |
|---|---|---|
| `K : Type*` | TYPING | real/complex scalar abstraction |
| `[RCLike K]` | TYPING | scalar operations; not an assumed PDE/estimate |
| `a : ℝ` | TYPING | weight parameter; valid extension to all real a |
| `p : ℝ` | TYPING | regularity parameter |
| `w : ℕ+ → K` | TYPING | coefficient sequence |
| `hw : IsEll a p w` | SOURCE | finite weighted source carrier (`w0:51–58`) |
| `y : lp (fun _ : ℕ+ => K) 2` | TYPING | represented weighted coordinates (`w1:30–37`) |
| `z : WaveSpace` | TYPING | product of represented coordinates (`w1:132–134`) |
| `a' : ℝ` | TYPING | target weight |
| `p' : ℝ` | TYPING | target regularity |
| `ha : a' ≤ a` | SOURCE | embedding (i), `w1:199–202` |
| `hp : p' ≤ p` | SOURCE | embedding (i), same |
| `ha : a' < a` | SOURCE | embedding (ii), `w1:203–205` |
| `hp : p < p'` | SOURCE | embedding (ii), positive σ |
| `L : ℝ` | TYPING | Lipschitz constant parameter |
| `Dom : Set (Fin 2 → ℝ)` | TYPING | source Π |
| `Ω : (Fin 2 → ℝ) → ℕ+ → ℝ` | TYPING | ambient representation of source map; on-Π membership in predicate |
| `hL : 0 ≤ L` (difference iff only) | SOURCE | source nonnegative Lipschitz convention |
| `m : ℝ` | TYPING | mass parameter of tails |
| `hm : 0 < m` | STANDING | positive mass from w0 / frozen convention |

Per-declaration counts (each named weight counted separately, implicit scalar type/instance included):

| Declaration | SOURCE | STANDING | TYPING | RULED | EXCESS |
|---|---:|---:|---:|---:|---:|
| `ellNorm_eq_ellTsumNorm` | 1 | 0 | 5 | 0 | 0 |
| `ellNorm_coeffW` | 0 | 0 | 5 | 0 | 0 |
| `norm_prod_eq_max_ellNorm` | 0 | 0 | 1 | 0 | 0 |
| `ellNorm_coeffW_le_of_le` | 2 | 0 | 7 | 0 | 0 |
| `ellNorm_coeffW_le_of_lt` | 2 | 0 | 7 | 0 | 0 |
| `isLinftyDiffLipschitz_iff` | 1 | 0 | 4 | 0 | 0 |
| `isLinftyLipschitz_iff` | 0 | 0 | 4 | 0 | 0 |
| `isLinftyLipschitz_tildeOmegaSeq` | 0 | 1 | 1 | 0 | 0 |

`isLinftyLipschitz_iff` is an equivalence of literal definitions: its right-hand sign/membership conditions are not extra hypotheses on a source theorem. The tails proof produces these conditions. F3's unchanged binders retain round 1's explicit distinction between a valid conditional helper and EXCESS relative to the complete field-specialization claim.

## Independent verification receipts

All commands below ran from `/root/code/KAM-inp-wpa`, sequentially.

Gated targeted build, **exit 0**:

```sh
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpa KAM.Wave.Seq.Transport KAM.Wave.Seq.Multiplier KAM.Wave.Seq.Embed KAM.Wave.Seq.Coordinatewise KAM.Wave.Seq.Diag KAM.Wave.Seq.Flow KAM.Wave.Seq.Linfty KAM.Wave.Seq.Tails
```

```text
[inp-gate] slot 1 acquired 17:34:45 for KAM.Wave.Seq.Transport KAM.Wave.Seq.Multiplier KAM.Wave.Seq.Embed KAM.Wave.Seq.Coordinatewise KAM.Wave.Seq.Diag KAM.Wave.Seq.Flow KAM.Wave.Seq.Linfty KAM.Wave.Seq.Tails
Build completed successfully (2799 jobs).
```

The wrapper runs `nice -n 5 lake build` with exactly those eight targets. No root/library rebuild, clean, update, or cache fetch was requested.

Kernel replay, **exit 0**, one invocation:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Wave.Seq.Transport KAM.Wave.Seq.Multiplier KAM.Wave.Seq.Embed KAM.Wave.Seq.Coordinatewise KAM.Wave.Seq.Diag KAM.Wave.Seq.Flow KAM.Wave.Seq.Linfty KAM.Wave.Seq.Tails
```

```text
replaying KAM.Wave.Seq.Tails
replaying KAM.Wave.Seq.Linfty
replaying KAM.Wave.Seq.Flow
replaying KAM.Wave.Seq.Diag
replaying KAM.Wave.Seq.Coordinatewise
replaying KAM.Wave.Seq.Embed
replaying KAM.Wave.Seq.Multiplier
replaying KAM.Wave.Seq.Transport
```

Fresh exact-body, series-characterization, negative-counterexample, consumer and axiom probe, **exit 0**, no errors or warnings:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/W1Round2.lean
```

The 20 `#print axioms` commands cover every new/renamed theorem or theorem whose type/body changed in the assigned sequence delta. Unchanged statements were not re-audited. All outputs are exactly the permitted standard axiom set; no `sorryAx` or project axiom:

```text
'KAM.Wave.ellTsumNorm_coeffW_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.ellTsumNorm_coeffW_le_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.ellNorm_coeffW_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.ellNorm_coeffW_le_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.isLinftyDiffLipschitz_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.isLinftyLipschitz_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.weightedDiagCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_diagCLM_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.weightedDiagCLM_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_diagCLM_le'' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_diagCLM_apply_of_norm_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_le_norm_diagCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.isEll_coeffW_of_ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.isLinftyLipschitz_tildeOmegaSeq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_tauLp_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.ellNorm_eq_ellTsumNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.ellNorm_coeffW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.ellTsumNorm_coeffW' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_prod_eq_max_ellTsumNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.norm_prod_eq_max_ellNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The rest of the successful scratch probe is reproduced for the negative tests and interface checks; the first four imports/open commands were `import KAM.Wave.Seq.Coordinatewise`, `import KAM.Wave.Seq.Flow`, `import KAM.Wave.Seq.Tails`, `open KAM.Wave`. These imports transitively load all eight modules. Probe SHA256: `7da0d0f3dd8bd2375678e6e5e635048ec52fdbc1fb402b8f18dca4e7c8656262`.

```lean
-- Source norm: exact body, full finite carrier, series identity, proof independence.
example {K : Type*} [RCLike K] (a p : ℝ) (w : ℕ+ → K) (hw : IsEll a p w) :
    ellNorm a p w hw = ‖tauLp a p w hw‖ := rfl
example {K : Type*} [RCLike K] (a p : ℝ) (w : ℕ+ → K) (hw : IsEll a p w) :
    ellNorm a p w hw = Real.sqrt (∑' j : ℕ+, (ellWeight a p j * ‖w j‖)^2) :=
  ellNorm_eq_ellTsumNorm a p w hw
example (a p : ℝ) (w : ℕ+ → ℝ) (h h' : IsEll a p w) :
    ellNorm a p w h = ellNorm a p w h' := rfl
example : True := by
  fail_if_success have bad : ℝ := ellNorm 0 0 (fun _ : ℕ+ => (1 : ℝ))
  trivial
example : ¬ IsEll 0 0 (fun _ : ℕ+ => (1 : ℝ)) := by
  unfold IsEll
  rw [memℓp_gen_iff (by norm_num)]
  simpa [ellWeight] using
    (show ¬ Summable (fun _ : ℕ+ => (1 : ℝ)) by simp [summable_const_iff])
example : ellTsumNorm 0 0 (fun _ : ℕ+ => (1 : ℝ)) = 0 := by
  have hn : ¬ Summable (fun _ : ℕ+ => (1 : ℝ)) := by simp [summable_const_iff]
  simp [ellTsumNorm, ellTsumSq, ellWeight, tsum_eq_zero_of_not_summable hn]
-- Source predicates: exact definition and full pointwise equivalence.
example (p L : ℝ) (D : Set (Fin 2 → ℝ)) (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ) :
    IsLinftyLipschitz p L D Ω ↔
      0 ≤ L ∧ (∀ ξ ∈ D, IsLinfty p (Ω ξ)) ∧ IsLinftyDiffLipschitz p L D Ω := Iff.rfl
example (p L : ℝ) (D : Set (Fin 2 → ℝ)) (Ω : (Fin 2 → ℝ) → ℕ+ → ℝ) :
    IsLinftyLipschitz p L D Ω ↔ 0 ≤ L ∧ (∀ ξ ∈ D, IsLinfty p (Ω ξ)) ∧
      ∀ ξ ∈ D, ∀ ζ ∈ D, ∀ j : ℕ+, |Ω ξ j - Ω ζ j| * (j : ℝ)^p ≤ L * ‖ξ - ζ‖ :=
  isLinftyLipschitz_iff
-- Old counterexample still satisfies only the distinctly named difference helper.
example : IsLinftyDiffLipschitz 0 0 Set.univ (fun _ j => (j : ℝ)) := by
  apply (isLinftyDiffLipschitz_iff (by norm_num)).2
  simp
example : ¬ IsLinftyLipschitz 0 0 Set.univ (fun _ j => (j : ℝ)) := by
  intro h
  have hi : IsLinfty 0 (fun j : ℕ+ => (j : ℝ)) := h.2.1 0 (Set.mem_univ _)
  obtain ⟨C, hC⟩ := memℓp_infty_iff.1 hi
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hb := hC (Set.mem_range_self n.succPNat)
  have hb2 : |(n : ℝ) + 1| ≤ C := by simpa [Real.norm_eq_abs] using hb
  rw [abs_of_nonneg (by positivity)] at hb2
  linarith
example : ¬ IsLinftyLipschitz 0 (-1) ∅ (fun _ _ => 0) := by
  intro h
  have := h.1
  norm_num at this
-- Actual tails consumer supplies all parts of the repaired source predicate.
example (m : ℝ) (hm : 0 < m) (ξ : Fin 2 → ℝ) :
    IsLinfty 1 (tildeOmegaSeq m hm ξ) :=
  (isLinftyLipschitz_tildeOmegaSeq hm).2.1 ξ (Set.mem_univ _)
example (m : ℝ) (hm : 0 < m) :
    IsLinftyDiffLipschitz 1 (3 / (2 * Real.pi) * (1 / lam m hm 1 + 1 / lam m hm 2))
      Set.univ (tildeOmegaSeq m hm) :=
  (isLinftyLipschitz_tildeOmegaSeq hm).2.2
```

### Protected paths, size and source hygiene

```sh
git diff inp...HEAD -- KAM/Frozen manifest README.md
git diff a5b601ec HEAD -- KAM/Frozen manifest README.md KAM.lean KAM/Root
git diff --check inp...HEAD
git diff --check
```

All four commands: empty output, **exit 0**. HEAD and inp remained at the snapshot hashes above through verification.

The generic broader comparison `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` remains nonempty solely for the inherited generated-root addition. The package envelope also adds generated `KAM/Root/Wave.lean` (24 lines). These are unchanged since the round baseline; the narrower AUDIT FOCUS protected-path check passes. The round-1 generated-root deviation is carried forward, not waived or repaired. This delta introduces no new protected-file change.

```sh
rg -n 'sorry|admit|axiom|unsafe|opaque|set_option|EuclideanSpace|KAM.Provider|KAM.Frozen.*Theorems' KAM/Wave/Seq
```

No matches, **exit 1** (successful absence check). No proof escape, resource override, provider import, or draft theorem import in these eight modules. The independent Unicode character scan found **zero** lines over 100 characters. `wc -l`:

```text
94 Coordinatewise.lean
161 Diag.lean
110 Embed.lean
250 Flow.lean
102 Linfty.lean
211 Multiplier.lean
198 Tails.lean
237 Transport.lean
1363 total
```

No file approaches the 1500-line cap. Module-system and frozen-integrity checks are covered by the prescribed lint receipt. SHA256 of audited files:

| File under `KAM/Wave/Seq/` | SHA256 |
|---|---|
| `Coordinatewise.lean` | `7c1f37053a19f71aa182a4a31557fa8b7ca98094b0ea66b001bf9a1fd80d947a` |
| `Diag.lean` | `5c4cdfff9ba620d92fbf31f249aba200e04497b3bd36c7e5428cc77eabcffe27` |
| `Embed.lean` | `5b3019c82acf272db1966595bda2fd03b8fc97ef981f8f013734ee2831acb845` |
| `Flow.lean` | `5d24be039a3fea6a96d31e40b4f7bf3e93ab5ec3709e6ccb3ae807181e3cb1f3` |
| `Linfty.lean` | `0ce25cdbe57ba2da697e8ab09031a3b588b2688a17b3485d7dd03a70d5448f46` |
| `Multiplier.lean` | `5f116cdc38e974a4e29df46fe522e68b4f844c8d2667b006c967cb160c8dba74` |
| `Tails.lean` | `c72510a5ed7a3544afccf957d7f30e825a357d3c996824e0d5eea451f5b2ba1f` |
| `Transport.lean` | `74ffff5ef2616bb018058a27994fea5982dcf973de0b5568fe05d47bb59fc28a` |

### Prescribed SLIM lint

```sh
env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpa
```

**Exit 0**, complete output:

```text
check_lean_modules: PASS (1636 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

This wrapper invokes `nice -n 5 sh scripts/lint_sources.sh` with the prescribed temporary build overlay for the ABI probe. No generated-root exception was needed for this run; F4 is resolved by a passing substantive lint, not by suppressing an error.

## Source defects, remaining gaps, and handoff

No new suspected pinned-source/blueprint defect was established, and no new defect was found in the assigned changed lines. F1/F2 were implementation carrier defects and are now repaired. The source requires finite weighted norm (`w0-conventions.tex:51–58`) and a map into ℓ∞ with `L ≥ 0` (`w1-sequences.tex:254–261`); the repaired definitions now encode those requirements.

F3 remains the exact source-completion limitation quoted above, not a source erratum. Do not mark the complete Hamiltonian-field specialization or the frozen PDE theorem proved from this result. The round-1 generated-root deviation is inherited and unchanged; the later Round 2 handoff supersedes earlier naming/completion prose. No deviations were introduced by the auditor.

Files delivered: **only `docs/tracks/W/audits/W1-WEIGHTED-audit-2.md`**. All audit-created `W1Round2*` probe/inventory/log files were removed after recording their commands, output, and relevant contents here. Final working-tree status contains only this report; whitespace and Markdown fence checks pass. The build, 20 theorem axiom checks, negative/interface probes, eight-module kernel replay, prescribed lint, frozen-anchor guard, ABI checks, and protected-path delta checks all passed. Unchanged statement verdicts and earlier not-done items remain those of round 1; this is not a fresh whole-package or campaign audit.
