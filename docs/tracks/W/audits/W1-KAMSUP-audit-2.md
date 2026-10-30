# W1-KAMSUP independent package audit 2

2026-10-30 UTC. **Scoped overall verdict: PASS WITH NOTES.** F1's operator-norm carrier and characterization are repaired. F2's new theorems are correct and recover the exact blueprint conclusion without a sign premise. **The reported blueprint defect is refuted:** negative `c` forces `A = 0`, so the claimed counterexample with `A ≠ 0` cannot satisfy domination. Correct the handoff and the explanatory Lean docstring; no source amendment is justified by this argument.

This is a tight delta audit, not a fresh approval of the whole package. No provider, frozen theorem or seal belongs to this infrastructure package; seal readiness is N/A. No W4 consumption, graph closure, or headline theorem closure is asserted.

## Scope and frozen inputs

Tier 2, independent of the author, report/scratch-only. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the handoff including AUDIT FOCUS and Round 2, and audit 1. Read the actual track statement file `docs/tracks/W/W-STATEMENTS.md` (there is no `statement.md`), interpreted under D41. The prompt overrides the brief's generic report destination: this report is inside `/root/code/KAM-inp-wpg`, not the main inp worktree.

Snapshot `round2-v1`:

- HEAD: `d4c130240aac5732a9e7913d7957660cf449712b`.
- Local `inp`: `7b86cf178eaaffba3a7a4205a561b41ef3660455`; merge base: `72cd9d25f9e995b13475054d22d51d2872bb42aa`.
- Requested delta baseline: `66034635`; round-1 audited HEAD: `f89dd8b1825a1bb4dffd6fdbfb2f303a0e47ff22`.
- Compared `git diff inp...HEAD` and read all changed KamSupport lines in `git diff 66034635 HEAD -- KAM/Wave/KamSupport`. The latter contains only `HilbertMatrix.lean` (35 additions/5 deletions), `KamSpace.lean` (39/16), and `SchurTest.lean` (6/6). The SchurTest renames already belong to the round-1 audited revision; its current bytes match audit 1.
- All six other KamSupport modules and the blueprint match the round-1 SHA256 values. Their mathematical audits are carried, not repeated. Nine-module kernel replay and axiom inspection are fresh hygiene checks, not a wider mathematical re-audit.

| Frozen input | SHA256 |
|---|---|
| `KAM/Wave/KamSupport/KamSpace.lean` | `d10482337701efbbfb841eef86fa744c29df47cda8548c6461c5202401c26c52` |
| `KAM/Wave/KamSupport/HilbertMatrix.lean` | `0e1e0fc6bf7c11be10b442c4960613cd87a87cf53f56d0882681ad78214d6819` |
| `KAM/Wave/KamSupport/SchurTest.lean` | `cd7c21eb584338a0b38383a71efadef5ae71a90523f9048898d3d94f7465433c` |
| `blueprint-W/parts/w1-sequences.tex` | `b27ab7134c188941198e547c4577e3263e0e5f618a41ebd6983ac48b8b07e796` |
| `docs/tracks/W/audits/W1-KAMSUP-audit-1.md` | `fc7852607ce6d54f54788a5454b4cec42c08e2a4c90eb2192fe947db07521b2c` |
| `docs/tracks/W/audits/W1-KAMSUP-handoff.md` | `beb1bf47616bb6df44de2bf0bf727fa69a81dc88b85ec1baf0900d90a3a6a07e` |

## F1: carrier and least-admissible characterization — PASS

Source anchor: `blueprint-W/parts/w1-sequences.tex:931-938` at round2-v1: **“For s,r>0”** and **“the least C≥0 ... (the operator norm; used only for bounded L ...)”**.

`KamSpace.lean:61-77` now uses the literal predicate
`KamOpAdmissible r s L C := 0 ≤ C ∧ ∀ W, kamNorm r (L W) ≤ C * kamNorm s W`, and a `KamBoundedMap r s` carries an actual complex-linear map, positive `r,s`, and existence of such a bound. This is boundedness of the source map, not an assumed value or least-constant conclusion. On each positive-radius space the displayed scaled sum is equivalent to the ordinary product norm, so this is the same bounded-map carrier in weighted coordinates; no CLM instance conversion is claimed here.

The admissible set is nonempty by `bounded`, and bounded below by zero. `kamOpNorm_apply_le` handles zero input norm using positive definiteness, and otherwise divides by the strictly positive input norm and uses the lower-bound property of the infimum. `kamOpNorm_le` uses an actual admissible constant. `kamOpNorm_isLeast` combines admissibility and minimality on **every inhabitant of its public carrier**. There is no empty-set fallback reachable through `kamOpNorm`.

Refutation attempts: the old `r=1,s=0` witness cannot inhabit the new carrier (`L.pos_s` gives `0<0`); an algebraic map without a finite bound cannot supply `L.bounded`. The scratch probe elaborates the expanded source characterization and direct application estimate with no loose `C` input. It also checks nonemptiness directly. Different proofs of boundedness do not change the defining set or its infimum, which only uses `toLinear`.

`kamNorm` itself is unchanged arithmetic on real parameters, and still degenerates at radius zero. Its explicit round-2 documentation (`KamSpace.lean:26-28`) restricts its norm interpretation to positive radii. This audit accepts the raw formula in that role; it does **not** declare it a norm for arbitrary real radius. The source operator-norm interface now enforces the positive locus structurally. `kamNorm_nonneg` actually takes `0 ≤ r`, not the handoff's claimed `0 < r`; this is a valid stronger range. Positive definiteness takes `0 < r`.

Definition classification:

| Definition | Classification / whole-carrier check | Verdict |
|---|---|---|
| `KamOpAdmissible` | Literal predicate on `r,s,L,C`; both conjuncts exactly expanded, no hidden operator construction. | PASS |
| `KamBoundedMap` | Source-domain structure: linearity, positive radii, finite bound; no conclusion-shaped field. | PASS |
| `kamOpNorm` | Infimum over a proved nonempty, lower-bounded set on the entire bounded-map carrier. | PASS |
| `kamNorm` | Unchanged raw scaled-sum formula; source norm interpretation restricted to positive radii. | PASS WITH NOTES above |

For `kamOpNorm`: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS OK; CHARACTERIZATION OK (`kamOpNorm_isLeast`); CHOICE_INDEPENDENCE N/A (no selected witness is used to define the number); DEFINITION_VERDICT PASS.

## F2: premise-free Schur estimates — PASS WITH NOTES

Source anchor: `blueprint-W/parts/w1-sequences.tex:1158-1160` at round2-v1:
**“If F_ij satisfies ... then F defines a bounded operator with ‖F‖ ≤ c(1+π/√3)‖A‖ ≤ 3c‖A‖.”** No sign premise is stated.

`HilbertMatrix.lean:359-408` retains the exact-constant proof under distinct `_nonneg` names. Lines 410-417 prove `KamDominated.of_le_const` by multiplying `c ≤ c'` by the nonnegative entry norm (divided by a positive off-diagonal distance). No sign of `c` is required. Lines 424-437 invoke the `_nonneg` results with `max c 0`, supplying both nonnegativity and domination monotonically. Both original source-facing names now have no excess `hc` binder. The renamed helper is `of_le_const`, as requested; no `mono_const` use remains in package code.

The new constants are syntactically different but **equal to the literal constants under the actual domination premise**. This is not a mathematical weakening: the probe below proves both the exact Schur bound and the exact operator-existence statement at the original blueprint types, consuming the current package exports without any additional sign hypothesis. These exact no-sign wrappers are audit evidence, not newly landed package exports. Adding them to the public API would make source consumption more direct.

### Reported blueprint defect — REFUTED; documentation correction needed

The Round 2 handoff says:

> for `c < 0` and `A ≠ 0`, the matrix `F = 0` satisfies the domination hypotheses

This is false. `HilbertMatrix.lean:421-423` repeats the related assertion that the literal inequality would fail for `A ≠ 0`, overlooking that domination excludes this case.

Independently reconstructed argument: for `c<0`, the diagonal clauses give `0 ≤ ‖F_ii‖ ≤ c‖A_ii‖`, hence `A_ii=0`. For `i≠j`, multiply `0 ≤ ‖F_ij‖ ≤ c‖A_ij‖/|i-j|` by the strictly positive `|i-j|`; again `A_ij=0`. Thus all entries vanish. A bounded operator on ℓ² is determined by its values on the canonical basis, whose finite linear span is dense; consequently `A=0`. Domination also forces `F=0`. All literal upper bounds are then zero, even though `c<0`. The same conclusion follows for real or complex scalars (`RCLike K` in the probe).

Adversarial check: the round-1 example `A=0,F=0,c=-1` still shows that domination need not imply `c≥0`. It does **not** refute the blueprint. The correct disjunction is `0 ≤ c ∨ A = 0`. I checked the infinite-dimensional step in Lean using `lp.ext_continuousLinearMap`, not just a finite-matrix analogy. Attempting to retain `A≠0` contradicts the proved `audit_A_zero`.

Disposition: no new P96-K or blueprint erratum is supported. Retract the proposed tacit-sign defect and correct the handoff/docstring explanation. The `_nonneg` specializations are valid; the unrestricted `max` versions are valid and recover the exact source conclusion. This is a nonblocking documentation finding, not a false proved theorem.

## Changed-declaration ledger and binder classification

Namespace prefix `KAM.Wave`; file lines refer to round2-v1. Unchanged declarations are governed by audit 1.

| Node / file:line | Declaration | Verdict | Reason |
|---|---|---|---|
| kam-space / KamSpace:61 | `KamOpAdmissible` | PASS | Literal expanded admissibility predicate. |
| kam-space / KamSpace:66 | `KamBoundedMap` | PASS | Faithful bounded positive-radius carrier. |
| kam-space / KamSpace:76 | `kamOpNorm` | PASS | No empty admissible-set branch on its carrier. |
| kam-space / KamSpace:108 | `kamOpNorm_apply_le` | PASS | Applies to every bounded map and vector, no extra admissible constant input. |
| kam-space / KamSpace:123 | `kamOpNorm_nonneg` | PASS | Infimum of nonnegative admissible constants. |
| kam-space / KamSpace:127 | `kamOpNorm_le` | PASS | Minimality against each literal admissible bound. |
| kam-space / KamSpace:132 | `kamOpNorm_isLeast` | PASS | Full membership plus minimality characterization. |
| schur / HilbertMatrix:359 | `kamSchurBound_of_dominated_nonneg` | PASS | Distinct exact-constant specialization under explicitly named sign premise. |
| schur / HilbertMatrix:397 | `exists_clm_of_dominated_nonneg` | PASS | Same specialization, HasSum for every input/row and both exact constants. |
| schur / HilbertMatrix:410 | `KamDominated.of_le_const` | PASS | Valid literal monotonicity helper; orchestrator rename accounted for. |
| schur / HilbertMatrix:424 | `kamSchurBound_of_dominated` | PASS WITH NOTES | No sign premise; max constant equals literal constant under domination; false defect explanation above. |
| schur / HilbertMatrix:432 | `exists_clm_of_dominated` | PASS WITH NOTES | Exact original conclusion recovered by compiled term-level composition below. |
| SchurTest:39 | `KamSchurBound.bound_nonneg` | PASS | Name-only change from requested baseline; already in audit 1. |
| SchurTest:41 | `KamSchurBound.bound_mono` | PASS | Name-only change; all changed call sites resolve correctly. |

Expanded binders (counts are for grouped parameter families; each row names one binder or repeated binder schema):

| Binder | Bin | Source / role |
|---|---|---|
| `r : ℝ` | TYPING | Radius parameter in kam-space definition. |
| `s : ℝ` | TYPING | Radius parameter in kam-space definition. |
| `L.toLinear : KamPhase →ₗ[ℂ] KamPhase` | SOURCE | Source linear map in weighted coordinates. |
| `L.pos_r : 0 < r` | SOURCE | “For s,r>0”. |
| `L.pos_s : 0 < s` | SOURCE | Same. |
| `L.bounded : ∃ C, 0 ≤ C ∧ ∀ W, ...` | SOURCE | “used only for bounded L”; not the least constant. |
| `W : KamPhase` | TYPING | Vector quantified in the defining operator inequality. |
| `C : ℝ` (comparison lemma) | TYPING | Candidate admissible scalar. |
| `hC : 0 ≤ C ∧ ∀ W, ...` (comparison lemma) | SOURCE | Definition's comparison class, not a premise of `kamOpNorm_isLeast`. |
| `K : Type*` | TYPING | Scalar carrier. |
| `[RCLike K]` | TYPING | Source ℝ/ℂ Hilbert scalars. |
| `A : lp ... 2 →L[K] lp ... 2` | SOURCE | Bounded operator from the Schur preamble. |
| `F : ℕ+ → ℕ+ → K` | TYPING | Source candidate matrix. |
| `c : ℝ` | TYPING | Source domination constant. |
| `h.off : ∀ i j, i≠j → ‖F i j‖ ≤ ...` | SOURCE | Schur (iii) off-diagonal clause. |
| `h.diag : ∀ i, ‖F i i‖ ≤ ...` | SOURCE | Schur (iii) diagonal clause. |
| `hc : 0 ≤ c` in `_nonneg` only | SOURCE of named specialization | Explicit narrower helper, not the unrestricted node export. |
| `M : ℕ+ → ℕ+ → K` in `of_le_const` | TYPING | Generic matrix-monotonicity helper. |
| `c' : ℝ` in `of_le_const` | TYPING | Larger candidate constant. |
| `hc : c ≤ c'` in `of_le_const` | SOURCE of helper | Literal monotonicity statement, supplied by `le_max_left` at use. |

Grouped inventory: TYPING 10; SOURCE (including the explicitly distinct specialization/helper statements) 10; STANDING 0; RULED 0; EXCESS 0. The two fields inside `hC` and `bounded` are displayed fully above; no hidden regularity, convergence or operator-existence field occurs. `KamDominated` expands to exactly `off` and `diag`. No constant has acquired dependence on an input vector or row.

## Verification

All Lean/Lake-related commands were serialized with `LEAN_NUM_THREADS=1`; wrappers supply `nice -n 5`. No heartbeat, recursion-depth, or synthesis-budget override; no clean, update, cache fetch, provider import, production edit, or git mutation. Commands run from `/root/code/KAM-inp-wpg`; logs remain in `.lake/abi-scratch/wpg2-{build,kernel,probe,axioms,lint}.log`.

1. Targeted gate build:

```sh
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpg KAM.Wave.KamSupport.SchurTest KAM.Wave.KamSupport.HilbertMatrix KAM.Wave.KamSupport.KamSpace
```

Exit 0. Output:

```text
[inp-gate] slot 1 acquired 19:21:01 for KAM.Wave.KamSupport.SchurTest KAM.Wave.KamSupport.HilbertMatrix KAM.Wave.KamSupport.KamSpace
Build completed successfully (3160 jobs).
```

2. Kernel replay (single invocation):

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Wave.KamSupport.KamSpace KAM.Wave.KamSupport.FourierL2 KAM.Wave.KamSupport.FourierBessel KAM.Wave.KamSupport.FourierShift KAM.Wave.KamSupport.HilbertMatrix KAM.Wave.KamSupport.SchurTest KAM.Wave.KamSupport.FourierBanach KAM.Wave.KamSupport.Lattice KAM.Wave.KamSupport.LatticeCount
```

Exit 0. Output:

```text
replaying KAM.Wave.KamSupport.LatticeCount
replaying KAM.Wave.KamSupport.Lattice
replaying KAM.Wave.KamSupport.FourierBanach
replaying KAM.Wave.KamSupport.SchurTest
replaying KAM.Wave.KamSupport.HilbertMatrix
replaying KAM.Wave.KamSupport.FourierShift
replaying KAM.Wave.KamSupport.FourierBessel
replaying KAM.Wave.KamSupport.FourierL2
replaying KAM.Wave.KamSupport.KamSpace
```

3. `env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Wpg2Probe.lean`: final exit 0, no warnings. Exact output:

```text
'audit_A_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'audit_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'audit_exact_schur' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Two preliminary probe attempts failed on scratch-only `ext` pattern handling; corrected using explicit CLM extensionality followed by `lp.ext` and `funext`. No package failure or budget increase occurred. Final probe SHA256: `0b6d246bac3464ccf322f439e4e49563cb577577cb91aa292db78d56fc8fc60a`.

4. `env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/Wpg2Axioms.lean`: exit 0; **132/132 public declarations** have exactly `[propext, Classical.choice, Quot.sound]`, zero unexpected lines/axioms. This includes every changed theorem, structure, definition and the renamed helpers. Generated by walking all nine modules' namespaces and public `def|abbrev|structure|theorem|lemma` declarations (private lemmas excluded), then emitting one `#print axioms` each. Probe SHA256 `ea151b59cc58c747bf674c7c9614568195fa523c447c325133c9d3bf94157558`. Examples:

```text
'KAM.Wave.kamOpNorm_isLeast' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.exists_clm_of_dominated' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.exists_clm_of_dominated_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.KamDominated.of_le_const' depends on axioms: [propext, Classical.choice, Quot.sound]
```

5. Authorized SLIM lint wrapper (which runs `scripts/lint_sources.sh`):

```sh
env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpg
```

Exit 0, exact output:

```text
check_lean_modules: PASS (1659 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

No generated-root warning or other lint exception occurred. Regenerated roots were authorized by the prompt; this audit did not regenerate anything.

6. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty. `KAM/Root/Wave.lean` contains exactly the nine authorized package public imports. `git diff --check inp...HEAD`, `git diff --check 66034635 HEAD`, and `git diff --check`: exit 0, no output. Forbidden-token/budget/provider-import scan of all nine module sources: no matches. Maximum module length is 439 lines (`HilbertMatrix`); module headers, exposure and import shape checked on the delta. `SchurTest.lean` is byte-identical to audit 1, including the renamed public helpers.

7. Final snapshot recheck: all six SHA256 values in the frozen-input table still match. HEAD and `inp` unchanged; complete `git diff inp...HEAD` byte-identical to the saved initial diff. Both temporary `.lean` probes deleted; their exact final proof source is retained below and the axiom probe generation is described above. `git status --short` shows only this untracked report. Report trailing-whitespace and code-fence checks pass.

## Reproducible exact-source and refutation probe

Recreate under `.lake/abi-scratch/`, run the command above, then delete. This is audit evidence only; it does not replace or edit a frozen declaration. It uses the actual package exports at round2-v1.

```lean
import KAM.Wave.KamSupport.HilbertMatrix
import KAM.Wave.KamSupport.KamSpace
noncomputable section
open KAM.Wave
variable {K : Type*} [RCLike K]

theorem audit_entries_zero {F M : ℕ+ → ℕ+ → K} {c : ℝ}
    (hc : c < 0) (h : KamDominated F M c) : ∀ i j, M i j = 0 := by
  intro i j
  by_cases hij : i = j
  · subst j
    have hn := (norm_nonneg (F i i)).trans (h.diag i)
    have hz : ‖M i i‖ = 0 := by nlinarith [norm_nonneg (M i i)]
    exact norm_eq_zero.mp hz
  · have hd : 0 < |(i : ℝ) - (j : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hij))
    have hn := (norm_nonneg (F i j)).trans (h.off i j hij)
    have hn' : 0 ≤ c * ‖M i j‖ := by simpa using (le_div_iff₀ hd).mp hn
    have hz : ‖M i j‖ = 0 := by nlinarith [norm_nonneg (M i j)]
    exact norm_eq_zero.mp hz

theorem audit_A_zero (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2)
    {F : ℕ+ → ℕ+ → K} {c : ℝ} (hc : c < 0) (h : KamDominated F (kamEntry A) c) : A = 0 := by
  have he := audit_entries_zero hc h
  apply lp.ext_continuousLinearMap (by norm_num)
  intro j
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext i
  have hb : A (kamBasis K j) = 0 := by
    ext i
    exact he i j
  have hs : lp.single 2 j x = x • kamBasis K j := by
    simp [kamBasis, ← lp.single_smul]
  change A (lp.single 2 j x) i = 0
  rw [hs, map_smul, hb, smul_zero]
  rfl

theorem audit_exact (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2)
    {F : ℕ+ → ℕ+ → K} {c : ℝ} (h : KamDominated F (kamEntry A) c) :
    ∃ T : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2,
      (∀ v i, HasSum (fun j => F i j * v j) (T v i)) ∧
        ‖T‖ ≤ c * (1 + Real.pi / Real.sqrt 3) * ‖A‖ ∧ ‖T‖ ≤ 3 * c * ‖A‖ := by
  obtain ⟨T, hT, h1, h2⟩ := exists_clm_of_dominated A h
  by_cases hc : 0 ≤ c
  · exact ⟨T, hT, by simpa [max_eq_left hc] using h1, by simpa [max_eq_left hc] using h2⟩
  · have hA := audit_A_zero A (lt_of_not_ge hc) h
    subst A
    exact ⟨T, hT, by simpa using h1, by simpa using h2⟩

theorem audit_exact_schur (A : lp (fun _ : ℕ+ => K) 2 →L[K] lp (fun _ : ℕ+ => K) 2)
    {F : ℕ+ → ℕ+ → K} {c : ℝ} (h : KamDominated F (kamEntry A) c) :
    KamSchurBound F (c * (1 + kamHilbertConst) * ‖A‖) := by
  have hb := kamSchurBound_of_dominated A h
  by_cases hc : 0 ≤ c
  · simpa [max_eq_left hc] using hb
  · have hA := audit_A_zero A (lt_of_not_ge hc) h
    subst A
    simpa using hb

example {r s : ℝ} (L : KamBoundedMap r s) :
    IsLeast {C : ℝ | 0 ≤ C ∧ ∀ W, kamNorm r (L.toLinear W) ≤ C * kamNorm s W} (kamOpNorm L) :=
  kamOpNorm_isLeast L
example {r s : ℝ} (L : KamBoundedMap r s) :
    ∃ C, 0 ≤ C ∧ ∀ W, kamNorm r (L.toLinear W) ≤ C * kamNorm s W := L.bounded
example (L : KamBoundedMap 1 0) : False := by linarith [L.pos_s]
example {r s : ℝ} (L : KamBoundedMap r s) (W : KamPhase) :
    kamNorm r (L.toLinear W) ≤ kamOpNorm L * kamNorm s W := kamOpNorm_apply_le L W
#print axioms audit_A_zero
#print axioms audit_exact
#print axioms audit_exact_schur
```

## Closeout and limits

F1 is closed for the repaired source operator-norm interface. F2's original excess-premise blocker is closed; the exact no-sign source result is demonstrated above. The new alleged sign erratum is rejected with formal refutation. The owner should correct the two false explanatory passages; a public exact no-sign wrapper is recommended for convenience, but its mathematical content is already recovered without additional assumptions.

No independent reviewer was spawned; the refutation pass reconstructed and machine-checked the disputed claim independently of the author's proof and handoff. No production repair was authorized or made. No new pinned-source defect or mathematical deviation was introduced. Earlier round-1 notes on unchanged Fourier/lattice/weight interfaces are carried without being reopened. Actual W4 use, frozen seals, whole dependency-graph closure, and a fresh page-image audit of P96-K remain outside this tight delta.
