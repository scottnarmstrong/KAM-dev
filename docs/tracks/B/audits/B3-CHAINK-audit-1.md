# B3-CHAINK audit 1 (refute-first, independent)

- Package: B3-CHAINK (track B, OD-B17 + OD-B18). The oscillator step/chain/checker/physical theorems are made
  generic over `CertCoeff K`; the new theorem is the disc physical variant `oscillatorChain_physical_disc`; there is a
  new `QSqrt2` one-step smoke.
- Branch `inp-b3chaink`, audited commit `ec8e9d5c0` (code commit `d76727daa`). Scope: `git diff inp-b3coef...HEAD`,
  merge base `bb1a23077`. B3-COEF itself was audited separately (B3-COEF-audit-1, PASS WITH NOTES).
- Inputs: the prover handoff `docs/tracks/B/audits/B3-CHAINK-handoff.md` and its AUDIT FOCUS; the brief
  `/root/code/KAM-inp-b1/.drafts/B/brief-B3-CHAINK.md`; OD-B18 in `/root/code/KAM-inp-b1/docs/tracks/B/OWNER-DECISIONS.md`.
- This package proves no frozen anchor and adds no provider, so brief item 1 (provider = frozen type) does not
  apply. The checks that matter are ℚ preservation, soundness over `K`, and fidelity to OD-B18.

## Verdict: **PASS WITH NOTES**

I found no blocking issue. The notes (N1–N5) cover one source-level rename, how the instances should be read, how
weak the smoke statements are, and stale docstrings. None of them changes the meaning of a production statement.

## 1. ℚ preservation (focus 1)

**Statements.** I wrote a script that pulls every public `theorem` header **verbatim from the `inp-b3coef` text** of
the 12 changed non-smoke modules (64 theorems), along with the old `variable`/`open` lines. It then emits each header
as `example <old header> := <name> <explicit args>`. The old types `CartPoly` and `OscStep` are kept. Each example is
proved only by applying the new generic theorem, with `K` left to unification, so it can close only when the new
theorem at `K = ℚ` has the old type (abbrevs `OscStep := OscStepK ℚ`, `OscStepCert n := OscStepCertK ℚ n`,
`OscChainCert n := OscChainCertK ℚ n`).

```
LEAN_NUM_THREADS=1 systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 \
  lake env lean .lake/abi-scratch/QPres.lean        → no output, exit 0 (64/64)
```

The probe covers `oscillatorStep_confinement`, `oscillatorChain_confinement`, `checkOscStep_sound`,
`checkOscChain_sound`, `oscillatorStep_physical`, `oscillatorChain_physical` and every helper lemma. The pattern-matched
theorems (`oscChain_identity`, `norm_oscChainRem_le`, `oscDomOKB_sound`, …) are covered as well.

**Names.** I extracted all 95 old top-level `theorem/def/abbrev/structure/instance` names and ran `#check` on each
on HEAD. 94 exist. The one that does not is `OscStepCert.Bmaj`, now `OscStepCertK.Bmaj` (N1). Dot notation `c.Bmaj`
on `c : OscStepCert n` still elaborates (probe). No module in the `inp-b3chaink` tree spells the old name.

**`oscillatorChain_physical`.** Its signature differs from `inp-b3coef` only by `CartPoly → CartPolyK K` and
`List OscStep → List (OscStepK K)` (`diff` of the header). At ℚ it is the old statement (probe above). The old proof
body moved into `oscillatorChain_physical_core`. The wrapper rebuilds the deleted `hw₀a` argument as the `hchart`
discharge, which is the same `sq_le_sq'` + `linarith` computation.

**Downstream.** No Torus*/FT* file is touched by the diff. A gated build of the 12 leaves
(`OscillatorChainPhysicalDiscSmoke OscillatorQSqrt2Smoke OscillatorChain.Smoke OscillatorStep.Smoke
OscillatorPhysicalSmoke OscillatorChainPhysicalSmoke OscillatorChainCheck TorusChainPhysicalSmoke TorusPhysicalSmoke
TorusChainCheck TorusStep.Smoke TorusChain.Smoke`) through `inp_lake_build.sh` finished with
`Build completed successfully (3028 jobs)`, rc=0. It rebuilt 21 modules, including all 15 Torus dependents, and
printed no error lines.

## 2. Soundness over `K` (focus 2)

- `checkOscStep_sound` and `checkOscChain_sound`: their conclusions are textually the `inp-b3coef` ones with the
  types generalized, and at ℚ they are the old statements (§1). The checkers (`checkOscStep`, `checkOscChain`,
  `oscStepOKB`, `oscChainOKB`, `oscDomOKB`, `cartFitsB`) use only `[CertCoeff K]` data: exact ring operations,
  decidable equality and the ℚ majorant `absUB`. Radii, ε, δ and the bounds stay in ℚ.
- **A non-standard `Algebra K ℝ`?** The theorems take `[Algebra K ℝ] [Algebra K ℂ] [IsScalarTower K ℝ ℂ]
  [CertNormLe K ℝ] [CertNormLe K ℂ]`, and nothing ties `algebraMap K ℝ` to `CertCoeff.toReal`. That cannot make a
  theorem false. The checker certifies exact ring identities, which every ring hom preserves, and `absUB` bounds,
  which `CertNormLe` transports to whatever embedding is supplied. The conclusion is then a true statement about
  `cartEval H` *under the supplied embedding*. The real meaning of a certificate is therefore fixed by the instance in
  scope at the use site, not by the checker. For example, the Galois-conjugate embedding `a − b√2` also satisfies
  `CertNormLe` and would yield the conjugate Hamiltonian's theorem (N2).
- **Which instance the QSqrt2 smoke uses.** Probe on HEAD: `#synth Algebra QSqrt2 ℝ` gives `instAlgebraQSqrt2Real`
  and `#synth Algebra QSqrt2 ℂ` gives `instAlgebraQSqrt2Complex`. `#synth CertNormLe QSqrt2 ℝ/ℂ` gives
  `instCertNormLeQSqrt2Real/Complex`. Both of these hold by `rfl`:
  `(inferInstance : Algebra QSqrt2 ℝ) = instAlgebraQSqrt2Real` and
  `algebraMap QSqrt2 ℂ x = ((x.a : ℝ) + (x.b : ℝ) * √2 : ℝ)`. So the smoke uses the standard embedding
  `a + b√2` = `CertCoeff.toReal`. No competing instance is found.

## 3. `oscillatorChain_physical_disc` and `_core` (focus 3)

- **Premises vs OD-B18 / brief.** Relative to `oscillatorChain_physical`, the statement removes `hs1 : 2a' ≤ s²` and
  `hs3 : (s + tail)² ≤ a`. It adds `σ`, `hσ0 : 0 ≤ σ`, `hσ1 : a' ≤ σ²`, `hsσ : 2σ² ≤ s²` and
  `hs3' : (σ + tail)² ≤ a`. `s`, `hs0`, `hs2 : OscPhysDom n s l 0`, `d`, `hd`, `z₀` and `hz₀` are kept. That is
  exactly the brief's list. The binder order (`a' s d hs0 σ hσ0 hσ1 hsσ hs2 hs3' hd z₀ hz₀`) places the new binders
  where the old `hs1 … hs3` sat. No premise is conclusion-shaped.
- **Conclusion.** A `diff` of the conclusion text of `oscillatorChain_physical` against `oscillatorChain_physical_disc`
  is empty (`CONCL_SAME`).
- **`oscillatorChain_physical_core`.** Its premises are those of the physical theorem minus `hs3`, plus
  `hchart : ∀ w, (∀ i, |w.1 i − z₀.1 i| ≤ tail ∧ |w.2 i − z₀.2 i| ≤ tail) → ∀ j, action w j ≤ a j`. This is a genuine
  geometric premise: an action bound on the coordinate `tail`-box around the given `z₀`. It is neither a conclusion of
  the physical theorem nor a hard proof step. It is used once (`hw₀a := hchart w₀ hdisp0`, with `hdisp0` from
  `oscChainInv_sub_le`). Both wrappers discharge it, from `hs3` (box) and from `hs3'` (disc). It has a distinct helper
  name and is not a source result (N4).
- **The disc wrapper.** It derives `hs1` as `2a' ≤ 2σ² ≤ s²` (`linarith`). `hA'` is `q² + p² ≤ 2a' ≤ 2σ²`, from the
  definition `oscillatorAction = (q² + p²)/2`. `discPlane_sq_le` then gives `(q+dq)² + (p+dp)² ≤ 2(σ+e)²`, so the
  action is at most `(σ+e)² ≤ a`. `e ≥ 0` comes from `oscTail_nonneg_of hok.stepsOK`.
- **`discPlane_sq_le`.** This is the correct Cauchy–Schwarz argument: `dq² + dp² ≤ 2e²`,
  `(q dq + p dp)² ≤ (q²+p²)(dq²+dp²) ≤ (2σe)²`, so `q dq + p dp ≤ 2σe` and
  `(q+dq)² + (p+dp)² ≤ 2σ² + 4σe + 2e²`. The hypotheses `0 ≤ σ` and `0 ≤ e` are needed; without them the statement is
  false (e.g. σ < 0). It uses no `sqrt`.
- The proof idea matches OD-B18. The plane displacement is at most `√2·tail` and the start radius at most `√2σ`, so
  the action is at most `(σ+tail)²`.

## 4. Smokes (focus 4)

- `hhStepCert_check : checkOscStep hhStepCert = true := by decide +kernel`. No `native_decide` anywhere in the diff
  (grep over added lines).
- **The intended H.** I proved this probe on HEAD:
  `cartEval hhStepCert.H z = I₀(z) − (√2/2)·I₁(z) + (1/1000)(q₀²q₁ − q₁³/3)` over ℝ, by `simp only […]`, `hhQuadSmoke_eval`,
  `algebraMap_qsqrt2_real`, `cartEval_qVar` and `ring`. This is the HH-shaped polynomial the handoff describes.
  `Nact = q₀ − (√2/2)q₁` and `P = (1/1000)·hhCubicSmoke`, which is consistent with the identity `H = Nact∘I + P` that
  the kernel check verifies at `L = 1`, `χ = 0`.
- `discSmoke_numbers`: `1/12500 + tail ≤ 1/12500 + 74·10⁻⁹ = 80.074·10⁻⁶ ≤ 81·10⁻⁶`, then squared. This is correct
  and matches the brief's literal numbers. `hσ1` at `a' = σ²` is `le_rfl`.
- `discSmoke_zeroDrift` applies `oscillatorChain_physical_disc` to two zero generators on the harmonic oscillator.
- The four old ℚ smokes are textually unchanged (`git diff --stat` lists only the two new smoke files) and rebuilt.

## Table

| Item | Lean declaration | Verdict | Note |
|---|---|---|---|
| step structure | `OscStepK K` / `abbrev OscStep := OscStepK ℚ` | PASS | gen/out in `CartPolyK K`; ρ δ ε order unchanged |
| certificates | `OscStepCertK`, `OscChainCertK` + ℚ abbrevs | PASS | `OscStepCert.Bmaj` → `OscStepCertK.Bmaj` (N1) |
| one-step soundness | `oscillatorStep_confinement` | PASS | at ℚ = old (probe) |
| chain soundness | `oscillatorChain_confinement` | PASS | at ℚ = old |
| checkers | `checkOscStep_sound`, `checkOscChain_sound` | PASS WITH NOTE | conclusions verbatim; meaning fixed by the use-site embedding (N2) |
| physical step | `oscillatorStep_physical` | PASS | at ℚ = old |
| physical chain | `oscillatorChain_physical` | PASS | statement unchanged up to the K types; wrapper over `_core` |
| shared tail | `oscillatorChain_physical_core` | PASS | helper; `hchart` a genuine premise, discharged by both wrappers |
| OD-B18 | `oscillatorChain_physical_disc` | PASS | premises exactly per OD-B18/brief; conclusion identical |
| plane lemma | `discPlane_sq_le` | PASS | correct; nonnegativity hypotheses needed |
| QSqrt2 smoke | `hhStepCert_check`, `hhStepCert_drift` | PASS WITH NOTE | `decide +kernel`; drift statement weak (N3) |
| disc smokes | `discSmoke_numbers`, `discSmoke_zeroDrift` | PASS WITH NOTE | weak statements by design (N3) |
| other 60 helpers | all `theorem`s in the 12 changed modules | PASS | at ℚ = old (probe) |

## Definition classification

These definitions are new or changed in their types only. All are total, with no junk value that any theorem relies on.

- **Pure data/Bool** (`[CertCoeff K]` only): `OscStepK`, `OscStepCertK`, `OscChainCertK`, `oscTail`, `oscChainBound`,
  `OscStepCertK.Bmaj`, `cartFitsB`, `checkOscStep`, `checkOscChain`, `oscStepOKB`, `oscChainOKB`, `oscDomOKB`. The
  bodies are unchanged apart from the types. The checkers read lists with `getD i 0` as before, and this is sound
  because the soundness theorems quantify over `Fin n`.
- **Prop predicates:** `OscStepOK`, `OscLieOK`, `OscChainOK`, `OscDomOK`, `OscPhysDom`. Their bodies are unchanged.
- **Semantic (ℂ/ℝ):** `stepChart`, `stepChartInv`, `stepRem`, `oscStepFlow`, `oscChainTheta`, `oscChainRem`,
  `oscChainDom`, `oscChainMap`, `oscChainInv`, `oscChartSteps`. The bodies are unchanged, and `cartEval` now goes
  through `Algebra K ℂ`. At ℚ this is Mathlib's `Algebra ℚ ℂ`.
- **New smoke data:** `hhStepCubic`, `hhStepNact` and `hhStepCert` are the intended objects (§4).

## Hygiene

- `#print axioms` on HEAD: `oscillatorStep_confinement`, `oscillatorChain_confinement`, `checkOscStep_sound`,
  `checkOscChain_sound`, `oscillatorStep_physical`, `oscillatorChain_physical`, `oscillatorChain_physical_core`,
  `oscillatorChain_physical_disc`, `discPlane_sq_le`, `discSmoke_numbers`, `discSmoke_zeroDrift`, `hhStepCert_check`,
  `hhStepCert_drift`, `oscStepOKB_sound` and `oscChainOKB_sound` all give `[propext, Classical.choice, Quot.sound]`.
  `cartFitsB_sound` gives `[propext, Quot.sound]`.
- Kernel replay, one module at a time (wrapped as above; `lake env leanchecker --verbose <M>`). Every module has exit
  0, at 9–18 s each: `OscillatorChain`, `OscillatorChain.{Basic,Domain,Drift,Remainder}`, `OscillatorChainCheck`,
  `OscillatorChainPhysical`, `OscillatorChainPhysicalDisc`, `OscillatorChainPhysicalDiscSmoke`, `OscillatorCheck`,
  `OscillatorPhysical`, `OscillatorQSqrt2Smoke`, `OscillatorStep`, `OscillatorStep.{Drift,Remainder}` (16/16).
- `sh scripts/lint_sources.sh`: the only failure is the expected
  `KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/EffectiveStability.lean)`. The new modules need
  root regeneration by the orchestrator. Also `check_lean_modules: PASS (4576 Lean files …)`, `Ran 25 tests … OK`,
  `FROZEN-ANCHOR GUARD OK` and `ABI HASHES OK (314 frozen declarations …)`.
- Added lines contain no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `set_option` (including heartbeats) or
  `native_decide` (grep over `git diff inp-b3coef...HEAD -- '*.lean'`). The largest changed file is
  `OscillatorChainPhysical.lean` at 307 lines, well under 1500.
- Each of the 3 new files has a copyright header, `module`, `public import`, a docstring and
  `@[expose] public noncomputable section`.
- `git diff inp-b3coef...HEAD -- KAM/Frozen manifest KAM.lean README.md KAM/Root lakefile.lean` is empty. No
  provider is imported.

## Notes

- **N1 (API rename).** `OscStepCert.Bmaj` no longer exists as a constant; it is now `OscStepCertK.Bmaj`. Dot notation
  is unaffected and no consumer in this tree uses the old full name. A future branch that spells
  `OscStepCert.Bmaj` explicitly would break. A one-line ℚ alias would close this if wanted.
- **N2 (embedding is a use-site parameter).** For `K ≠ ℚ` the real/complex meaning of a certified `H` is whatever
  `[Algebra K ℝ]`/`[Algebra K ℂ]` is in scope. The soundness theorems are true for every such instance satisfying
  `CertNormLe`, but they do not force `algebraMap = CertCoeff.toReal`. Downstream applications that cite a `QSqrt2`
  certificate as being about the `+√2` Hamiltonian should rely on the global instances
  (`instAlgebraQSqrt2Real/Complex`, both `rfl` to `toReal`/`toComplex`) or state `algebraMap_qsqrt2_real`
  explicitly. Introducing a second `Algebra QSqrt2 ℝ` instance anywhere would be a hazard.
- **N3 (smoke statements are weak).** `hhStepCert_drift` drops the flow, initial-value and uniqueness parts of
  `checkOscStep_sound`. Its stated `∃ z, …` is nearly content-free: with `a = 0`, `hw₀` forces `w₀ = 0`, and `χ = 0`.
  `discSmoke_zeroDrift` similarly keeps only `z 0 = z₀` and the drift bound. They still exercise the full theorems
  (the proofs call `checkOscStep_sound` and `oscillatorChain_physical_disc` with all premises discharged), which is
  their purpose. Do not cite them as content.
- **N4 (helper status).** `oscillatorChain_physical_core` is public. It is a legitimate conditional helper with a
  distinct name. It should not be recorded as a source node.
- **N5 (stale docstrings).** Several docstrings still say "rational" or "exact `ℚ`" where coefficients are now in `K`:
  the `OscillatorCheck` module docstring and `checkOscStep` ("evaluated in exact `ℚ`"), the `OscStepCertK` docstring
  ("all numbers are rational"), and `cartEval_realInclusion₂_im` ("any rational polynomial"). This is cosmetic.

## Suspected source / blueprint defects

None. I confirm the OD-B18 finding is a genuine structural limitation of the coordinate-box `oscillatorChain_physical`
(`hs1`, `hs3` force `a ≥ 2a'`), and the disc variant resolves it as specified. I introduced no deviations.

## Probes

The probe files `.lake/abi-scratch/{QPres,Probe2,Names}.lean` were run and then deleted. Copies are in the auditor's
scratchpad. The generator extracted old headers from `git show inp-b3coef:<file>`.

Auditor timestamp: 2026-11-03 10:18 UTC.
