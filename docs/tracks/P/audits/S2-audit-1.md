# S2 independent package audit 1

Audit date: 2026-10-28. **Overall verdict: PASS WITH NOTES**. Scope is only `KAM/Planetary/SecularBox/Covariance.lean`, as explicitly directed by `S2-handoff.md`. No implementation changes were made.

## Snapshot and authority

- Worktree: `/root/code/KAM-inp-p14-s2`; branch commit `2229cdeef9e4f7ced5f79562e446248915feb87c`.
- Comparison: `git diff inp...HEAD`, with `inp` at `e2088d57c609cc20f1033b70a41e064402222f53`. The full delta adds `Chart.lean` (143 lines, inherited S1) and `Covariance.lean` (124 lines). Only Covariance receives an audit verdict here. The pre-existing untracked `S2-handoff.md` was preserved.
- Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the handoff and its AUDIT FOCUS, track P statement (especially lines 566–604), P14 design S2 and node rows, both P14 design audits, blueprint `p14b-secular-box.tex:164–173`, the relevant frozen definitions, and the two D25 theorem anchors.
- The user's exact absolute report destination overrides the generic brief's main-worktree destination.
- Implementation SHA-256: `09708bd8dd777d71298b5cbdf809416f0645b7f56b50410782bbbd1900dfb5b8`.
- Current canonical signature file SHA-256: `24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`.
- Current P14 design SHA-256: `04c358878699851e0e45adcccbfd06048e2474b6cffe015821df5e072f36fca3`.
- Blueprint SHA-256: `f14536c948f27bc9ccb330b5df0b482846696aa7ea10283d42ee2569be2d0ae7`.

## Verdict and declaration ledger

**S2 covariance infrastructure: PASS.** Both public declarations match the canonical signature slices exactly, including binder order and, for the definition, the complete body. All four graph records assigned to Covariance are established. The package-level note concerns only the permitted stale generated root reported by lint; see the final receipts below.

| Anchor | Verdict | Scope limit |
|---|---|---|
| `planetary.d25.secularBoxSafety.v1` | PASS WITH NOTES for this S2 contribution | Manifest state remains `DRAFT_SORRY`; exact frozen body is still `by sorry`. S2 supplies no provider or seal. Headline remains FROZEN_UNPROVED. |
| `planetary.d25.secularBoxAtCitedMasses.v1` | PASS WITH NOTES for this S2 contribution | Same boundary: no theorem-closure or seal-readiness claim. |

Provider-to-anchor type/seal probes are N/A: there is no S2 provider export or frozen theorem assigned for sealing. Instead, a fresh theorem copies the canonical `sb_cov` telescope and uses exactly `by exact KAM.Planetary.sb_cov m w theta`, and a `type_of%` probe checks its whole type. No draft anchor is imported into the probe or production module.

All declaration names below are in `KAM.Planetary`. Line numbers refer to Covariance.

| Node / declaration | Lean implementation | Verdict | Reason / evidence |
|---|---|---|---|
| Rotation definition, source b165 | `secularRotation`, 38–41 | PASS | Literal canonical definition (signatures 377–380); correct `assemble I phi p q` order fixes both fast blocks and rotates `(xi,eta)` without a domain restriction. |
| `bpP:p14:sb-cov` | `sb_cov`, 101–120 | PASS | Canonical telescope (signatures 426–433) is byte-identical; Gamma/eccentricity-vector, Jacobian, position and momentum identities for arbitrary masses and all points/longitudes. |
| `stepP:p14:sb-cv-1` | internal: `sbCov_gamma`, `sbCov_ecc`, `sbCov_root`, `hax` | PASS | Squared-radius invariance by sin²+cos²; unchanged Lambda fixes root, axis, and the square-root coefficient rho. Rotation norm invariance also comes from `KAM.Kepler.planeLength_rot`. |
| `stepP:p14:sb-cv-2` | internal: `sbCov_orbitalUnit`, `sbCov_jac`; 85–99 | PASS | `c(F)=R(theta)c(F-theta)` has the correct shift sign. `planeDot_rot` gives scalar x invariance and therefore Jacobian invariance. |
| `stepP:p14:sb-cv-3` | internal: final two goals of `sb_cov`, 111–120 | PASS | Position follows by linearity; momentum also uses `rot_quarterTurn`. No division cancellation or nonzero-denominator premise is used. |
| private block helpers | `sbCov_fast_snd`, `sbCov_slow_fst`, `sbCov_slow_snd`, `sbCov_pair`, 43–61 | PASS | Exact component identities of `assemble`; no logical assumptions. |
| private linearity helpers | `sbCov_rot_smul`, `sbCov_rot_sub`, `sbCov_rot_add`, 63–70 | PASS | Coordinatewise ring identities for the literal rotation. |
| private Gamma helper | `sbCov_gamma`, 72–78 | PASS | Literal quadratic action invariance. |
| private eccentricity helper | `sbCov_ecc`, 80–83 | PASS | Same real sqrt argument on both sides, then rotation commutes with scalar multiplication. |
| private orbital-unit helper | `sbCov_orbitalUnit`, 85–89 | PASS | Existing `rot_ex` plus theta+(F-theta)=F. |
| private root helper | `sbCov_root`, 91–94 | PASS | Direct unfolding with unchanged Gamma and fast actions. |
| private Jacobian helper | `sbCov_jac`, 96–99 | PASS | Direct dot-product covariance. |

P14 design lines 220–223 explicitly classify `sb-cv-1..3` as internal obligations, rather than separate exported theorems. No node-named public export replaces a literal node conclusion. The blueprint also mentions unchanged k,a and scalar x, which are not separate conjuncts in the approved signature. They are proved internally or follow immediately by unfolding; independent scratch probes establish the k,a,x equalities from the public result and literal rotation, so no node is left unpaid.

Departure D3 (`P14-LEAN-DESIGN.md:326–327`) expressly strengthens the elliptic-only blueprint result to all w. This is sound for these equalities: rotation leaves every input to total division/sqrt unchanged. The theorem does not assert ellipticity, positivity, integrability, or physical Kepler meaning at singular inputs. No added premise or constant dependence is hidden in a structure or instance.

## Binder audit

Source locators: blueprint b25–30 (carriers/formulas), b164–168 (rotation covariance), P14 design D3, and canonical signatures 426–433. There are no project-owned assumption bundles or mathematical instance premises to expand.

| Binder / quantifier | Classification | Source / role |
|---|---|---|
| `m : Fin 2 → ℝ` | SOURCE | Arbitrary planet weights in b27–29; axis and momentum formulas. No mass positivity is needed for the algebraic result. |
| `w : Phase (2+2)` | SOURCE | b165 chart point, with ellipticity removed under D3. `Phase` expands to two `Fin (2+2) → ℝ` blocks. |
| `theta : ℝ` | SOURCE | b165 rotation angle in radians. |
| first `∀ i : Fin 2` | SOURCE, conclusion quantifier | b165–166: both planets' Gamma and eccentricity vector. |
| second `∀ i : Fin 2` | SOURCE, conclusion quantifier | b165–168: both planets' orbital quantities. |
| `∀ F : ℝ` | SOURCE, conclusion quantifier | b165–168: every eccentric longitude. |

Input counts: SOURCE 3, STANDING 0, TYPING 0, RULED 0, EXCESS 0. Conclusion quantifiers: SOURCE 3. D3 governs the removed domain premise, rather than introducing a RULED input. There are no implicit or instance binders in the declared telescope. `secularRotation` has only `theta,w`, the same source data. Private helpers take only scalar/vector/coordinate data, never a desired covariance result as a hypothesis.

## Definition classification

The only new definition is `secularRotation`; no new abbrev or structure exists. It is a literal, globally meaningful rotation of slow coordinates. `assemble I phi p q = (Fin.append phi q, Fin.append I p)` explains why the displayed rotated coordinate 1 is passed before coordinate 0: these arguments are eta and xi respectively. The first arguments retain Lambda and lambda. The function has no choice, branch, fallback, or proof-dependent junk values. Its exposed body agrees with the signature byte for byte and with the source rotation on the entire declared carrier.

- BODY_MATCH: OK
- PUBLIC_CARRIER: OK
- WELL_DEFINEDNESS: N/A_LITERAL
- CHARACTERIZATION: N/A_LITERAL
- CHOICE_INDEPENDENCE: N/A
- DEFINITION_VERDICT: PASS

## Verification receipts

All Lean/Lake/checker invocations in this audit were sequential, at niceness 5 or greater, with `LEAN_NUM_THREADS=1`. No clean, update, cache download, heartbeat/resource override, dependency edit, or state-changing git command was used.

### Targeted build

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s2 KAM.Planetary.SecularBox.Covariance
```

Exit 0, output:

```text
[inp-gate] slot 1 acquired 18:05:47 for KAM.Planetary.SecularBox.Covariance
Build completed successfully (9095 jobs).
```

This was the prescribed targeted build; it was not a clean rebuild. No warnings were emitted.

### Signature/body/semantic probes and axioms

Mechanical extraction compared signatures 377–380 to the entire definition and signatures 426–433 (excluding the `sorry` body) to the entire implemented theorem telescope:

```text
secularRotation literal bytes: True
sb_cov telescope literal bytes: True
file lines: 124 max line characters: 99
overlong lines: []
```

The untracked `.lake/abi-scratch/S2Audit.lean` imported only the target module, copied the canonical rotation under `expectedRotation`, and proved `expectedRotation = KAM.Planetary.secularRotation` by `rfl`. It copied the canonical theorem telescope under `KAM.Planetary.S2Audit.exactSignature` with body `by exact KAM.Planetary.sb_cov m w theta`, followed by:

```lean
example : type_of% @exactSignature := @KAM.Planetary.sb_cov
```

Additional probes proved unchanged fast angles, unchanged root k, unchanged axis a, and scalar x covariance, at all points. For x, the proof unfolded `longitudeJacobian` in `(sb_cov m w theta).2 i F |>.1` and used `linarith`; no extra mathematical premise was added. For k and a it used unchanged fast actions and the Gamma clause. Thus the additional source scalar clauses are available by actual terms.

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S2Audit.lean
```

Final exit 0; complete output:

```text
'KAM.Planetary.sb_cov' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.secularRotation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.S2Audit.exactSignature' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The first exploratory probe exited 1 because the auditor's unnecessary `congr 2; ext j` step reached a scalar goal (`No applicable extensionality theorem found for type ℝ`). Replacing it with an explicit fast-action equality and rewriting fixed the scratch proof; the final complete probe above passed without warnings. This was not a package failure.

### Kernel replay

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.Covariance
```

One invocation, exit 0. Complete output:

```text
replaying KAM.Planetary.SecularBox.Covariance
```

The target is the sole audited lemma module; there is no S2 provider module to add to this invocation.

### Lint and repository hygiene

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 solely for the explicitly permitted stale generated root. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (823 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module checker, frozen-anchor guard and ABI comparison all passed. The brief expressly permits leaving the generated root stale; it was not regenerated. No other lint failure was reported.

Independent static checks: 124 total lines; maximum line length 99 Unicode characters; no line exceeds 100. Copyright, `module`, public imports, module docstring, and `@[expose] public noncomputable section` are present. No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace`, `set_option`, or `_root_` occurs. All new declarations are under `KAM.Planetary`; a declaration search across KAM found exactly one declaration each named `secularRotation` and `sb_cov`, both in this file, and neither existed in `inp`.

A source-import traversal found 49 project modules including the target and 46 frozen definition modules, each registered `SEALED`; zero provider imports and zero frozen theorem imports. There is no dependence on S1's proof, a draft theorem, or a quarantined provider. The design's S1 prerequisite is unnecessary for these purely algebraic identities.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` produced no output, exit 0. `git diff --check inp...HEAD` produced no output, exit 0. The only persistent audit write is this report; temporary probes and check logs are deleted after capturing their contents here.

## Uncertainties, source defects, and deviations

No suspected source/blueprint defect, unauthorized deviation, missing S2 node, or implementation finding was identified. The source labels this calculation “Ours; direct calculation from the frozen definitions” (b168), so no external paper theorem is being silently assumed. D3 is an existing documented strengthening, independently checked here. This verdict does not audit inherited S1, downstream averaging/flow proofs, or either D25 headline theorem.
