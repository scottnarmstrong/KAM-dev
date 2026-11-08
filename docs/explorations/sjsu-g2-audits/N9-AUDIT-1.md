Audited commit: `7d67c84d5f2a8ba2ea9a8f9af5a2684485606b52`; actual HEAD (`git rev-parse HEAD`): `f9cf5e441f48f35871922b866b1fd405e8dc291c`; SHA256: `KAM/EffectiveStability/SJSU/Check/Eta.lean` = `fdd80b76378809d1055de40cc13ca6ba36d6e137294f0ce1bc8ce9f51bb80c20`; `KAM/EffectiveStability/SJSU/Confinement/Proof.lean` = `42170b7aee4d99809118fa8e227c53bbd0968fbac88eeecaca0e75b238b9c1c1`.

**Verdict: PASS WITH NOTES — N9 (C), audit 1.**

The exact D76 candidate type passes structural expression equality. Every intermediate premise
is supplied, the four rational budgets fit the literal rates, the time inequalities hold, and
all requested axiom checks return exactly `[propext, Classical.choice, Quot.sound]`. No in-scope
mathematical defect, excess premise or proof escape was found.

**N1 — generated-root integration remains outstanding.** The prescribed lint reports
`KAM.lean is out of date; run scripts/gen_root_imports.py`, naming
`KAMSJSU/EffectiveStability/SJSU/Check.lean`, `Confinement.lean`,
`Ledger/Br/Top0.lean`, `Top1.lean`, `Top2.lean` and `KAMSJSU.lean` (the abbreviated paths
share the same `KAMSJSU/EffectiveStability/SJSU/` prefix). These generated roots do not yet
reflect the module inventory. Suggested integration fix: the orchestrator regenerates them
with `scripts/gen_root_imports.py` when accepting the package, then runs the landing checks.
AGENTS rule 10 and this audit's write restriction exclude that repair here. This note does
not invalidate the direct module build or the ordinary theorem.

**Scope and provenance.** Followed `AUDIT-N9-launch.md`, `AUDIT-PKG-brief.md`, the N9 and N5b
briefs, WORKER-RULES, AGENTS, PLAN, DECISIONS (D74–D76), the N5b handoff's N9(C) section and the
route/gate/ApproxIntegral context. Applied the `lean-statement-audit` method to the actual
ordinary export. This is an audit of the two named files and their use of audited inputs;
it does not freeze or seal an anchor, or repeat the ledger/source/package audits.

The shared worktree is on the target's parent; both audit files already existed as untracked
files. Consequently `git diff 7d67c84d5 -- <files>` reports deletions, because that command
does not include untracked contents. Direct binary comparison against
`git show 7d67c84d5:<path>` returns **BYTE_EQUAL True for both files**. Their hashes above
were checked independently. No checkout, staging, commit or branch change was performed.
The pre-existing handoff modification and unrelated untracked files were preserved.

Only this report and files under `.drafts/g2/scratch/aud-n9/` were authored by this audit.
The wrapper ran every Lean/Lake command under its serial lock, nice 5, 6 GiB memory cap and
`LEAN_NUM_THREADS=2`. No ledger target, producer or clean build was launched. The one required
build reused the existing module build artifacts; this is not a fresh ledger kernel replay.

**Statement fidelity: PASS — EXPR-EQUAL.**

The source of authority is the verbatim `.drafts/g2/freeze/gen/v2/stmt.txt`, SHA256
`16424cdc10231b2fa589ca925de301272156b8ecaadfe5fcedd3cc943a75325f`, as required by the launch
and D76. `Proof.lean:111–130` retains both initial-coordinate vectors, the closed radius
`10⁻⁶` box, the exact Hamiltonian, the strict extension `T₁ > 5·10⁹`, existence on the open
interval, agreement with every solution on an order-connected set containing zero, and the
two-sided eccentricity bounds on the closed time window `|t| ≤ 5·10⁹` for all three indices.
The oscillator-action argument order and all three fixed action normalizers are unchanged.

Expanded binder inventory (there are no project-owned assumption aliases in this type):

| Binder | Classification | Exact source correspondence |
|---|---|---|
| `z₀ : (Fin 3 → ℝ) × (Fin 3 → ℝ)` | TYPING | `stmt.txt:1`, explicit Cartesian initial state |
| `hz₀` | SOURCE | `stmt.txt:2–3`, both coordinate inequalities, each with `≤ 1 / 10 ^ 6` |
| `j : Fin 3` inside `hz₀` | TYPING | `stmt.txt:2–3`, universal component index for both inequalities |

Outer binder counts: SOURCE 1, STANDING 0, TYPING 1, RULED 0, EXCESS 0.
Including the nested component binder: SOURCE 1, STANDING 0, TYPING 2, RULED 0, EXCESS 0.
The two conjuncts of `hz₀` are exactly the two source premises; neither assumes dynamics,
rates, certificates, positivity or confinement. Existential trajectory/time variables and
the variables in the uniqueness clause remain inside the conclusion in the same scope.

The independent stdin probe copies the verbatim declaration, changing only `theorem` and
its name to `def auditVerbatimV2`, and supplies the actual export as its body. It compares
the two `ConstantInfo.type` expressions with `==`, without `isDefEq`, reduction, rewriting
or normalization:

```lean
open Lean Elab Command in
run_elab do
  let source ← getConstInfo `auditVerbatimV2
  let actual ← getConstInfo ``sjsu_secular_confinement_proof
  unless source.type == actual.type do
    throwError "EXPR-DIFFERENT"
  logInfo "EXPR-EQUAL"
```

Result: `EXPR-EQUAL: verbatim v2 proposition == theorem type (Expr ==, no defeq)`.
The final probe also checks an independently formed proposition and three fully supplied
applications of `_of_rate`, `_of_N7` and `_of_obs` at that proposition.

**Premise discharge and consumption: PASS.**

| Consumer/location | Supplied premises |
|---|---|
| `_proof`, `Proof.lean:130` | `η := sjsuEta`; actual theorems `sjsu_hη`, `sjsu_hTη`; only `z₀`, `hz₀` remain |
| `_of_rate`, `Proof.lean:104–105` | `f := sjsuObs`, `ct := sjsuObsCt`, `ε := sjsuObsEps`; `sjsu_hfper`, `sjsu_hfd`, `sjsu_hface`, `sjsu_hερ`, `sjsu_hFu`, `sjsu_hFφ`; the rate/time facts passed above |
| `_of_N7`, `Proof.lean:76–77` | `h := sjsuHTilde sjsuB`; `sjsu18O2_chart` on `actionPos 3`, joint differentiability `sjsu_hhd`, and the already supplied observable/rate/face/partial facts |
| `_of_obs`, `Confinement/Statement.lean:120–166` (audited input) | Receives these exact premises; its existing proof supplies the ball, centering, face-separation and other assembly checks |

The two distinctly named conditional helpers retain their intermediate contracts; the final
theorem assumes none of those contracts. `sjsu_hhd` (`Proof.lean:35–42`) proves positivity of
every `B_j(φ) + u_j` from `sjsuB_bounds`, `sjsu_rho_lt_bmin` and the negative side of `|u_j| ≤ ρ`.
It then applies joint `differentiableAt_hTildeOf`; slice differentiability is not substituted.
The final stdin applications compile, confirming consumer applicability beyond name matching.

**η and four-budget accounting: PASS.**

`Eta.lean:173` defines `sjsuRateQ = ![6/10^19, 23/10^19, 22/10^19]` in `ℚ`;
`Eta.lean:190` casts it to the real function `sjsuEta`. `Initial/Data.lean:29–31` instead defines
`sjsuEtaQ` as the three negative initial η coordinates, beginning
`-9080669615926963 / 1000000000000000000`. The two names have different definitions and roles;
the rate proof uses `sjsuRateQ`, never the initial-coordinate literal. This is the documented
naming deviation, not a changed rate or initial point.

The application at `Eta.lean:142–168` uses:

- **KEPT:** `sjsu_G_bound j` for the same `Ftab j`, `sjsuMons`, Fourier models and monomial map,
  summed over total degree at most 8. `sjsu_kept_cast` identifies the real finite sum with the
  triple-range rational sum without changing its domain or weights.
- **DROP:** `sjsu_drop_bound j hu' φ` on that same radius `2/1000000`, bounding the terms with
  degree strictly greater than 8, with the same models and list. Its literal is cast once.
- **ERR:** all Hamiltonian Taylor coefficients through degree 9, each once.
  `monOf_injective`, `sjsuMons_nodup`, `_mem`, `_cov` establish the full enumeration.
  `sjsu_hcert` uses `sjsu_hIdx_ne` to supply the nonempty-index premise of `sjsu_hcerts` for
  every monomial; no empty/default case is left assumed. `sjsu_hbr` identifies the true Horner
  coefficient with `hCoef` using the audited `sjsuHD_Ht_eq_hCoef`. The rational ERR includes
  both `a.castSucc` and action-2 derivatives, with the correct lowered exponents and errors.
- **TAIL:** `sjsu_hRem_bounds` supplies both the action and angular remainder partial bounds
  for the degree-9 Taylor remainder. Positivity `hpu` is proved on the entire closed box.
  The audited `reducedBracket_hTilde_bound` supplies the joint remainder differentiability
  required by its bound, from `differentiable_sjsuB`, `sjsuB_pos` and `hpu`.

`Fd_a = FuMax_(a.castSucc) + FuMax_2` bounds the absolute derivative difference by `abs_sub`
and the two N8 partial bounds; `Fp_a = FphiMax_a` uses the matching angular partial.
Thus TAIL is `Σ_a [Fd_a Rp + Fp_a (Ru_(a.castSucc) + Ru_2)]`, and ERR uses precisely these
same ceilings. `sjsu_err_cast` and `sjsu_tail_cast` preserve every summand.
There is no omitted term or conflation of the degree-8 bracket cutoff with degree-9 H data.

Independent exact-rational evaluation gives these ceilings in units of `10⁻²²`:

| `j` | KEPT | DROP | ERR | TAIL | ceiling of actual sum | η |
|---|---:|---:|---:|---:|---:|---:|
| 0 | 1718 | 168 | 1 | 3960 | 5846 | 6000 |
| 1 | 17565 | 226 | 1 | 4339 | 22129 | 23000 |
| 2 | 17188 | 339 | 1 | 3441 | 20968 | 22000 |

Each column is rounded upward independently; the total column is not the sum of rounded
components. The inequalities themselves are proved by `sjsuRate_ok0..2` using
`decide +kernel`, combined by `sjsuRate_ok`, and transferred by `Rat.cast_le` in `sjsu_hη`.
The evaluation is a cross-check, not a replacement for those proofs.

At `T = 5·10⁹`, the exact products `T·η_j` are respectively
`3·10⁻⁹`, `1.15·10⁻⁸`, `1.1·10⁻⁸`, all strictly below `δ/2 = 5·10⁻⁷`.
`sjsu_hTη` proves the rational inequalities by finite cases and `norm_num`, then transfers
them to `ℝ` using `Rat.cast_lt`. The probe independently verifies the rate vector and these
three product values by `norm_num`.

**Hygiene and checks.** Both files have the copyright header, `module`, public imports,
module docstring and `@[expose] public section`. Definitions required to unfold are exposed.
The ambient coordinates are `Fin n → ℝ`. A code-masked scan found no `sorry`, `admit`, `axiom`,
`unsafe`, `opaque`, `native_decide`, `ofReduceBool`, `set_option` or `EuclideanSpace`.

| File | Lines | Maximum line length |
|---|---:|---:|
| `Check/Eta.lean` | 208 | 100 |
| `Confinement/Proof.lean` | 135 | 99 |

Exact command receipts, all foreground and awaited:

1. `.drafts/g2/g2lake build KAM.EffectiveStability.SJSU.Confinement.Proof`:
   exit 0, `Build completed successfully (13866 jobs).` Only dependency warnings were
   replayed; no audited module or ledger was rebuilt. Full output: scratch `build.out`.
2. `.drafts/g2/g2lake env lean --stdin < .drafts/g2/scratch/aud-n9/Probe.lean`:
   final exit 0, `EXPR-EQUAL`, all consumer applications accepted, numeric output above.
   Full final output: scratch `probe.out`. The deliberate verbatim `def` and independent
   quantified proposition generate only probe-local style warnings; no options suppress them.
3. `#print axioms` for `sjsu_secular_confinement_proof`, `sjsu_hη`, `sjsu_hTη`, `sjsu_rate_le`
   and additionally `sjsuRate_ok0`, `sjsuRate_ok1`, `sjsuRate_ok2`:
   **each exactly `[propext, Classical.choice, Quot.sound]`**.
4. `PYTHONDONTWRITEBYTECODE=1 TMPDIR="$PWD/.drafts/g2/scratch/aud-n9"
   .drafts/g2/lint_noabi.sh`: completed, exit 1. The repository diagnostic is N1 above;
   neither audited file has a width, size, module-format or forbidden-pattern diagnostic.
   Output includes `check_lean_modules: PASS (23129 Lean files, 0 comparator configurations)`,
   the 8 root-generation tests passing, and `FROZEN-ANCHOR GUARD OK`. The 29 anchor-fixture
   tests initially fail at setup because this audit placed temporary fixtures inside the
   checkout; their explicit guard requires fixtures outside it. Full output: `lint.out`.
   `abi_hashes` was intentionally skipped as expressly required by WORKER-RULES; no full
   `scripts/lint_sources.sh` was substituted.
5. Corrective component rerun:
   `env -u TMPDIR python3 -I -B scripts/test_frozen_anchors.py`: exit 0,
   `Ran 29 tests in 4.415s`, `OK` (`fixture-tests.out`). The suite's normal temporary fixtures
   are automatically removed. This resolves the audit-induced setup failure; it does not
   turn the earlier full lint invocation green. The full lint was not repeated.

Probe-development record: the first run omitted the parent namespace for `sjsu18O2` and
the meta import needed for rational evaluation; a subsequent run compared a newly encoded
`∀` proposition body with a declaration type and did not pass raw expression equality.
Neither failed probe established statement equality. The final run elaborates the verbatim
declaration with its original binder form and compares declaration types directly, as the
launch requires. The successful proposition applications provide a separate semantic check.
Earlier outputs are retained as `probe-initial.out` and `probe-forall-encoding.out`.

**Uncertainties, errata and deviations.** No suspected in-scope source erratum or mathematical
deviation found. The rate-name deviation and reflow are documented above; literal structural
equality validates the reflow. Inherited analytic and data inputs retain the scope of their
earlier audits; this report checks their application and the resulting ordinary theorem,
not a new independent source/data audit or a frozen-anchor seal. The non-green full lint,
its corrected fixture component, and the generated-root integration requirement are recorded
above. No heartbeat, recursion or synthesis overrides were used or needed by the N9 checks.

Final integrity recheck: both audited files retain the opening SHA256 values and remain
byte-identical to `7d67c84d5`; the target is the ordinary theorem at these bytes. The report
and retained probes/receipts are the only audit deliverables. Nothing was staged or committed.

READY g2-audit-n9-1
