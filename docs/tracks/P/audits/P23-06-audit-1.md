# P23-06 independent package audit 1

Overall verdict: **PASS WITH NOTES** for the explicitly assigned package scope. All nine public declarations pass statement/body and proof checks. No theorem anchor or provider belongs to this package; no frozen theorem is certified seal-ready by this report. Notes concern the permitted stale generated root and inconsistent design ownership prose below.

## Scope and pinned evidence

Audited only `KAM/Planetary/Averaging/OscillatorSetting.lean`, HEAD `dc53913117b4e52c657fbb011fe01bd6ee17ef4c`, against `inp` at `5847c76fbf9293181c8193218a7caf28ad3495d5`. `git diff inp...HEAD` adds this one file (69 physical lines). The handoff calls it 68 lines; this is an immaterial counting discrepancy. Module SHA256: `74b914362f45f15604666f33ccada4b7fe03e8e21ae1c46b7a596e9e63862b43`.

Read AGENTS.md, PLAN, DECISIONS, the shared package-audit brief and local handoff/AUDIT FOCUS. The user's exact worktree report path overrides the generic brief's main-worktree output instruction. Used the lean-statement-audit skill for semantic checks; this is infrastructure rather than a manifest-bound anchor audit.

Contract: `docs/tracks/P/design/P23-LEAN-DESIGN.md` revision 2, package row L270, coordinate/width decisions L25–26, Appendix A L628–657, and proof/package boundaries; design audits 1 and 2; `/root/code/KAM-inp/.drafts/design/P23Signatures.lean` L246–274, SHA256 `7d7dae4308ea9ec0ca763a2a21ce4b83280bdbb4b91d2c4f5e7567b71085e834`. The shared signature file is absent from this worktree, so the named shared copy was read directly. Source comparison: `blueprint-P/parts/p2-averaging.tex` L162–169 (`bpP:p2:s-osc#data`), inherited N norm/class definitions in `blueprint-N/parts/p4-weighted-norms.tex` L12–16, L47–53, and track P `statement.md` conventions. Existing `Averaging/Setting.lean`, `Weighted/Norm.lean`, frozen `ActionNbhd` and `ComplexStrip` bodies were inspected.

No frozen theorem participates in the target type. The two directly imported frozen definitions are manifest `SEALED`; the import closure contains no frozen theorem module or provider. Frozen-anchor guard and ABI checks pass below.

## Per-declaration results

All names below have namespace `KAM.Planetary`; all implement the data node `bpP:p2:s-osc#data`.

| Declaration / module line | Verdict | Reason |
|---|---|---|
| `oscPack`, 34 | PASS | Exact signature/body; sends `((θ,q),(I,p))` to `(θ,(I,p,q))`, with no coordinate scaling. |
| `oscUnpack`, 37 | PASS | Exact inverse coordinate concatenation in frozen phase order; no arbitrary/default branch. |
| `oscFunction`, 40 | PASS | Literal pullback `f ∘ oscUnpack`; only fast angles are Fourier variables. |
| `oscParams`, 43 | PASS | Frozen complex action neighbourhood and independent strict max-norm bounds for p and q; exact `(I,p,q)` order. |
| `oscDom`, 47 | PASS | Pullback of the geometric fast strip times the parameter domain; S is geometric. This helper is present in the signatures although omitted from the package-row name list. |
| `oscBound`, 49 | PASS | Uniform pointwise-in-parameter weighted bound with explicit summability, not a sum of parameter suprema. Existing weight is `exp(2π S |k|₁)`, consistent with geometric S. |
| `oscClass`, 53 | PASS | Complex differentiability on the intended domain and period-one translations only in fast θ coordinates; no periodicity imposed on oscillator q. |
| `oscGauge`, 58 | PASS | Exact four-block max, with θ/σ, I/ρ, q/ρq, p/ρp. |
| `s_osc_data`, 62 | PASS | Exact intended inverse identity; no proof premise. Product/function extensionality and finite block cases reduce each component to itself. |

The eight-definition block is whitespace-normalized identical to the shared signatures. Independent Lean probes also establish definitional equality for each full definition and exact theorem type, rather than relying on textual matching.

### Theorem binders and proof

| Binder | Bin | Evidence |
|---|---|---|
| implicit `n : ℕ` | TYPING | Fast dimension in design signature L274; block formulas are meaningful also at zero. |
| implicit `m : ℕ` | TYPING | Oscillator dimension in the same signature; no positivity needed for coordinate identity. |
| explicit `z : CPhase (n+m)` | TYPING | Arbitrary point in the exact signature carrier. |

Counts: SOURCE 0, STANDING 0, TYPING 3, RULED 0, EXCESS 0. No instance binders, hidden hypothesis bundle, constant/witness choice or conditional premise. The theorem is stronger than the positive-dimension source setting because it also covers zero-sized blocks; this is valid and matches the supplied signature.

`Prod.ext` and `funext` produce four coordinate cases via `Fin.addCases`; `Fin.append_left/right` and the block definitions close every case. No hard analytic assertion is assumed or proved here. The reverse identity on flat parameters is not part of this package's theorem contract.

### Definition classification

All eight new definitions are **literal formulas or source predicates**, not characterization-defined objects. No new abbrev, structure or instance. For each of `oscPack`, `oscUnpack`, `oscFunction`, `oscParams`, `oscDom`, `oscBound`, `oscClass`, `oscGauge`:

- BODY_MATCH: OK
- PUBLIC_CARRIER: OK
- WELL_DEFINEDNESS: N/A_LITERAL
- CHARACTERIZATION: N/A_LITERAL
- CHOICE_INDEPENDENCE: N/A
- DEFINITION_VERDICT: PASS

Packing/unpacking and pullback are total coordinate formulas on their whole carriers, including empty coordinate blocks. Domains use literal inequalities for all radii; empty domains outside the positive-radius setting are the corresponding set formula, not selected fallback objects. Gauge uses ordinary total real division; its interpretation as a scaled norm requires positive losses as in the blueprint. The identity theorem does not exploit zero-loss division. `oscBound` explicitly pairs `WSummable` with `wsum`, so the underlying nonsummable-tsum value cannot fake a finite norm. `oscClass` and `oscBound` name source class/norm predicates and do not bundle a desired theorem conclusion.

## Independent checks

All explicit Lean/Lake verification commands below use `LEAN_NUM_THREADS=1`, sequentially. No resource overrides, library reset, dependency mutation or root regeneration was performed.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2306 KAM.Planetary.Averaging.OscillatorSetting
```

Exit 0; output:

```text
[inp-gate] slot 2 acquired 07:33:06 for KAM.Planetary.Averaging.OscillatorSetting
Build completed successfully (9086 jobs).
```

The gate invokes `nice -n 5 lake build` and uses the worktree overlay. No warnings reported.

2. Exact signature/body and axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2306Audit.lean
```

Exit 0. The scratch file imports only the target module, copies the exact shared-signature definition block into namespace `P2306Audit`, and checks `example : @P2306Audit.<name> = @KAM.Planetary.<name> := rfl` for all eight definitions. Its copied exact theorem declaration has body `by exact KAM.Planetary.s_osc_data z`; it additionally checks `example : type_of% @P2306Audit.s_osc_data := @KAM.Planetary.s_osc_data`. This is the applicable exact-binder assembly check; frozen/provider checks themselves are N/A.

Full axiom output:

```text
'KAM.Planetary.oscPack' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscUnpack' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscFunction' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscParams' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscDom' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscClass' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscGauge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.s_osc_data' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorSetting
```

Exit 0; output:

```text
replaying KAM.Planetary.Averaging.OscillatorSetting
```

This single invocation covers the only new lemma module; there is no provider module.

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1 solely for the explicitly permitted stale generated root; all other checks pass. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (449 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

An earlier unprefixed `sh scripts/lint_sources.sh` invocation returned the same output and exit 1. The final run above was repeated with explicit thread restriction and niceness after kernel replay completed.

5. Static checks:

```sh
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Both exit 0 with empty output. Target has 69 physical lines, maximum line length 99, copyright/license/authors header, `module`, public imports, module docstring, exposed public section. No forbidden escape, sorry, override or `EuclideanSpace`. Traversal of project imports reaches 40 project modules, no provider and no frozen theorem module. Thus no imported DRAFT_SORRY theorem or provider quarantine violation.

## Notes, defects and limits

- Permitted generated-root staleness is the lint exception explicitly allowed by the brief. The root is left untouched.
- Minor design documentation inconsistency: `P23-LEAN-DESIGN.md` L288 says **“OscHyp is defined in P23-06, not the late finite-iteration module.”** The P23-06 row at L270 and the user's AUDIT FOCUS inventory do not assign `OscHyp`; the audited file does not define it. This does not affect any of the nine assigned exports or the inverse theorem, but the orchestrator should reconcile ownership before treating that prose as implemented. No implementation or design repair was made here.
- No suspected pinned-source mathematical erratum or blueprint contradiction was found in the audited definitions/identity. This is a blueprint/design/signature audit; no fresh CP10 PDF audit or downstream oscillator bracket/flow proof certification is claimed. Prior design-audit findings on `osc_iter` and private limit packages remain outside this package.
- No frozen, manifest, production, generated or pre-existing handoff file was edited. Only this report is delivered; the audit probe is removed after verification. No state-changing git command, commit or seal.
