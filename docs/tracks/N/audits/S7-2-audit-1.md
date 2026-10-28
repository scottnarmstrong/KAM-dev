# Independent S7-2 audit 1

Overall verdict: **PASS WITH NOTES** for S7-2. Both result nodes are proved with the exact design v2 signatures. No blocking mathematical, statement-fidelity, or hygiene finding was found. This is an infrastructure package with **no frozen theorem anchor and no provider export**; “seal-ready” is therefore inapplicable, and this audit does not close any I/N/P headline theorem.

## Scope and authority

Audited only `KAM/Nekhoroshev/Stability/Gradient.lean`, as required by the handoff's AUDIT FOCUS. Read the package audit brief, repository rules, PLAN, DECISIONS, N track statement, design v2 B.3 and S7-2 proof plan, both design audits, and blueprint-N p7 L44–65. Inspected imported definitions and relevant coefficient/Cauchy/representation interfaces for their actual meanings. No other package's proofs are certified here.

The user's explicit output path overrides the generic brief's main-worktree destination. The only retained auditor change is this report. No production Lean, frozen file, manifest, generated file, or git state was modified. Temporary probes were placed under this worktree's `.lake/abi-scratch/` and removed after validation. All auditor Lean operations were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`; the targeted build used the specified compile gate.

Snapshot (2026-10-28):

| Item | Revision / SHA-256 |
|---|---|
| Package HEAD | `4c2ce1a34db3a33adc23ea12af23b8189fe3e754` |
| `inp` at intake | `88983f74ff9952994d1de31d0ed671307437b563` |
| Merge base | `00cf49c93cbcea2fd371edf0865258fadd64a43d` |
| `Gradient.lean` | `6481a5f3a636c947beae0d479679170b8853c628b7a9aedeef2bc96ed696bbe7` |
| Design v2 | `9376271a6f311a2fa9bdf530680433ae2b759a84747a05aa1aa8ad07d2e53be2` |
| p7 blueprint | `f3d6e993abd74759469db1c9ae3c2c6d7cc65555a6d13167e8bfc7c38493e4bd` |

`git diff inp...HEAD` contains exactly one added file, `Gradient.lean` (200 lines). The pre-existing untracked `S7-2-handoff.md` was preserved.

## Declaration ledger

Names below are in `KAM.Stability`; line numbers refer to `Gradient.lean`.

| Node / role | Declaration | Verdict | Reason |
|---|---|---|---|
| Private real-domain bridge | `realInclusion_mem_polyNbhd` L26 | PASS | Carries the actual real-neighbourhood witness through the isometric real inclusion. |
| Private restriction | `inClass_mono'` L31 | PASS | Restricts differentiability and periodicity by domain inclusion. |
| Private pointwise Fourier estimate | `norm_le_wsum` L38 | PASS | Uses genuine `HasSum` representation and summable weighted majorant at the same action. |
| Private Euclidean comparison | `euclid_le_sum_norm` L48 | PASS | Square-root of sum of coordinate norm squares is bounded by the sum of norms, including n=0. |
| `bpN:p7:theta-derivative` | `theta_derivative` L60 | PASS | Exact B.3 signature; sum, Euclidean, and value estimates retained, with bound `M/(exp 1*s)`. |
| `bpN:p7:resonant-gradient` object | `resSpan` L102 | PASS | Exact B.3 definition of real linear span of the cast integer modes. |
| Private derivative bridge | `thetaGradR_realH` L106 | PASS | Chain rule through real inclusion, scalar restriction, and `Complex.reCLM`; holomorphy on an open domain guards `fderiv`. |
| Private Fourier annihilator argument | `sum_dtheta_eq_zero` L124 | PASS | Summable derivative expansions at width s/2; every Fourier term vanishes by orthogonality or off-support vanishing. |
| `bpN:p7:resonant-gradient` | `resonant_gradient` L166 | PASS WITH NOTES | Exact B.3 signature and full span-membership conclusion; unused source reality premise is harmless (N1). |

## Statement fidelity and proof review

Mechanical comparison against `docs/tracks/N/design/PART67-LEAN-DESIGN.md` L987–1005 gives **verbatim equality of both theorem signatures and the `resSpan` definition**. Independent elaboration of fresh declarations copied from these design signatures, with bodies `by exact theta_derivative hs hu hb` and `by exact resonant_gradient hs hg hgr hb hΛ`, succeeds. No frozen-provider type probe or seal-body probe applies because this package has neither a frozen theorem nor a provider.

The blueprint's finite weighted norm is represented by the standing `WBound` predicate: summability and an upper bound at every complex action. This is source size data, not a derivative or gradient conclusion assumed in disguise. It permits the blueprint's sharp norm as well as any larger bound. Geometric strip width and period-one characters preserve the constant 1/(es): the derivative factor 2π is already paired with the weight exp(2πs|k|₁) in `cauchy_theta`. No dimension factor is introduced. Statements allow arbitrary n and arbitrary real action radius; this strengthens the positive-radius/n≥1 source convention without invalidating the proof (empty domains are vacuous).

For `theta_derivative`, L73 obtains the sum of the derivative weighted sums **at a fixed action**, before taking the bound by M. L81 uses each derivative's summability and Fourier representation at positive width s′, so no divergent-series fallback is used. L88–98 takes the right-hand limit s′↓0 of the numerical upper bound; it never evaluates a representation theorem at width zero. The denominator is nonzero since s>0. The Euclidean comparison and the complex-domain value estimate complete every blueprint conclusion.

For `resonant_gradient`, L110–120 identifies the genuine real gradient with the real parts of the complex partials. L130–164 obtains absolutely summable derivative expansions at s/2, takes only a finite sum over coordinates, and shows each Fourier term is zero. The on-support case uses the actual dot product with the integer mode; the off-support case uses the supplied coefficient-support condition. Finally L173–196 separates a hypothetical vector outside the finite-dimensional real span by a linear functional, writes that functional in coordinates, and contradicts the vanishing directional derivative. This is the planned annihilator argument and requires no auxiliary projection or unproved orthogonal-complement premise.

## Definition classification

The sole new definition is `resSpan` L102–103: a genuine `Submodule.span ℝ` of the image of Λ under coordinatewise integer-to-real coercion. It is correct for every Λ and n, including the empty set and zero-dimensional carrier. It has no choice-dependent substitute, domain fallback, or hidden proof field; its body is exposed by the public exposed section. There are no new structures, abbreviations, or instances.

Imported `realH` is the total real part of the complex function at real inclusion, as explicitly authorized in design §0 decision 6 (L50–54), rather than the blueprint's zero extension off Wᵣ. Every derivative in this package is evaluated inside the open real domain, where the extensions agree for real-on-real inputs. Imported `wsum` is only used with summability proved by `WBound` or `cauchy_theta`. Neither totality convention weakens a result.

## Hygiene and independent validation

Commands were run from `/root/code/KAM-inp-s72` unless an absolute path is shown.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-s72 KAM.Nekhoroshev.Stability.Gradient
```

Exit **0**. Output:

```text
[inp-gate] slot 1 acquired 06:41:04 for KAM.Nekhoroshev.Stability.Gradient
⚠ [3185/3185] Replayed KAM.Nekhoroshev.Stability.Gradient
warning: KAM/Nekhoroshev/Stability/Gradient.lean:168:5: Variable name `hgr` is not explicitly referenced.
Build completed successfully (3185 jobs).
```

The build reused the worktree snapshot; no clean, dependency-cache fetch, or library rebuild was requested. The warning additionally suggests renaming the unused binder; no linter suppression was introduced.

2. Signature and axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S72Audit.lean
```

Exit **0**, with exact output:

```text
'KAM.Stability.theta_derivative' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.resonant_gradient' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are all new public theorems. The probe also checks the exact defining equality for `resSpan` by `rfl`, alongside the fresh design-signature declarations described above. The transitive axiom checks exclude hidden `sorryAx` in their private proof dependencies.

3. Kernel replay (single invocation; this package has one lemma module and no provider):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Stability.Gradient
```

Exit **0**, exact output:

```text
replaying KAM.Nekhoroshev.Stability.Gradient
```

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely for the explicitly permitted stale generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (427 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No root regeneration was performed. The module has **200 total lines and zero lines over 100 Unicode characters**. Module header, copyright, public imports, module docstring, public section and exposed definition are present. No forbidden proof escapes, resource overrides, or `EuclideanSpace` occur in the new code.

5. Read-only diff checks:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
```

Both exit **0** with empty output. A local transitive-import traversal found 53 KAM modules: **no provider imports, no frozen theorem imports, and 19 frozen definition modules, all manifest SEALED**. Thus no DRAFT_SORRY theorem enters this package, even transitively.

## Notes, uncertainties, and errata

**N1 (nonblocking): unused reality hypothesis.** `Gradient.lean` L168 keeps `hgr : RealOn ... g` exactly as prescribed. The proof establishes membership for the real part of any supported holomorphic function, so reality is unnecessary for that conclusion. This is a mathematically stronger proof behind the unchanged API, not an extra premise or a weakened theorem. Retaining the signature is appropriate; the unused-binder warning does not block acceptance.

**N2 (nonblocking): generated root pending.** The expected stale `KAM.lean` lint exception remains for the orchestrator's regeneration. Every other lint gate passed, including the 100-character limit.

No suspected source or blueprint defect was found within S7-2. The previously documented total-real-part extension is inherited from the design, not a new deviation. No new deviation was introduced. This audit compares the local proof against the pinned blueprint/design contracts; it does not claim a fresh PDF audit of Pöschel or certification of downstream package applications.
