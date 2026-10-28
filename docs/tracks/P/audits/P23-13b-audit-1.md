# P23-13b independent package audit 1

**Verdict: PASS WITH NOTES for the scoped infrastructure package.** All five signed public declarations pass statement/definition fidelity; the four theorem proofs implement the signed estimates without additional premises. No frozen anchor is sealed by this package. This report does not close `bpP:p2:osc-iter`, P23-13j, P23-15, or a planetary headline.

## Scope, authority and frozen-v1 snapshot

Audit date: 2026-10-28. Worktree: `/root/code/KAM-inp-p2313b`.
Read-only audit authorized by the user and `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, narrowed by the handoff's AUDIT FOCUS to `KAM/Planetary/Averaging/OscillatorSeriesAlgebra*.lean`. Only this report is a new repository deliverable. Temporary probes were confined to `.lake/abi-scratch/`. No production, frozen, manifest, generated-root or README changes were made by the auditor.

Frozen inputs:

| Input | Revision / SHA256 |
|---|---|
| HEAD | `387d44269912bc96b306e5616e2fff92c715e2a7` |
| `inp` at audit start | `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2` |
| `inp-design-p23r3` | `a20e538c5ef2b4a2f5adee25654132ed4ba6b97c` |
| Pre-package integration commit | `09821488356662e7f28252a5772f91d6a9665398` |
| `KAM/Planetary/Averaging/OscillatorSeriesAlgebra.lean` | `1a0d474eafd472557c862089de638eca034ce2c118a378c6bd795652f18007b2` |
| `docs/tracks/P/design/P23-LEAN-DESIGN.md` | `618497aa0c1d5114b76905ae2e3bc552c560a5d17f3136b505aec983bd2d5c6a` |
| `docs/tracks/P/design/P23-design-audit-1.md` | `1420eb016bb4ee39dd0efeca8f0b8fa91dc34b9a5f295c8f044bf72843bcc3ab` |
| `/root/code/KAM-inp/.drafts/design/P23Signatures.lean` | `d067d47dbabfdf4913da3e2b76886eb29598f4502ad16318d328568d82380cd3` |

The handoff's relative `.drafts/design/P23Signatures.lean` does not exist in this package worktree. The shared original at the absolute path above exists and matches the design's pinned hash. Appendix A.3 remains the in-worktree statement authority. Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, track P statement conventions, design Revision 3 and Appendix A.3, the design audit, and `blueprint-P/parts/p2-averaging.tex:183–196`.

## Comparison scope and inherited changes

Ran the requested `git diff inp...HEAD` and the handoff comparison `git diff inp-design-p23r3...HEAD`. Both include inherited integration work outside the focused package. Git reports:

```text
warning: inp...HEAD: multiple merge bases, using a20e538c5ef2b4a2f5adee25654132ed4ba6b97c
```

`git merge-base --all inp HEAD` returns `a20e538c5ef2b4a2f5adee25654132ed4ba6b97c` and `5991245cabc06e69ec900cb6006b45f72cc85eb0`.
The full selected three-dot diff has 81 changed files. Its protected-path check is **not empty**: `KAM.lean` has 34 added imports; frozen files, manifest and README have no changes. The same generated-root difference occurs against `inp-design-p23r3`. It is inherited: `git diff 0982148 HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty, and `git diff --stat 0982148 HEAD` contains only the new 335-line `OscillatorSeriesAlgebra.lean`. The package consists of commits `633e835` and `387d442`. Thus the brief's whole-branch protected-path condition fails literally for the inherited root, but there is no package-owned protected-file edit. This distinction is a note, not permission to certify the other 80 files or regenerate the root.

## Declaration ledger

All public names below are prefixed `KAM.Planetary`. Line locators refer to frozen-v1 above.

| Node / interface | Declaration | Verdict | Evidence |
|---|---|---|---|
| `stepP:p2:oi-transfer`, A.3:1395 | `oscTruncate`, implementation 36–37 | PASS | Entire definition matches the signed body byte for byte. Existing `Weighted.truncate` of `oscFunction f`, evaluated at `oscPack z`; no expansion of slow q variables. |
| `stepP:p2:oi-transfer`, A.3:1416 | `osc_bound_const_mul`, 126–141 | PASS | Exact signed header; coefficient scalar linearity, summability and bound scaled by `norm c`. No analyticity premise added. |
| `stepP:p2:oi-transfer`, A.3:1420 | `osc_bound_add`, 143–168 | PASS | Exact signed header, positive S and both class assumptions retained; coefficient triangle inequality gives A+B. |
| `stepP:p2:oi-transfer` / `oi-ratio`, A.3:1425 | `osc_bound_tsum`, 225–247 | PASS | Exact signed header; class, weighted bound and uniform weighted-tail conclusion all proved; no extra dimension/nonemptiness premises. |
| `stepP:p2:oi-transfer`, A.3:1436 | `osc_truncation_tail`, 250–330 | PASS | Exact signed header; class and bound at S, tail at S−σ with exactly `exp (-(2*pi*K*σ))*A`, including K=0. |

A Python comparison extracted each signed theorem command through `:= sorry` and compared its header, with whitespace normalized, against production through `:= by`. Output:

```text
osc_bound_const_mul: exact normalized signature MATCH
osc_bound_add: exact normalized signature MATCH
osc_bound_tsum: exact normalized signature MATCH
osc_truncation_tail: exact normalized signature MATCH
oscTruncate: full definition byte MATCH
```

A separate transient Lean probe copied these exact signed theorem commands under fresh names and supplied the corresponding production theorem with every explicit argument in order. All elaborated. A definitional-equation example for `oscTruncate` closed by `rfl`. This is infrastructure, so provider/frozen-type and seal-body probes are N/A: there is no provider or theorem anchor in scope.

## Binder audit and semantic closure

Bin meanings: SOURCE = explicit Appendix A.3 input; TYPING = dimension, carrier, function or scalar parameter. No STANDING, RULED or EXCESS binders. This is comparison with the approved generic helper interfaces, not a claim that class/bound inputs are premises of the final `osc_iter`.

The following table gives one row per elaborated outer binder; each row is justified by the corresponding verbatim Appendix A.3 command. Shared section variables are counted only when actually present in the exported type.

| Declaration | Binder | Bin | Source role |
|---|---|---|---|
| `osc_bound_const_mul` | `n` | TYPING | fast dimension |
| `osc_bound_const_mul` | `m` | TYPING | oscillator dimension |
| `osc_bound_const_mul` | `D` | TYPING | real action set |
| `osc_bound_const_mul` | `r` | TYPING | action width |
| `osc_bound_const_mul` | `rp` | TYPING | p width |
| `osc_bound_const_mul` | `rq` | TYPING | q width |
| `osc_bound_const_mul` | `S` | TYPING | angle width |
| `osc_bound_const_mul` | `A` | TYPING | input bound |
| `osc_bound_const_mul` | `c` | TYPING | complex scalar |
| `osc_bound_const_mul` | `u` | TYPING | Hamiltonian |
| `osc_bound_const_mul` | `hu` | SOURCE | weighted summability and bound |
| `osc_bound_add` | `n` | TYPING | fast dimension |
| `osc_bound_add` | `m` | TYPING | oscillator dimension |
| `osc_bound_add` | `D` | TYPING | real action set |
| `osc_bound_add` | `r` | TYPING | action width |
| `osc_bound_add` | `rp` | TYPING | p width |
| `osc_bound_add` | `rq` | TYPING | q width |
| `osc_bound_add` | `S` | TYPING | angle width |
| `osc_bound_add` | `A` | TYPING | first bound |
| `osc_bound_add` | `B` | TYPING | second bound |
| `osc_bound_add` | `hS` | SOURCE | 0 < S |
| `osc_bound_add` | `u` | TYPING | first Hamiltonian |
| `osc_bound_add` | `v` | TYPING | second Hamiltonian |
| `osc_bound_add` | `hu` | SOURCE | class of u |
| `osc_bound_add` | `hv` | SOURCE | class of v |
| `osc_bound_add` | `hA` | SOURCE | weighted summability and bound of u |
| `osc_bound_add` | `hB` | SOURCE | weighted summability and bound of v |
| `osc_bound_tsum` | `n` | TYPING | fast dimension |
| `osc_bound_tsum` | `m` | TYPING | oscillator dimension |
| `osc_bound_tsum` | `D` | TYPING | real action set |
| `osc_bound_tsum` | `r` | TYPING | action width |
| `osc_bound_tsum` | `rp` | TYPING | p width |
| `osc_bound_tsum` | `rq` | TYPING | q width |
| `osc_bound_tsum` | `S` | TYPING | angle width |
| `osc_bound_tsum` | `hS` | SOURCE | 0 < S |
| `osc_bound_tsum` | `v` | TYPING | sequence of Hamiltonians |
| `osc_bound_tsum` | `b` | TYPING | sequence of real majorants |
| `osc_bound_tsum` | `hv` | SOURCE | each term in class |
| `osc_bound_tsum` | `hb` | SOURCE | each term weighted-summable and bounded by b j |
| `osc_bound_tsum` | `hb0` | SOURCE | all b j nonnegative |
| `osc_bound_tsum` | `hs` | SOURCE | Summable b |
| `osc_truncation_tail` | `n` | TYPING | fast dimension |
| `osc_truncation_tail` | `m` | TYPING | oscillator dimension |
| `osc_truncation_tail` | `D` | TYPING | real action set |
| `osc_truncation_tail` | `r` | TYPING | action width |
| `osc_truncation_tail` | `rp` | TYPING | p width |
| `osc_truncation_tail` | `rq` | TYPING | q width |
| `osc_truncation_tail` | `S` | TYPING | angle width |
| `osc_truncation_tail` | `A` | TYPING | input bound |
| `osc_truncation_tail` | `σ` | TYPING | strip loss |
| `osc_truncation_tail` | `K` | TYPING | cutoff |
| `osc_truncation_tail` | `f` | TYPING | Hamiltonian |
| `osc_truncation_tail` | `hf` | SOURCE | class of f |
| `osc_truncation_tail` | `hA` | SOURCE | weighted summability and bound of f |
| `osc_truncation_tail` | `hσ` | SOURCE | 0 < σ |
| `osc_truncation_tail` | `hσS` | SOURCE | σ < S |
| `osc_truncation_tail` | `hK` | SOURCE | 0 ≤ K |

Outer-binder counts (SOURCE / STANDING / TYPING / RULED / EXCESS): scalar 1/0/10/0/0; addition 5/0/11/0/0; series 5/0/9/0/0; truncation 5/0/11/0/0. No instance or bundled output assumption is introduced. The binders of the new literal definition are `{n m : Nat}`, `(K : Real)`, `(f : CHam (n+m))`, all TYPING (4).

Expanded meanings were checked in `OscillatorSetting.lean:34–57`, `Setting.lean:40–55`, `Weighted/Norm.lean:42–64`, and the frozen `ActionNbhd`, `ComplexStrip`, `Phase`, `Fast`, `Slow` definitions. `CHam (n+m)` is a complex-valued function on the product of two `Fin (n+m) → Complex` spaces; packing is `(theta,(I,p,q))`, with parameter dimension `n+(m+m)`. `oscClass` means holomorphic on the open oscillator domain and period one in each fast angle. `oscBound` expands to **both** `WSummable` and `wsum ≤ A` at **every** flat parameter. `WSummable` is actual coefficient summability; the coefficient weight is `exp(2*pi*S*modeSize k)`. Frozen strip and action-neighbourhood bodies retain the strict sup-norm inequalities. No proposition alias hides an analytic estimate or existence conclusion.

The bundled SOURCE inputs expand as follows. Each row is a distinct logical constituent, with the universal parameter binder and domain guard shown explicitly. Here P is `oscParams D r rp rq`, O is `oscDom D r rp rq S`, F_u is `oscFunction u`, and w_k is `modeWeight S k`; these are notation for the literal definitions, not extra assumptions.

| Declaration | Expanded input | Bin | Exact authority |
|---|---|---|---|
| scalar | hu: forall x in P, Summable (fun k => norm (coeff F_u x k) * w_k) | SOURCE | A.3:1417; oscBound definition |
| scalar | hu: forall x in P, tsum (fun k => norm (coeff F_u x k) * w_k) <= A | SOURCE | A.3:1417; oscBound definition |
| addition | hS: 0 < S | SOURCE | A.3:1420 |
| addition | hu: DifferentiableOn Complex u O | SOURCE | A.3:1421; oscClass definition |
| addition | hu: forall j z, z in O implies u (fast-shift j z) = u z | SOURCE | A.3:1421; oscClass definition |
| addition | hv: DifferentiableOn Complex v O | SOURCE | A.3:1421; oscClass definition |
| addition | hv: forall j z, z in O implies v (fast-shift j z) = v z | SOURCE | A.3:1421; oscClass definition |
| addition | hA: forall x in P, weighted coefficients of F_u at x are summable | SOURCE | A.3:1422; oscBound definition |
| addition | hA: forall x in P, weighted coefficient sum of F_u at x <= A | SOURCE | A.3:1422; oscBound definition |
| addition | hB: forall x in P, weighted coefficients of F_v at x are summable | SOURCE | A.3:1422; oscBound definition |
| addition | hB: forall x in P, weighted coefficient sum of F_v at x <= B | SOURCE | A.3:1422; oscBound definition |
| series | hS: 0 < S | SOURCE | A.3:1425 |
| series | hv: forall j, DifferentiableOn Complex (v j) O | SOURCE | A.3:1426; oscClass definition |
| series | hv: forall j i z, z in O implies v j (fast-shift i z) = v j z | SOURCE | A.3:1426; oscClass definition |
| series | hb: forall j x, x in P implies weighted coefficients of F_(v j) at x are summable | SOURCE | A.3:1427; oscBound definition |
| series | hb: forall j x, x in P implies weighted coefficient sum of F_(v j) at x <= b j | SOURCE | A.3:1427; oscBound definition |
| series | hb0: forall j, 0 <= b j | SOURCE | A.3:1428 |
| series | hs: Summable b | SOURCE | A.3:1428 |
| truncation | hf: DifferentiableOn Complex f O | SOURCE | A.3:1437; oscClass definition |
| truncation | hf: forall j z, z in O implies f (fast-shift j z) = f z | SOURCE | A.3:1437; oscClass definition |
| truncation | hA: forall x in P, weighted coefficients of F_f at x are summable | SOURCE | A.3:1437; oscBound definition |
| truncation | hA: forall x in P, weighted coefficient sum of F_f at x <= A | SOURCE | A.3:1437; oscBound definition |
| truncation | hσ: 0 < σ | SOURCE | A.3:1438 |
| truncation | hσS: σ < S | SOURCE | A.3:1438 |
| truncation | hK: 0 <= K | SOURCE | A.3:1438 |

Expanded logical constituent counts are respectively 2, 9, 7 and 7, all SOURCE; STANDING=RULED=EXCESS=0. All subordinate j/i/k indices, points z/x and membership guards are TYPING data local to the displayed quantifiers. The scalar real/natural/complex carriers and Mathlib summability/holomorphy definitions introduce no project premise bundle. Neither norm bounds nor summability have been silently dropped.

## Definition classification

- `oscTruncate` (36–37): literal source formula, not a characterization-defined or chosen object. BODY_MATCH: OK; PUBLIC_CARRIER: OK; WELL_DEFINEDNESS: N/A_LITERAL; CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS. Its total function carrier and existing Fourier truncation are exactly the signed interface; no new conditional/default branch is introduced. Quantitative use is guarded by the signed class/summability and width assumptions.
- Private `cube'` (43): literal `Set.pi univ (fun _ => Icc 0 1)`, exactly the real unit Fourier cell, including zero dimension. BODY_MATCH: OK; PUBLIC_CARRIER: OK (private helper); WELL_DEFINEDNESS and CHARACTERIZATION: N/A_LITERAL; CHOICE_INDEPENDENCE: N/A; DEFINITION_VERDICT: PASS.
- No new structure or other definition/abbreviation. Local existential selection of a parameter ball comes from openness and is used only to prove local differentiability and bounds; it does not define an exported choice-dependent object.

## Proof review and refutation pass

Read every line of the scoped file, then revisited possible failure cases separately:

1. **Scalar coefficients and integration (48–69):** constant multiplication commutes with the total integral even without integrability. Addition explicitly obtains integrability from real-angle continuity and compactness of the unit cell. The public scalar lemma consequently needs no new class hypothesis; the public addition lemma retains both signed class premises and S>0.
2. **Coefficient interchange (71–103, 194–223):** continuity gives measurable integrands; the character has norm one on real angles; the finite restricted measure and summable `b` justify dominated convergence. For each mode, positivity of the weight gives summability of coefficient norms, so `norm_tsum_le_tsum_norm` is not applied to an arbitrary divergent total tsum. Finite sums of nonnegative weighted coefficients are bounded by `tsum b`; `wsummable_of_finset_le` establishes genuine summability before using the resulting sum inequality. No dimension equality is assumed: the private flat ports have independent dimensions n,N.
3. **Holomorphic sum and periodicity (179–192):** `oscBound.norm_le` supplies a uniform pointwise majorant on the entire original domain. The M-test and `uniform_limit_holomorphic` apply to finite holomorphic sums on that open domain. Periodicity is termwise at the shifted fast coordinate. A globally total tsum is used only on points where the majorant proves convergence.
4. **Tail quantifiers (237–247):** choose N from the scalar majorant tail before quantifying N' and before any flat parameter. Apply the same class/bound proof to the shifted family `v (j+N')`; domain summability identifies its sum with total minus initial segment. `oscBound.congr` transports equality on the domain, which suffices because coefficients read the real angle cell and S>0. This proves the signed uniform weighted tail, rather than only a pointwise or C0 tail.
5. **Truncation (257–330):** openness of `oscParams` gives a positive parameter ball at each point. `FClass.inClass` and `Weighted.projections` apply with parameter dimension `n+(m+m)` on that ball. Local differentiability is promoted at the center via the ball's open neighbourhood; fast shifts leave the flat parameter fixed. `oscPack_oscUnpack` proves the transported truncation identity. The same ball permits the existing `Weighted.truncation_tail` at S−σ. The constant remains exactly `exp(-2*pi*K*σ)*A`.
6. **Degenerate cases:** there is no hidden n>=1, m>=1, nonempty-D or positivity-of-A premise. Empty domains make the relevant universal assertions vacuous. K=0 remains allowed. Negative majorants on an empty domain do not invalidate the signed statements; the public series lemma keeps hb0 even though the implementation's auxiliary proof does not need it. At nonempty parameters the bound itself controls nonnegativity.

No mathematical or statement-fidelity objection survived this pass. The unused signed `hb0` is deliberately retained (`have _ := hb0`); this is not a new assumption. No repaired code or hypothesis was substituted.

The project import closure was traversed recursively: 71 project modules, 12 frozen definition modules, **zero provider imports, zero frozen theorem imports, zero DRAFT_SORRY markers**. Relevant imported mathematical interfaces were inspected at their actual types (`oscClass.flat`, `oscBound.norm_le`, `oscBound.congr`, `FClass.inClass`, `projections`, `truncation_tail`, `uniform_limit_holomorphic`). This is not a fresh source audit of all 71 dependencies; kernel replay and axiom closure check the formal dependency use.

## Verification (independent reruns)

All Lean/Lake operations in this audit are serialized and use `LEAN_NUM_THREADS=1` and `nice -n 5`. No heartbeat, recursion-depth or synthesis budget override was used; no clean/update/cache command was run.

1. Targeted compile gate:

```sh
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2313b KAM.Planetary.Averaging.OscillatorSeriesAlgebra
```

Exit 0; output:

```text
[inp-gate] slot 2 acquired 10:34:44 for KAM.Planetary.Averaging.OscillatorSeriesAlgebra
Build completed successfully (9117 jobs).
```

This is a targeted incremental build on the provided overlay, not a clean library rebuild.

2. Exact-signature/defining-equation probe and axiom check:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2313bAudit.lean
```

Exit 0, no warnings/errors. The probe contained the four Appendix A.3 theorem types under fresh names with bodies `exact KAM.Planetary.<name> <all explicit binders>`, the literal `oscTruncate` equation closed by `rfl`, `#check @<export>` and `#print axioms` commands. Output for all public declarations:

```text
'KAM.Planetary.osc_bound_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_bound_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_bound_tsum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.osc_truncation_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.oscTruncate' depends on axioms: [propext, Classical.choice, Quot.sound]
```

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Averaging.OscillatorSeriesAlgebra
```

Exit **0**. Complete output:

```text
replaying KAM.Planetary.Averaging.OscillatorSeriesAlgebra
```

4. Full source lint, run after kernel replay completes:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, exclusively the explicitly permitted generated-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (530 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The module-system, frozen guard and ABI checks pass. The generated root was not regenerated.

5. Scoped static hygiene: `wc -l KAM/Planetary/Averaging/OscillatorSeriesAlgebra.lean` reports **335** lines (below 1500; the handoff's 333 count is stale). The file has copyright, `module`, public interface imports, a module docstring and `@[expose] public noncomputable section`. No `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option` token occurs. `git diff --check inp...HEAD -- 'KAM/Planetary/Averaging/OscillatorSeriesAlgebra*.lean'` exits 0 with only the merge-base warning on stderr.

## Findings, errata, deviations and closeout

- **N1 (inherited branch hygiene, confirmed):** the full requested three-dot protected-path diff contains the 34 generated-root imports quoted above. Refutation check against the actual pre-package integration commit isolates them as inherited, not an edit by this package. Disposition: scoped PASS WITH NOTES; do not certify the whole branch or regenerate generated files during this audit.
- **N2 (expected lint exception, confirmed):** lint exits 1 only for “KAM.lean is out of date”; module checks, frozen guard and ABI hashes pass. This exact exception is allowed by the brief.
- **N3 (handoff precision, informational):** shared signatures live in the main inp worktree; production has 335 lines rather than the stated 333. The exact signature hash and substantive statements match. Neither is a proof defect.
- No suspected new pinned-source or blueprint mathematical defect found in this scoped transfer. The blueprint's existing `sourcegap` after `stepP:p2:oi-disp` remains: “the extension is stated by its (short) list of changes, not rewritten in N.” This scalar algebra package does not purport to discharge the entire extension.
- No mathematical deviation introduced by the implementation or auditor. No unauthorized edits, commits, permission requests or root regeneration.

Closeout: five public declarations classified; four exact theorem signatures checked mechanically and by Lean application; literal definition checked; complete scoped proof read and refutation pass performed; targeted build and axioms independently verified. Kernel replay independently exits 0; full lint has only its explicitly allowed stale-root failure. No seal or full-node closure claim is made. Final source hash was rechecked against frozen-v1; temporary probe and captured scratch logs were removed. The initial untracked handoff was preserved. Final repository status contains only that pre-existing handoff and this report.
