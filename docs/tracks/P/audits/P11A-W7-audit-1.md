# P11A-W7 independent package audit 1

Verdict: **PASS WITH NOTES** for `bpP:p11a:diophantine-measure`. No mathematical or statement-fidelity failure found. This is an infrastructure package, with no provider or frozen anchor to seal; no physical headline/root closure is claimed.

## Scope and authority

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the W7 handoff and its AUDIT FOCUS, Track P statement conventions, design Revision 3 (W7 row L709, mapping L233–237, contracts L500–509, signature L1106–1118), delivered signatures L163–175, and design audits 1–3. Applied the statement-audit method. The latest explicit user path overrides the generic brief's main-worktree output instruction.

Snapshot: HEAD `526146e4975bd0d49e583c25e7bf1086619f0a22`; `inp` = `05a664ce5d0c96e94e699a691f4d85d1e7b7f8d2`; `inp-p11aw6` = `a23ae97b3554360f03657f80388c2855ba6e2ecd` at inspection. `git diff inp...HEAD` has four WeakMeasure additions (BallSublevel, MeasureTools, Sublevel, Diophantine; 1021 lines). Only Diophantine is in W7 scope. The named W6 ref has advanced beyond the merged W6 history: its merge base with HEAD is `ea71d2a1f23fc965d151b97959e51453b555d176`; hence its full three-dot diff includes unrelated integrated work. Both its Diophantine-filtered diff and `git diff HEAD^ HEAD` identify exactly the new 171-line module. W6 dependencies are inspected for attachment, not independently re-audited as W7.

Pins:

| Artifact | SHA-256 |
|---|---|
| W7 `Diophantine.lean` | `aa019e9f0b6d82aea5e45e476dc4349dc5d538d247a70e3e19c1ce0a7dc6a1d4` |
| Design Revision 3 | `8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9` |
| Delivered `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean` | `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092` |
| `blueprint-P/parts/p11a1-weak-measure.tex` | `66b5ce26db59b57dbf934938a7bae2fead6b6ff4c7c9d420d33b9582e272bab5` |

## Declaration and node ledger

All Lean names below are in `KAM.Planetary`; line locators refer to `KAM/Planetary/WeakMeasure/Diophantine.lean`.

| Node / role | Declaration or proof obligation | Verdict | Reason |
|---|---|---|---|
| Geometry helper | `p11_K_sub_V`, L29 | PASS | Derives inclusion from the source thickening premise, with zero displacement. |
| Continuity helper | `continuous_p11dotZ`, L32 | PASS | Finite linear functional on the actual Pi carrier. |
| `stepP:p11a:dm-compact` | `p11_dm_compact`, L36–56 | PASS | Closed inequalities relative to compact K, including harmless k=0 factor; needs only C^mu regularity, no positivity or size premises. Stronger than the main theorem's compactness component. |
| Normalization helper | `p11euclid_int_pos`, L58 | PASS | Nonzero integer mode has positive explicit Euclidean length. |
| Normalization helper | `p11euclid_unit_int`, L68 | PASS | Dividing a nonzero real-cast mode by its Euclidean length yields a unit vector. |
| Dot-product helper | `p11dot_unit_int`, L73 | PASS | Literal finite-sum scaling identity, even at k=0; no nonzero premise needed. |
| `stepP:p11a:dm-onek` attachment | `p11_dm_onek_hyp`, L79–99 | PASS | Constructs every S1–S3 field from D1–D3 at the normalized mode; no sublevel estimate assumed. |
| Constant helper | `p11Csub_nonneg`, L101 | PASS | Uses beta>0 and M>=0, patch geometry; ordinary nonnegative factors. |
| `stepP:p11a:dm-union` | `hsub`, L134–148 | PASS | A failed good-set inequality supplies a nonzero mode; normalizes and raises nonnegative quantities to rho to obtain inclusion in the closed sublevel set. |
| `stepP:p11a:dm-onek` estimate | `hterm`, L149–161 | PASS | Applies W6 `sublevel` with positive eps=(psi/length)^rho<beta/4; derives the exact real-power factorization. |
| `stepP:p11a:dm-sum` | final `calc`, L162–167 | PASS | Measure monotonicity, countable subadditivity, termwise bound, and constant extraction in ENNReal; no summability assumption or real-tsum fallback. |
| `bpP:p11a:diophantine-measure` | `diophantine_measure`, L110 | PASS WITH NOTES | Full statement is byte-identical to delivered signature before the proof delimiter. Compactness and exact constant/exponent retained. |

The theorem is precisely the blueprint L149–169 with ambient Pi max norm for diameter, explicit Euclidean mode length, Lebesgue volume, and one perturbed map per mode. The finite/infinite right side is handled in ENNReal. `psi 0` and `wt 0` are arbitrary and never constrained or consumed. No constant is chosen after the profile or mode.

## Expanded binder audit

For `diophantine_measure`, each row is one binder or one expanded logical field; structure carrier fields are also enumerated. SOURCE cites the blueprint at `p11a1-weak-measure.tex:149–160` (D1–D4); TYPING records pure object formation. No instance input is hidden in the declaration.

| Binder / expanded field | Bin | Authority / meaning |
|---|---|---|
| n | TYPING | Parameter dimension N. |
| m | TYPING | Frequency dimension. |
| rho | TYPING | Natural scalar-family exponent. |
| mu | TYPING | Natural derivative order. |
| P.K | TYPING | Parameter set in Fin n → R. |
| P.V | TYPING | Open-domain carrier. |
| P.v | TYPING | Thickening radius. |
| P.n_pos | SOURCE | N>=1, L150. |
| P.nonempty | SOURCE | K nonempty, L150. |
| P.compact | SOURCE | K compact, L150. |
| P.openV | SOURCE | V open, L150. |
| P.diameter_pos | SOURCE | d_infty(K)>0, L150. |
| P.v_pos | SOURCE | vartheta>0, L150. |
| P.thick_sub | SOURCE | K_vartheta subset V, L150. |
| w | TYPING | Original frequency map. |
| wt | TYPING | Mode-dependent perturbed maps. |
| beta | TYPING | Amount parameter. |
| M | TYPING | Size parameter. |
| H.m_pos | SOURCE | m>=1, L150. |
| H.mu_pos | SOURCE | mu>=1, L150. |
| H.convention | SOURCE | rho=1 or 2, L150. |
| H.beta_pos | SOURCE | beta>0, L150. |
| H.size_ge | SOURCE | M>=beta, L150. |
| H.regular | SOURCE | w is C^(mu+1) on V, L150. |
| H.perturbed_regular | SOURCE | Each nonzero-mode wt is C^mu on V, L155. |
| H.amount | SOURCE | D1: beta<=index_def, L152. |
| H.size | SOURCE | D2: all unit c, orders 1..mu+1, y in thickening; full Euclidean tensor bound, L153. |
| H.close | SOURCE | D3: all nonzero k, unit c, orders 0..mu, y in thickening; diagonal jet of scalar-family difference <=beta/2, L157. |
| psi | TYPING | Profile on modes; zero-mode value unconstrained. |
| hp | SOURCE | Positive profile at each nonzero mode, L155. |
| hsmall | SOURCE | D4: normalized natural power <beta/4, L158. |

Counts: SOURCE 19, TYPING 12, STANDING 0, RULED 0, EXCESS 0 (31 expanded rows). Nested D2/D3 index and direction quantifiers are preserved exactly; `p11JetBound true` expands to all orders through mu on the thickening. The bundled amount is a source hypothesis of this abstract theorem, not an assumed conclusion about a physical frequency.

Other public helpers: all implicit dimensions, orders, maps, sets and scalar parameters are TYPING; patch and DioHyp fields expand as above. The only additional proof binders are `hwt` (source perturbed regularity in the compactness helper), `hk : k != 0` in the length/unit/mode helpers (the source nonzero-mode condition), and `hb : 0<beta`, `hM : 0<=M` in the constant helper (source positivity; M>=beta implies the latter). `psi`, `k`, `v` are data, never conclusion-shaped assumptions. The compactness helper drops unused source assumptions; arithmetic helpers state identities or nonnegativity under their natural conditions. EXCESS=0 throughout.

## Definitions and semantic attachment

W7 introduces **zero** `def`, `abbrev`, `structure`, instance, or choice-defined objects. Its local `x` is exactly psi(k)/|k|_2, and `S` is exactly the closed scalar-power sublevel set over the original K. No fallback values or replacement carriers are introduced.

Inspected unchanged W0 definitions in `Basic.lean:24–110`: `P11Vec` is the required Pi carrier; `p11euclid` uses the explicit Euclidean formula; `p11dot` and `p11dotZ` are literal finite sums; `p11thick` is Euclidean thickening; `p11Good` is the literal simultaneous nonzero-mode predicate; `p11Csub` is exactly the blueprint formula. `P11Patch` and `P11DioHyp` bundle only source geometry/D1–D3 inputs. `P11SublevelHyp` bundles S1–S3 and is constructed in this proof, not assumed as extra W7 input. Diagonal and full-tensor norms retain their distinct roles.

The use of the amount infimum is justified by existing `index_def_le` (`Basic.lean:257–260`): bounded-below values are proved nonnegative, and the actual unit direction and y in K supply membership. It does not rely on an empty or junk infimum. W7 never uses the least-index selector or chooses an attaining point.

Definition classification for the unchanged literal objects consumed here: BODY_MATCH OK; PUBLIC_CARRIER OK; WELL_DEFINEDNESS N/A_LITERAL; CHARACTERIZATION N/A_LITERAL; CHOICE_INDEPENDENCE N/A; DEFINITION_VERDICT PASS for their W7 use. Existing derivative suprema/amount are dependency infrastructure; this report checks their actual W7 attachment, not a new full W0 audit.

## Mechanical checks

All audit-owned Lean/Lake invocations are sequential with `LEAN_NUM_THREADS=1` and nice priority 5. No library clean, cache fetch, package modification, or full rebuild was run.

1. Targeted build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11aw7 KAM.Planetary.WeakMeasure.Diophantine
```

Exit **0**. Output: `[inp-gate] slot 2 acquired 10:56:41 for KAM.Planetary.WeakMeasure.Diophantine`; `Build completed successfully (9056 jobs).` The wrapper runs `nice -n 5 lake build` under the prescribed compile gate. Four replayed unused-variable warnings are outside W7: Stability L302 (`hn`), L304 (`hK`), L403 (`hn`); DividedDifference L96 (`hab`). No W7 warnings.

2. Exact-signature assembly and axiom closure:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AW7Audit.lean
```

Exit **0**, no errors or warnings. The probe imports only the proved W7 module, copies the delivered `diophantine_measure` signature under `audit_w7_signature`, and proves it by `exact diophantine_measure H psi hp hsmall` (all explicit binders, in order). Thus no draft signature or sorry-bearing source was imported. A Python comparison also returned `Signature byte equality: True` for the complete pre-proof theorem text. The probe prints all nine new public exports:

```text
'KAM.Planetary.p11_K_sub_V' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.continuous_p11dotZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dm_compact' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11euclid_int_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11euclid_unit_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11dot_unit_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_dm_onek_hyp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11Csub_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.diophantine_measure' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no provider/frozen type-equality or seal-body target in W7; those checks are N/A, not waived for an anchor. The actual design-signature application is checked instead. The temporary probe has been deleted.

3. Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakMeasure.Diophantine
```

Exit **0**. Complete output: `replaying KAM.Planetary.WeakMeasure.Diophantine`. One invocation covers the sole new W7 theorem module; no provider module exists.

4. Source lint:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the brief-permitted stale-root exception. Complete output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (555 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

No forbidden-token, line-length, file-size, module, errata-rendering, frozen-integrity or ABI errors. Generated KAM.lean was not regenerated.

5. Static checks: 171 total lines (below the cap), required copyright/module/public imports/module docstring/public section present, no new definitions or forbidden tokens/overrides. Recursive inspection of every project import found no `KAM.Frozen.*` or `KAM.Provider.*` module, so no DRAFT_SORRY dependency or quarantine violation. The only direct project import is W6 Sublevel; existing Basic/Stability/BallSublevel/MeasureTools/ScalarSublevel/DividedDifference and Norms/Fourier infrastructure form its dependency closure. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty. `git diff --check` exits **0**.


## Notes, errata, and limits

N1 (documentation only): the module docstring L14–16 names `p11_dm_union` and `p11_dm_onek` as if they were declarations. They are not exports: union is the local `hsub`; the one-mode work is `p11_dm_onek_hyp` plus local `hterm`. The handoff correctly explains the inlining. This does not affect any graph obligation or theorem type.

No new mathematical blueprint defect, pinned-source erratum, design signal, or mathematical deviation was found in the W7 scope. Previously recorded source adaptations (including k-dependent perturbed maps, rho=1/2 scalar family, and recomputed C_sub) remain as stated at blueprint L163 and L226. No fresh comparison against the entire Rus01 PDF is claimed. Later power-law summation, limiting-frequency attachment, and physical/frozen headline closure are outside this package.

No production repair or git mutation is authorized or performed. Only this report persists; audit probes are deleted after checks. The pre-existing untracked W7 handoff is retained.

## Closeout

**PASS WITH NOTES for P11A-W7**: the exact design theorem and all four mapped proof steps pass statement review, actual-premise attachment, serial targeted build, nine axiom checks and kernel replay. Notes are the documentation-only helper names and the expressly permitted stale generated root. No frozen anchor is a seal target in this package.

Final integrity: W7 source hash remains the pinned hash above; protected-path diff remains empty; `git diff --check` exits 0. The report has no trailing whitespace and balanced code fences. Git status contains only the new report and the pre-existing untracked handoff. No temporary audit Lean probe remains.
