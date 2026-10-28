# P11A-C4 independent package audit 1

Overall verdict: **PASS WITH NOTES**. No blocking mathematical or signature finding in the two-module audit focus. This is infrastructure acceptance, not a frozen-anchor seal or P-FIXED closure.

## Scope and immutable inputs

Audited worktree `/root/code/KAM-inp-p11ac4`, HEAD `d8186af4760416753d9fc6f3c93eca3f0bfdc2b9`, against `inp` at `31f0bfbf70c07b1eefd006237f331c00e003a0e5`, using `git diff inp...HEAD`. Read AGENTS.md, PLAN.md, DECISIONS.md, the package brief, P11A-C4-handoff.md, Track P statement, design row P11A-C4 (L715), relevant proof registry/signatures and design audits 1–3. Applied lean-statement-audit to premise, carrier and signature checks. Only this report is a persistent audit edit; transient probes are confined to `.lake/abi-scratch/`. The user's explicit report destination supersedes the generic brief's main-worktree destination.

The full branch diff contains five added files: the two C4 files and three inherited W8 files. Only `KAM/Planetary/MaximalStep/Cutoff.lean` (113 lines) and `Divisor.lean` (94 lines) receive a new implementation verdict. W8 is inspected only at the consumed `limit_bridge` boundary. The pre-existing untracked handoff is preserved. No provider or frozen theorem is implemented here; provider/frozen ABI equality and literal frozen seal-body checks are **N/A**. Instead exact design-type and explicit-binder assembly probes check the three contracted exports and both helpers.

The standalone signature file is absent under this worktree's `.drafts/design/`, but the referenced original exists at `/root/code/KAM-inp/.drafts/design/P11ASignatures.lean`. Its SHA-256 is `c31fda0b479f2dd0488b12e7f2daeda18f965eb316610df1c65f14012dfcb092`, matching design audit 3. The checked-in design hash is `8619ea896c856347a9a5c5efac5080f0c830ea19245320b5f03a2b4267a300b9`; blueprint `p11a2-cutoff-step.tex` hash is `990694a832aa02dca0138c5cbb3bab842984583f4ca92576479eff04786ed3ec`, also matching audit 3. Python extraction found the complete theorem text before `:=` byte-identical for `cutoff`, `divisor_wide`, and `divisor_perturb` against the original signature file (L264–298), as well as the embedded design signatures (L1207–1241). The helper `p11_taylor_real` has no prescribed signature; its source is the reality step at blueprint L132. The handoff's broad “signatures unchanged” claim is understood to concern the three contracted exports.

## Declaration ledger

Names below have prefix `KAM.Planetary.`.

| Node / obligation | Declaration and implementation location | Verdict | Reason |
|---|---|---|---|
| `bpP:p11a:cutoff` core signature | `cutoff`, Cutoff:80–111 | PASS WITH NOTES | Exact designed four-clause result; C3 at M=eps followed by C1 at M=2eps. Blueprint coefficient/full polynomial clauses are separately planned, not closed by this export. |
| `stepP:p11a:cu-c` Taylor reality | `p11_taylor_real`, Cutoff:29–77 | PASS | Derivative of the imaginary part vanishes on the real line; real restriction chain rule and derivative uniqueness establish reality without a new premise. |
| `bpP:p11a:x-duality` dot-product clause | `p11_norm_dotC_le`, Divisor:29–37 | PASS | Sum triangle inequality, integer scalar modulus and Pi coordinate bound give the exact l1/max-norm duality. |
| `bpP:p11a:divisor-wide` | `divisor_wide`, Divisor:40–54 | PASS | W8 limit_bridge supplies per-mode margin; nonpositive-exponent monotonicity gives cutoff-wide margin. No limit vector is assumed. |
| `bpP:p11a:divisor-perturb` | `divisor_perturb`, Divisor:57–92 | PASS | Source premises and exact D/2 conclusion on all of E+t, using each contained convex ball. No global convexity or openness of E assumed. |

No anchor receives a seal-ready verdict: this package has no frozen theorem/provider pair. All three source-facing contracted exports satisfy declaration fidelity and have proved bodies; the broader source nodes retain the notes below.

## Binder audit

Each row lists one outer binder, splitting the two fields of `p11Admissible`. SOURCE includes explicit source conventions and the exact accepted design's positivity guards. TYPING denotes only parameter/object carriers. No instance binders or bundled proof obligations are hidden. Quantifiers inside `hb`, `hreal`, `hu`, `hc`, and `hdiv` range over precisely the source domains/mode windows, retaining their membership, nonzero and size guards; these are expanded in the final column rather than treated as unexamined gates.

| Declaration | Binder / expanded field | Bin | Source and meaning |
|---|---|---|---|
| cutoff | n | TYPING | blueprint p11a2:113–124; design:1207–1217; ambient data |
| cutoff | r | TYPING | blueprint p11a2:113–124; design:1207–1217; ambient data |
| cutoff | s | TYPING | blueprint p11a2:113–124; design:1207–1217; ambient data |
| cutoff | T | TYPING | blueprint p11a2:113–124; design:1207–1217; ambient data |
| cutoff | d | TYPING | blueprint p11a2:113–124; design:1207–1217; ambient data |
| cutoff | eps | TYPING | blueprint p11a2:113–124; design:1207–1217; ambient data |
| cutoff | q | TYPING | blueprint p11a2:113–124; design:1207–1217; ambient data |
| cutoff | B | TYPING | blueprint p11a2:113–124; design:1207–1217; ambient data |
| cutoff | R | TYPING | blueprint p11a2:113–124; design:1207–1217; ambient data |
| cutoff | hn | SOURCE | blueprint p11a2:113–124; design:1207–1217; positive dimension |
| cutoff | hr | SOURCE | blueprint p11a2:113–124; design:1207–1217; r>0 |
| cutoff | hs | SOURCE | blueprint p11a2:113–124; design:1207–1217; s>0 |
| cutoff | hT | SOURCE | blueprint p11a2:113–124; design:1207–1217; T>=0 |
| cutoff | hd | SOURCE | blueprint p11a2:113–124; design:1207–1217; d>0 |
| cutoff | hdr | SOURCE | blueprint p11a2:113–124; design:1207–1217; d<r |
| cutoff | he | SOURCE | blueprint p11a2:113–124; design:1207–1217; nonnegative upper bound eps |
| cutoff | hq | SOURCE | blueprint p11a2:113–124; design:1207–1217; q>0 |
| cutoff | hq1 | SOURCE | blueprint p11a2:113–124; design:1207–1217; q<1 |
| cutoff | hB | SOURCE | blueprint p11a2:113–124; design:1207–1217; B open |
| cutoff | hR.1 | SOURCE | blueprint p11a2:113–124; design:1207–1217; holomorphy on D(r,s;B) |
| cutoff | hR.2 | SOURCE | blueprint p11a2:113–124; design:1207–1217; one-periodicity on that domain |
| cutoff | hb | SOURCE | blueprint p11a2:113–124; design:1207–1217; for every z in D(r,s;B), norm R(z)<=eps |
| p11_taylor_real | n | TYPING | blueprint p11a2:113–124,132; ambient data |
| p11_taylor_real | r | TYPING | blueprint p11a2:113–124,132; ambient data |
| p11_taylor_real | s | TYPING | blueprint p11a2:113–124,132; ambient data |
| p11_taylor_real | B | TYPING | blueprint p11a2:113–124,132; ambient data |
| p11_taylor_real | F | TYPING | blueprint p11a2:113–124,132; ambient data |
| p11_taylor_real | hs | SOURCE | blueprint p11a2:113–124,132; s>0 |
| p11_taylor_real | hB | SOURCE | blueprint p11a2:113–124,132; B open |
| p11_taylor_real | hF.1 | SOURCE | blueprint p11a2:113–124,132; holomorphy on D(r,s;B) |
| p11_taylor_real | hF.2 | SOURCE | blueprint p11a2:113–124,132; domain-local one-periodicity, unused but allowed admissibility |
| p11_taylor_real | hreal | SOURCE | blueprint p11a2:113–124,132; for all real phase x and real parameter b lying in D, Im F=0 |
| p11_norm_dotC_le | m | TYPING | blueprint p11a2:33; ambient data |
| p11_norm_dotC_le | k | TYPING | blueprint p11a2:33; ambient data |
| p11_norm_dotC_le | v | TYPING | blueprint p11a2:33; ambient data |
| divisor_wide | n | TYPING | blueprint p11a2:148–151; design:1223–1231; ambient data |
| divisor_wide | gamma | TYPING | blueprint p11a2:148–151; design:1223–1231; ambient data |
| divisor_wide | tau | TYPING | blueprint p11a2:148–151; design:1223–1231; ambient data |
| divisor_wide | T | TYPING | blueprint p11a2:148–151; design:1223–1231; ambient data |
| divisor_wide | v | TYPING | blueprint p11a2:148–151; design:1223–1231; ambient data |
| divisor_wide | u | TYPING | blueprint p11a2:148–151; design:1223–1231; ambient data |
| divisor_wide | hg | SOURCE | blueprint p11a2:148–151; design:1223–1231; gamma>0 |
| divisor_wide | ht | SOURCE | blueprint p11a2:148–151; design:1223–1231; tau>=0 |
| divisor_wide | hT | SOURCE | blueprint p11a2:148–151; design:1223–1231; T>0 |
| divisor_wide | hu | SOURCE | blueprint p11a2:148–151; design:1223–1231; every nonzero mode of size<=T has margin 2gamma |k|^(-tau) at u(k) |
| divisor_wide | hc | SOURCE | blueprint p11a2:148–151; design:1223–1231; same modes: norm(u(k)-v)<=gamma |k|^(-tau-1) |
| divisor_perturb | n | TYPING | blueprint p11a2:157–162; design:1232–1241; ambient data |
| divisor_perturb | E | TYPING | blueprint p11a2:157–162; design:1232–1241; ambient data |
| divisor_perturb | t | TYPING | blueprint p11a2:157–162; design:1232–1241; ambient data |
| divisor_perturb | T | TYPING | blueprint p11a2:157–162; design:1232–1241; ambient data |
| divisor_perturb | D | TYPING | blueprint p11a2:157–162; design:1232–1241; ambient data |
| divisor_perturb | L | TYPING | blueprint p11a2:157–162; design:1232–1241; ambient data |
| divisor_perturb | w | TYPING | blueprint p11a2:157–162; design:1232–1241; ambient data |
| divisor_perturb | ht | SOURCE | blueprint p11a2:157–162; design:1232–1241; t>0 |
| divisor_perturb | hT | SOURCE | blueprint p11a2:157–162; design:1232–1241; T>0 |
| divisor_perturb | hD | SOURCE | blueprint p11a2:157–162; design:1232–1241; D>0 |
| divisor_perturb | hL | SOURCE | blueprint p11a2:157–162; design:1232–1241; L>=0; accepted design norm-bound guard |
| divisor_perturb | hw | SOURCE | blueprint p11a2:157–162; design:1232–1241; holomorphic on E+t |
| divisor_perturb | hb | SOURCE | blueprint p11a2:157–162; design:1232–1241; every b in E+t has operator norm D w(b)<=L |
| divisor_perturb | hsmall | SOURCE | blueprint p11a2:157–162; design:1232–1241; t T L<=D/2 |
| divisor_perturb | hdiv | SOURCE | blueprint p11a2:157–162; design:1232–1241; every b in E and nonzero mode of size<=T has real-center divisor>=D |

Counts: SOURCE=31, TYPING=30, STANDING=0, RULED=0, EXCESS=0. The conditional reality input in the last conclusion of `cutoff` is exactly source clause (c), not an unconditional input added to the estimate.

## Definitions and proof consumption

There are **no new def/abbrev/structure declarations** in either audited file. Definition classification for the new inventory: BODY_MATCH / PUBLIC_CARRIER / WELL_DEFINEDNESS / CHARACTERIZATION / CHOICE_INDEPENDENCE = N/A (empty inventory); DEFINITION_VERDICT = PASS.

Expanded the consumed definitions at their existing C0/W0/frozen boundaries: `P11Vec n = Fin n → ℝ`, `P11CVec n = Fin n → ℂ`, family = (complex angle × complex action) × complex parameter; all norms are Pi max norms. `domain_def` is angle strip × action polydisc × B; `p11Admissible` is domain-local holomorphy plus one-periodicity, `p11Bound` is pointwise norm bound and `p11Real` tests actual real inclusions. `p11Taylor` is value plus complex Frechet derivative at eta=0; `p11Cutoff` is literal Fourier cut of that polynomial; `p11dotC` / `p11dotZ` are finite coordinate sums. `p11Error` is the existing dimension-only explicit Fourier-tail expression. `actionNbhd` is the union of max-norm balls about real inclusions of E. No changed definition, invented fallback or choice witness is introduced. Differentiability at eta=0 is established before relying on totalized `fderiv`; the positive action radius supplies a genuine neighborhood.

`cutoff` consumes `taylor_cutoff` (Cutoff:90) with all source premises and the supplied bound, then `fourier_cutoff` (91–92) on the resulting Taylor part with bound 2eps. For the remainder, the two explicit domain inclusions (100–103) put each summand on its own proven domain. The triangle inequality pays eps*q²/(1-q) + E*2eps exactly. Taylor reality holds along t↦F(theta,t eta,b), |t|<1, entirely within the action polydisc, and is fed to Fourier reality (93). No reality or coefficient estimate is assumed in the unconditional norm clauses.

`divisor_wide` consumes the actual W8 `limit_bridge` theorem (Divisor:50). Nonzero integer k gives |k|>=1; monotonicity of x^(-tau) for tau>=0 yields T^(-tau)<=|k|^(-tau). The unused hT is retained exactly as designed. The source's intermediate per-mode margin is available from the consumed theorem; this export states the cutoff-wide conclusion.

`divisor_perturb` extracts an actual real center J from neighborhood membership. Its open ball is contained in E+t (69–72), and the convex-ball mean value theorem (74–76) gives norm(w(b)-w(J))<=L norm(b-J). Finite duality then gives the divisor difference <=T L t<=D/2 (79–85); the final reverse triangle estimate uses the actual source center margin. Arbitrary disconnected or empty E causes no gap. The Pi complex ball is exactly the source polydisc, and the complex Frechet operator norm is used directly.

The project-import closure has 61 modules. Its ten frozen imports are all manifest state SEALED and kind definition: ActionNbhd, ComplexStrip, HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip, IsRealOnReals, OmegaZero, SymplecticForm, and Planetary.Phase. No imported frozen theorem, DRAFT_SORRY anchor or provider occurs in the closure. Checked the frozen Phase and actionNbhd bodies directly; manifest/lint checks validate their immutable identities.

## Notes, uncertainties and source defects

1. `cutoff` is the exact accepted core signature, but blueprint L117–123 additionally states coefficient bounds and trigonometric-polynomial/extended admissibility facts. The design expressly separates `cutoff_coefficients` (L2184–2194); it is absent from these two audited files. Do not mark the entire blueprint cutoff/coefficient node closed on this report alone. Similarly `p11_norm_dotC_le` proves the dot-product part of x-duality; the character estimate is an existing separate interface, not a new theorem here.
2. The helper has no frozen/design signature to compare byte-for-byte; its premises and full conclusion were reconstructed from blueprint reality step L132. It makes no extra source-facing demand on the contracted cutoff result. The retained unused hT/hD binders in Divisor match the contract.
3. No suspected defect in the scoped blueprint mathematics or pinned paper is established. The cutoff estimates are explicitly original constants/deviations D-4/D-5 in the blueprint; this implementation adds no new deviation. Earlier design audit findings concern other packages or separately planned companions and are not silently promoted to proof closure here. No external paper was used as a substitute for the pinned local blueprint.

## Independent mechanical receipts

All successful Lean/Lake checks below were run with `LEAN_NUM_THREADS=1` and `nice -n 5`, sequentially. The targeted build used the required campaign gate. An initial lint attempt was stopped during its Python frozen-anchor check before reaching ABI Lean elaboration; its partial output is not used as a validation receipt. The complete lint receipt below is a later serialized rerun.

### Targeted build

```text
LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11ac4 KAM.Planetary.MaximalStep.Cutoff KAM.Planetary.MaximalStep.Divisor
[inp-gate] slot 2 acquired 12:54:34 for KAM.Planetary.MaximalStep.Cutoff KAM.Planetary.MaximalStep.Divisor
Build completed successfully (9107 jobs).
exit 0
```

This was a targeted overlay build, not a clean rebuild. Output replayed upstream deprecation and unused-variable warnings. The only warnings attributed to an audited module were Divisor:41:37 unused `hT` and Divisor:58:31 unused `hD`; no C4 elaboration error or resource override.

### Exact signatures, explicit assembly and axioms

Generated `.lake/abi-scratch/P11AC4Audit.lean` by extracting the three exact source signatures from the pinned original signature file, replacing only declaration names and bodies. The explicit assembly bodies were:

```lean
exact KAM.Planetary.cutoff hn hr hs hT hd hdr he hq hq1 hB hR hb
exact KAM.Planetary.divisor_wide hg ht hT v u hu hc
exact KAM.Planetary.divisor_perturb ht hT hD hL w hw hb hsmall hdiv
```

Each was followed by `example : type_of% @KAM.Planetary.audit_<name> := @KAM.Planetary.<name>`. The two helper declarations were also recopied under fresh names with literal explicit-binder applications. No signature draft or its sorry bodies were imported.

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P11AC4Audit.lean
'KAM.Planetary.p11_taylor_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.p11_norm_dotC_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.divisor_wide' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.divisor_perturb' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

### Kernel replay

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.MaximalStep.Cutoff KAM.Planetary.MaximalStep.Divisor
replaying KAM.Planetary.MaximalStep.Divisor
replaying KAM.Planetary.MaximalStep.Cutoff
exit 0
```

One invocation replays both audited modules, including all five public theorem bodies. No provider exists in this package, so no provider module is added to the invocation.

### Source lint and integrity

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (659 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole nonpassing diagnostic is the explicitly permitted stale generated root. No root regeneration was performed. No forbidden tokens, size/module violations or overlong lines were reported. A separate scoped token scan found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `EuclideanSpace` or `set_option` in either audited file.

`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0. `git diff --check`: empty, exit 0. The report also passed an explicit trailing-whitespace and balanced-fence check. Temporary `.lake/abi-scratch/P11AC4Audit.lean` was deleted after successful elaboration. Final tracked diff is unchanged; git status has only the pre-existing untracked handoff and this new untracked report. No state-changing git command, production edit, dependency update, cache fetch or clean was performed.

Closeout: **PASS WITH NOTES for P11A-C4's exact two-module focus**. The core signatures, proof consumption, allowed axiom closure, kernel replay, and hygiene gates pass, with only the authorized stale-root lint exception. The coefficient companion and broader source-node/frozen-headline closure remain outside this package receipt. Suspected new source errata: none. Audit-introduced mathematical deviations: none.
