# LOCK-ASM1 independent audit 1

**Verdict: PASS WITH NOTES for the authorized part-1 helper package.** No frozen anchor is sealed or seal-ready on the strength of this package. The lunar headline remains unproved here: the actual certified barrier and its action-window attachments are pending. No mathematical blocker was found. Notes: one trailing-space defect, the permitted stale generated root, the explicitly documented three extra sign checks, and the still-uninstantiated certificate/data dependency.

Auditor `maud-lockasm-1`, 2026-10-30 UTC. Focused tier-2, refute-first review, including the user's additional focus (a)–(c). Read-only implementation inspection; only this report and deleted worktree-local probes were written. No commits, repairs, generated-root changes, or subagents.

## Scope and immutable inputs

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the complete local handoff, original `/root/code/KAM-inp/.drafts/briefs/lock/PKG-LOCK-ASM1.md`, signed SOLockSignatures, design §§1.2–1.5, 5–7, and the imported action/barrier/orbit/centre implementation. The handoff has no literal AUDIT FOCUS section; its stated scope plus the user's extra focus control. The user's exact package-worktree report path overrides the generic brief's main-worktree destination.

This is SO unfrozen infrastructure, not an I/N/P provider-sealing package. The SO design and signatures are the relevant source authority; unrelated I/N/P theorem statements do not specify these helpers. Provider-versus-frozen and frozen-seal-body probes are N/A. Fresh copies of the actual signed statements, with application bodies, were checked instead.

Frozen-v1:

- HEAD `258327fea62f0d32a338186f82b033afd4860b9e`.
- `inp` and merge base `a5f010ebcb430f2c7a9b15726507db29321760eb`.
- Full `git diff inp...HEAD`: one file, `KAM/SpinOrbit/Lock/Assembly.lean`, 389 added lines; every line reviewed.
- Initial worktree state: only the supplied untracked `docs/tracks/SO/audits/LOCK-ASM1-handoff.md`.

| Frozen input | SHA256 |
|---|---|
| Assembly.lean | `f78501c0aafe2cbaaeb239051e6329781ae17300635e53e93df19241f1037454` |
| docs/tracks/SO/design/SO-LOCK-DESIGN.md | `7785225bb6f3d3985ae7719f3aecf107eb33302530147bbff5672935eb170c6d` |
| /root/code/KAM-inp/.drafts/design/SOLockSignatures.lean | `aa544d085056410f205df49c08a778e854ad79ea48ad158fffe5302c3d0cd60d` |
| local LOCK-ASM1-handoff.md | `d9160033ff95e01d0d9b39013c89323e36ac26f4d6e0662b13f5ec23f576b110` |

Acceptance criteria: exact signed interfaces; complete authorized slice; faithful definition bodies; correct literal inequalities and term-level conditional assembly; standard axiom closure; successful targeted build, probe and kernel replay; hygiene with the brief's sole generated-root lint exception. Reviewed against this frozen-v1, not against prior audit verdicts.

## Declaration inventory

All names below have prefix `KAM.SpinOrbit.Lock`; line anchors refer to Assembly.lean at frozen-v1. PASS here means the stated helper contract, not source-headline closure.

| Node / role | Declaration : line | Verdict | Reason |
|---|---|---|---|
| CONF corollary | abs_le_of_libAction_lt : 39 | PASS | Signed header byte-identical to signatures:111–114; both weighted coordinate bounds. |
| Transfer ingredient | sqrt_sq_add_sq_le : 57 | PASS | General planar inequality; absolute perturbation bounds imply nonnegative A,B. |
| ASSEMBLY transfer | sqrt_libAction_le : 80 | PASS | Signed header byte-identical to signatures:117–119; correct sqrt π and sqrt Ω factors. |
| Finite sums | abs_list_sum_map_le : 112 | PASS | Inductive triangle inequality for arbitrary lists, including repeats/empty. |
| Finite derivatives | hasDerivAt_list_sum_map : 118 | PASS | Derivative of actual finite sum, no differentiability assumption hidden. |
| Centre majorant | lockCentreAbs : 128 | PASS | Exact rational sum of coefficient absolute values. |
| Centre derivative majorant | lockCentreDAbs : 132 | PASS | Exact rational sum (k+1)|c_k|; factor 2π supplied separately. |
| Centre bound | abs_lockCentre_le : 135 | PASS | Uniform whole-real-line sine bound. |
| Centre derivative | hasDerivAt_lockCentre : 143 | PASS | Actual finite sine series; correct 2π(k+1) frequency. |
| Derivative bound | abs_deriv_lockCentre_le : 154 | PASS | Uniform bound 2π times lockCentreDAbs. |
| Root approximation | lockNatSqrt : 174 | PASS | Total fuel-bounded integer Newton computation, no correctness presumed. |
| Root approximation | lockSqrtUp : 179 | PASS WITH NOTES | Total rational candidate, not a globally certified sqrt function; candidates rechecked. |
| Candidate sign | lockSqrtUp_nonneg : 183 | PASS | Nonnegative on the entire rational carrier. |
| π lower enclosure | lockPiLo : 187 | PASS | 3141592/10^6, strictly positive and strictly below π. |
| π upper enclosure | lockPiHi : 188 | PASS | 3141593/10^6, strictly above π. |
| Literal verifier | lockLiteralCheck : 193 | PASS WITH NOTES | Signed type identical to signatures:319; new body sound, extra signs documented below. |
| Output facts | LockLiteralFacts : 206 | PASS | Transparent output proposition with all five required real inequalities. |
| Verifier soundness | lockLiteralCheck_sound : 214 | PASS | No premise beyond passing check and rational typing data. |
| Lunar scale | lunarOmega : 295 | PASS | Signed type and complete literal body 8/65 match signatures:64. |
| Lunar instance | lunar_literalCheck : 297 | PASS | Actual verifier on all lunar literals proved by decide +kernel. |
| Parametric assembly | lunar_sync_lock_of_barrier_check : 307 | PASS, CONDITIONAL | Barrier, action-window attachments, literal pass, and initial source condition. |
| Lunar assembly | lunar_sync_lock_of_barrier : 371 | PASS, CONDITIONAL | Exact signed headline conclusion, conditional on barrier and two action bounds. |
| Part 2 | lunar_sync_lock_of_cert | DEFERRED BY BRIEF | Requires unavailable LockGraphCert / lockHamExpr; original part-1 brief explicitly permits skipping. |
| Headline | lunar_sync_lock | NOT CLAIMED | Original brief forbids stating/proving it in this package. |

## Extra focus (a): conditional critical path and exact conclusion

The original brief expressly authorizes a distinctly named helper with a LockBarrier and action-bound hypotheses. These helpers do not claim to produce that barrier or stand in for the headline. The signature file itself labels this family “unfrozen helpers; hypotheses = conclusions of pending packages” (line 86); design §1.5 gives the same boundary.

Mechanical extraction found the conclusion of `_of_barrier` (from `∃ z` to `:=`) **byte-identical** to signed `lunar_sync_lock` at SOLockSignatures:72–80. `_check` has the identical conclusion after replacing the signed output literals `21 / 100`, `26 / 1000` by its output parameters `Rψ`, `Rp`. It intentionally generalizes these constants; it is not literally the fixed-literal conclusion before specialization. Neither changes time quantifiers, physical soField, HasDerivAt, the initial value, strict angle bound, orbit/derivative centre, or equality with every global solution. The initial condition uses the same action around lunarSyncOrbit.

The fresh probe copies the entire signed headline statement under a new name, adds only B/hlo/hhi, and closes it with `exact lunar_sync_lock_of_barrier B hlo hhi q₀ p₀ φ₀ h₀`. It elaborates at default resource limits.

Binder audit (typing families are individually named below; RULED means the explicit part-1 conditional-helper authorization, not a premise permitted on the final source headline):

| Declaration | Binder | Bin | Authority / meaning |
|---|---|---|---|
| abs_le_of_libAction_lt | Ω | TYPING | Signed real scale. |
| same | I | TYPING | Signed real action cap. |
| same | c | TYPING | Signed centre function. |
| same | hΩ | SOURCE | Signatures:111, positive scale. |
| same | x | TYPING | Signed physical triple. |
| same | h | SOURCE | Signatures:112, action below cap. |
| sqrt_libAction_le | Ω | TYPING | Signatures:117. |
| same | r | TYPING | Signatures:117. |
| same | r' | TYPING | Signatures:117. |
| same | hΩ | SOURCE | Signatures:117. |
| same | c | TYPING | Signatures:117. |
| same | ψ | TYPING | Signatures:117. |
| same | hr | SOURCE | Signatures:118, centre displacement bound. |
| same | hr' | SOURCE | Signatures:118, derivative displacement bound. |
| same | x | TYPING | Signatures:118. |
| _check | Ω | TYPING | Rational scale, design §1.5. |
| same | cs | TYPING | Rational finite centre data. |
| same | lo | TYPING | Rational inner window endpoint. |
| same | hi | TYPING | Rational outer window endpoint. |
| same | Iin | TYPING | Rational initial cap. |
| same | Rψ | TYPING | Rational output angle cap. |
| same | Rp | TYPING | Rational output spin cap. |
| same | Iin' | TYPING | Real barrier inner bound. |
| same | Iout | TYPING | Real barrier outer bound. |
| same | B | RULED | Original brief §3: actual conditional LockBarrier input. Expanded below. |
| same | hlo | RULED | Signatures:329, lo ≤ pLo−disp. |
| same | hhi | RULED | Signatures:330, pHi+disp ≤ hi. |
| same | hlit | RULED | Signatures:331, passing arithmetic verifier. |
| same | q₀ | TYPING | Signed initial position. |
| same | p₀ | TYPING | Signed initial spin. |
| same | φ₀ | TYPING | Signed initial phase. |
| same | h₀ | SOURCE | Signatures:332, generalized initial action condition. |
| _of_barrier | Iin | TYPING | Real barrier inner bound. |
| same | Iout | TYPING | Real barrier outer bound. |
| same | B | RULED | Original brief §3; specialized scale and centre. |
| same | hlo | RULED | Inner action-window attachment. |
| same | hhi | RULED | Outer action-window attachment. |
| same | q₀ | TYPING | Signatures:72. |
| same | p₀ | TYPING | Signatures:72. |
| same | φ₀ | TYPING | Signatures:72. |
| same | h₀ | SOURCE | Signatures:73. |
| lockLiteralCheck_sound | Ω | TYPING | Rational checker input. |
| same | cs | TYPING | Rational checker input list. |
| same | lo | TYPING | Rational checker input. |
| same | hi | TYPING | Rational checker input. |
| same | r₀ | TYPING | Rational checker input. |
| same | r₁ | TYPING | Rational checker input. |
| same | Iin | TYPING | Rational checker input. |
| same | Rψ | TYPING | Rational checker input. |
| same | Rp | TYPING | Rational checker input. |
| same | h | SOURCE | Soundness assertion's sole logical premise: checker passes. |

Top-level counts: TYPING 36, SOURCE 8, RULED 7, STANDING 0, EXCESS 0. Each B expands to P (typing witness), continuous, periodic_α, periodic_φ, invariant, lower, upper, pos; each of the seven logical fields is RULED by the exact signed LockBarrier at signatures:90–102 and the original conditional-helper brief. In particular `invariant` asserts invariance of the boundary graph, not confinement of every initial state or the final quantitative headline. All fields remain obligations of the future barrier producer. LockLiteralFacts is an output, never an assumed input; its five fields are not hidden hypotheses.

Producer/consumer attachment: signed `lockBarrier_of_certV2` (signatures:304–314) returns `Nonempty (LockBarrier (g.Ω:ℝ) (lockCentre g.cs) (g.graph.pLo−disp) (g.graph.pHi+disp))`. Eliminate Nonempty and instantiate `_check` with precisely those endpoints; its hlo/hhi are exactly the signed certificate assembly's attachments. hlit is the independently checked arithmetic premise, not a fact LOCK-GRAPH alone supplies. The concrete `_of_barrier` already supplies hlit using lunar_literalCheck. DATA must additionally identify Ω and cs with lunarOmega/lunarLockCentre and establish `132/10000 ≤ pLo−disp`, `pHi+disp ≤ 163/10000`. The design's projected [0.013238, 0.016258] allows margins 0.000038 and 0.000042 before disp. Those projections do not prove the actual kernel certificate's range. This audit verifies interface compatibility; it does not assert that pending DATA already delivers these facts.

Proof review: the real transfer strictly raises the initial sqrt-action by at most δ; strict h₀ yields strict initial inclusion even though the checker permits `(√Iin+δ)^2 ≤ lo`. Apply the existing lock_confinement with actual centre C² regularity, then bound coordinates at hi and transfer pointwise to ψ*. The final angle estimate uses Rψ+r₀, without adding δ a second time. Existence, all-real-time validity and uniqueness are preserved from lock_confinement.

## Extra focus (b): verifier body and soundness

No unchecked numerical approximation enters the proof. Write A=Σ|c_k|, D=Σ(k+1)|c_k|, R=r₀+A, S=r₁+2πD and S_hi=r₁+2π_hi D. Both sums are nonnegative, S≤S_hi, and signed centre frequencies are in turns (derivative factor 2π).

| Required item | Check / proof at frozen-v1 | Audit |
|---|---|---|
| Positive Ω | line 199, cast at 233 | Positive divisions and sqrt Ω justified. |
| π enclosure | lines 227–231 use pi_gt_d6 and pi_lt_d6 | 0<π_lo<π<π_hi with exact rational endpoints; inequality directions correct. |
| Root candidate signs | lines 221–223, lockSqrtUp_nonneg | All a₁,a₂,b≥0 for every rational input. |
| Root upper bounds | lines 200–201 square-check π_hi Ω≤a₁², π_hi/Ω≤a₂², Iin≤b² | Hence √π√Ω≤a₁, √π/√Ω≤a₂, √Iin≤b. No Newton quality theorem assumed. |
| Tube transfer | line 201 `(b+a₁R+a₂S_hi)^2≤lo` | Nonnegative terms permit monotonic squaring, giving LockLiteralFacts.tube with exact real S. |
| Angle output | line 202 R≤Rψ and hi/(π_lo Ω)≤(Rψ−R)² | Nonnegative gap prevents false acceptance by squaring a negative gap; hi≥0 gives correct denominator comparison. |
| Spin output | line 203 S_hi≤Rp and Ωhi/π_lo≤(Rp−S_hi)² | Same sign guard and denominator argument; substitute S≤S_hi. |
| Strict synchronous angle | line 203 Rψ+r₀<1/4 | Exactly LockLiteralFacts.angle, then triangle inequality around ψ*. |
| Concrete lunar arithmetic | lines 297–300 | Verifier itself proved true by decide +kernel, independently repeated in probe. |

Every safety inequality of design §1.4 and the §7 literal-check contract is covered. The design's strict tube selection rule is relaxed to ≤ in this sufficient checker; strict initial action makes this sound and slightly more general. The checker verifies compatibility, not the *optimality* of the design's decimal rounding rules. No theorem claims optimality. Design §7 numerical support, decay and certificate threshold projections are not asserted or independently certified here.

Definition classification: lockCentreAbs and lockCentreDAbs are literal whole-list sums. getD is only used on List.range cs.length; defaults are never read out of bounds. lockNatSqrt is total structural recursion on fuel, including its explicit x=0 branch. lockSqrtUp maps every rational input to a nonnegative finite approximation using num.toNat; negative inputs and finite-fuel accuracy are not silently treated as mathematical sqrt. Its only mathematical role beyond nonnegativity is checked again by the verifier's squared inequalities. lockPiLo/Hi and lunarOmega are exact rational constants. lockLiteralCheck is an executable rational conjunction; rational division is total, and Ω>0 guards all accepted divisions involving Ω. LockLiteralFacts is a transparent proposition collecting the five proved output inequalities; unused r₁ in its parameter list is harmless. There is no choice-defined object, junk fallback relied on by a theorem, or deferred definition characterization among the new definitions.

Adversarial second pass challenged: accepting a negative output gap by squaring (blocked by R≤Rψ and S_hi≤Rp), a bad finite-fuel root (blocked by independent square checks), zero/negative Ω (blocked), incorrect π denominator direction (hi≥0 and π_lo>0 used), the Ω scaling of spin (correct), and loss of strict initial inclusion at equality in tube (strict h₀ preserves it). No mathematical counterexample survived these checks. Positive lunar reduction and four independent negative-input reductions passed in the probe; those negative examples are controls, not claims that each rejects solely for one conjunct.

## Extra focus (c): three added signs

The new body adds `0 ≤ r₀`, `0 ≤ r₁`, `0 ≤ hi` (line 199), explicitly disclosed in the handoff. The signed checker body was `sorry`; this is an implementation choice, not a changed signed type or new theorem binder. The checks conservatively restrict acceptance and are used in soundness for nonnegative transfer radii and monotonic division. All hold for the lunar literals, whose full check passes. A negative purported orbit radius cannot bound an absolute value; a negative hi cannot bound the positive barrier action. Thus these guards exclude no physically applicable certificate. They do not assume any final confinement conclusion. Accepted deviation; no source erratum.

## Verification receipts

All Lean/Lake commands were serialized, with LEAN_NUM_THREADS=1 and nice -n 5. No budget override, full rebuild or cache operation was used.

Targeted gated build:

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-lockasm KAM.SpinOrbit.Lock.Assembly
```

Exit 0; wrapper runs `nice -n 5 lake build`:

```text
[inp-gate] slot 3 acquired 17:26:19 for KAM.SpinOrbit.Lock.Assembly
Build completed successfully (2962 jobs).
```

Inherited replay warnings: KAM/ODE/Exit.lean:36 unused section variable `[NormedSpace ℝ E]`; KAM/Certificate/Expr/Basic.lean:85 variable hS not explicitly referenced. No warning in Assembly.lean.

Exact-statement, body, reduction and axiom probe:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/LockASM1Audit.lean
```

Exit 0, no errors/warnings. Probe SHA256 `2c1dcdf4977249decdce590e7e67e95ebf6ed64bb0ac65a90723a7f917e81572`. Mechanical comparisons: both signed theorem headers identical; lunarOmega and lockLiteralCheck types identical; lunarOmega body checked by rfl; headline conclusion byte-identical; generic conclusion identical after output-parameter substitution. Probe repeats the positive literal check with `decide +kernel`, and checks rejection for Ω=0 and representative negative r₀/r₁/hi inputs. Probe deleted after verification.

`#print axioms` was run for all 22 inventory declarations. Exact output classification: `lockNatSqrt` “does not depend on any axioms”; each of the other 21 “depends on axioms: [propext, Classical.choice, Quot.sound]”. In particular both signed transfer theorems, lockLiteralCheck_sound, lunar_literalCheck and both conditional assembly theorems have exactly those three foundational dependencies; no sorryAx, native-decide trust or project axiom.

Kernel replay:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.Lock.Assembly
```

Exit 0, one invocation:

```text
replaying KAM.SpinOrbit.Lock.Assembly
```

Short names:

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-lockasm KAM.SpinOrbit.Lock.Assembly
```

Exit 0: `short-name check OK (no reused public short name)`.

Protected-path check:

```sh
git diff --quiet inp...HEAD -- KAM/Frozen manifest KAM.lean KAM/Root README.md
```

Exit 0, no output. Recursive import inspection reaches 57 KAM modules, including 17 frozen definition modules, all manifest state SEALED. No provider or DRAFT_SORRY theorem is imported. No new frozen export or provider exists in this slice. Direct imports are Confine, PO.Orbit, Coords.Maps and Mathlib.Analysis.Real.Pi.Bounds.

Assembly is 389 lines with maximum Unicode width 100; copyright, module, public imports, docstring and exposed public noncomputable section are present. No forbidden proof escape, resource override, EuclideanSpace, native_decide or harmful root shadow found.

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the expected generated-root complaint explicitly allowed by the audit brief:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py (KAM/Root/SpinOrbit.lean)
check_lean_modules: PASS (1640 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

No generated file was edited.

Whitespace check:

```sh
git diff --check inp...HEAD
```

Exit **2**:

```text
KAM/SpinOrbit/Lock/Assembly.lean:248: trailing whitespace.
+  refine ⟨hΩr, ?_, ?_, ?_, 
```

## Findings, errata and closeout

N1 (minor hygiene, survived separate mechanical recheck): frozen-v1 Assembly.lean:248 ends with a space, quoted above. Suggested owner repair: remove trailing whitespace. No production edit made by this auditor. This is not a mathematical or signed-interface defect.

N2 (allowed integration note): generated root must be regenerated by the orchestrator, not this report-only auditor. Record the actual lint receipt above independently of compilation.

N3 (retained boundary): LOCK-GRAPH/DATA must produce the real barrier, identity attachments and action window before the helper can close the headline. The helpers are complete for this part-1 brief; the final certificate-to-headline theorem is outside it. No N=65 kernel certificate success is inferred from a literal checker success.

No suspected pinned-source erratum, blueprint contradiction, extra unapproved hypothesis, changed carrier, missing safety inequality or weakened signed conclusion found. The original design's “proofs pending” numerical prose does not override the current proved conditional results. The only implementation deviation is the disclosed sign checks; the ≤ tube test is a sound generalization discussed above. Report-only scope and original part-1 skip authorization were maintained. All 22 new named public declarations were inventoried, and the mathematical and verification boundaries are explicit.

Workflow memory was used only for the serialized audit/checklist convention; every package-specific fact above was freshly checked.

<oai-mem-citation>
<citation_entries>
MEMORY.md:49-60|note=[serialized package audit workflow and generated root exception]
</citation_entries>
<rollout_ids>
01a1814a-d083-7040-90e4-beafe8050729
</rollout_ids>
</oai-mem-citation>
