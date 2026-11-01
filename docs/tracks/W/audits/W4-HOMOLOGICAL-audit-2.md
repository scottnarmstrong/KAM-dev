# W4-HOMOLOGICAL independent audit 2

Verdict: **PASS WITH NOTES for the round-2 tight delta. F1 and F2 are resolved at the source-facing interfaces reviewed here.** This accepts the eight-file repair at `7155ce2c`; it does not re-audit unchanged W4 mathematics, certify W5, or approve a frozen seal/provider. There is no W4 provider or frozen anchor in this delta.

## Scope and reproducible identity

Auditor: `maud-wpja-2`; date: 2026-10-31. Worktree `/root/code/KAM-inp-wpja` resolves to `/mnt/HC_Volume_106379410/kam-w/KAM-inp-wpja`. Entry HEAD is `7155ce2c8cbdd55b5c187eda54f2d2c25dfa8bca`, with a clean tracked worktree. Round-1 baseline is `7de5b4e0b026248276662eddf40672717df509c8`. `inp` is `ba270772d4dfe54965e03af2033bd21182545318`; merge-base with HEAD is `9c6d9128c2032acd1fb764896a149d5153119206`.

Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the round-1 report (especially F1 and F2), and the handoff's Round 2 section. Applied the lean-statement-audit binder/carrier/characterization checks to the changed interfaces. The user's tight-delta scope and D53 command/lint restrictions control over the generic brief. No subagents, implementation edits, git mutations, or source repairs.

Performed `git diff inp...HEAD` for package context and `git diff 7de5b4e0 7155ce2c -- KAM/Wave/Homological` for the actual review: **8 files, 281 insertions, 76 deletions**. `KAM/Wave/KamStep` is excluded from mathematical review; only a textual consumer-name search was made to check the handoff's no-citation claim. No unchanged theorem was re-audited. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.

Source comparisons: `blueprint-W/parts/w4-homological.tex:490–549` (weak pairing/bracket and guard), `:630–658` (Lemma 1 premises and conclusions), and only the generalization setting in `blueprint-W/parts/w5-kamstep.tex`, `bpW:w5:w4-general` / `bpW:w5:freq`. W4 blueprint SHA256: `d5c2d6de2b8317b34fc0745600b48616345db1e45acd3d6ea3b5742ac71a6baa`, matching round 1. The round-1 treatment of the generalized equation's explicit `1 ≤ p+pb` domain condition is retained, not reopened.

| Changed file under KAM/Wave/Homological | Physical lines | SHA256 |
|---|---:|---|
| Lemma1.lean | 188 | `5308dc762b010acee2f4e92b2c7511e978e395623a7248ac7d00bd20faa718d0` |
| LemmaOneAll.lean | 266 | `28324ff7ab62f4ae61bd4b0442cd53086de4de4a39b49655d71d9495cf8a38d2` |
| LemmaOneBounds.lean | 292 | `05c7152315bdd8ea5f35c1042877e9041b83c7ebebc77496a4dd77f7b6891fd7` |
| LemmaOneEquation.lean | 360 | `c56113984fbd158d3e8bf0c2d9e6f64aae6d5aeacf46261ae538b3ebb622ddb9` |
| LemmaOneFin.lean | 112 | `2ad37b6f42e9eedf6522efe55f03f5e0ee83274478d5736b3f5a178c4b971b25` |
| Lie.lean | 207 | `c3307b1b9b49ae9d8627699adc4f12b49484a94f49c98e1e5f6fbb603c7b928f` |
| LieDeriv.lean | 281 | `c56922d7c992421b7c1a3d46e5c3b2fc2e509b63e3e153199e79586fcc77b4a3` |
| PPlusOne.lean | 380 | `24e38060b11aa5c70b1d5108262671f0885077edb62f230a3cbaab16c8f84283` |

## F1: resolved source-domain pairing interfaces

`Lie.lean:119–145` now requires `Summable (fun j => x j * x' j)` for `homPair0` and both product-series summability proofs for `homLieSeq`, `homWeakBracket`, and `homWeakBracket_eq_neg_lieN`. The weak bracket constructs the reversed, scalar-multiplied pairing evidence with `homSummable_weak_left`; neither pairing is silently left divergent. The signs remain exactly `-Fθω - i⟨Ωzb,Fzb⟩ + i⟨Ωz,Fz⟩ = -L_N F`.

`homPair0_hasSum` proves the defining series actually converges to the exported pairing. Uniqueness of that value follows from `HasSum.unique`; evidence choice cannot change it (also definitionally, by proof irrelevance). Thus the former constant-one divergent example no longer inhabits the source-domain API. There is no need to construct that old counterexample again.

`LemmaOneFin.lean:41–57` defines `HomOmegaCarrier` as summability of the displayed representative series for every `c,z : HomL2`; `homPairOmega_gen` requires that evidence and `homPairOmega_hasSum_gen` proves its convergent-sum characterization. `LemmaOneEquation.lean:62–78` similarly requires the carrier for `homLieN_gen`; `homLieN_gen_eq` unfolds it to exactly the two evidence-bearing pairings, with the original period-one factor and signs.

The carrier is paid by proofs, not added to the source Lemma 1 premises: `homOmegaCarrier_of_bound` (`LemmaOneAll.lean:176`) transfers the existing bounded diagonal pairing's summability term by term under the frequency bound and `1 ≤ p+pb`. `homOmegaCarrier_of_guard` (`LieDeriv.lean:121`) does the same through the guarded normal-form CLM and the embedded smoothing gradient. In the latter, the new termwise lemma cancels the weight ratio with nonzero weights; it does not assert convergence without a supplier. `homLemma_lie_iv_gen` now concludes with the evidence-bearing `homLieN_gen` using this guard supplier. Its proof's reduction to the raw formula preserves that evidence-bearing statement.

**Visibility note:** “internal” means the explicitly named/documented `Raw` implementation layer, not Lean `private`: these declarations remain publicly visible. Their totalized semantics are explicitly disclosed and are not accepted as source pairings. The two `p+1` aliases are likewise renamed `homLieNRaw` and `homPairOmegaRaw`. No external production citation of the reviewed raw names was found. The `p+1` derivative corollary still prints `homLieNRaw`, but has the full guard/frequency hypotheses and is a direct application of the evidence-bearing generalized theorem; the carrier proof is constructible from those same arguments. This is a visible implementation-layer corollary, not an unguarded extension of the source object.

## F2: resolved source-premise headline exports

The six original-name exports (three generalized and three `p+1` versions) now take the actual frequency and Melnikov assumptions, source input-field bounds, positivity and parameter membership. They take **no `HomMultBounds`, `HomMultLip`, `hK0`, or `hΩ` gate binder**. Their proofs apply `homMultBounds_of`, `homMultLip_of`, and, for the equation, `homOmega_le` and `homOmegaCarrier_of_bound`. Constants remain `7 + 10*homKS`, `waveBW τ σ / α`, and `Mω + MΩ`; the Lipschitz distance is the actual `‖ξ - ζ‖`. The solutions in the conclusions use the gates produced from those same source inputs.

The former gate-taking versions have distinct `_of_gates_gen` / `_of_gates` names and explicitly CONDITIONAL docstrings. Uses in the new source-facing proofs are legitimate discharge of helper inputs, not a replacement of the source theorem by an assumed conclusion. The finite-support `homLemma1_equation_gen` / `homLemma1_equation` and coefficient equations remain internal conditional steps with raw expressions, as explicitly stated by the round-2 handoff. They are not the all-vector source export reviewed here.

A textual search across KAM for these headline, conditional-headline, and raw-pairing names found **zero uses outside KAM/Wave/Homological**. In particular W5 does not cite the renamed gate-taking helpers as Lemma 1. This is a consumer-name check only; no W5 proof acceptance is implied. Older paragraphs/tables in the handoff predate the Round 2 section; the Round 2 section and actual declarations control this review.

### Expanded logical binder check

S = SOURCE, T = TYPING, A = STANDING, R = RULED, E = EXCESS. The following table enumerates the logical binders/fields of the six source-facing wrappers. Input data are listed separately below. No input is classified by the existence of a producer: gates are absent from these signatures and are produced in the bodies.

| Binder / expanded field | Wrappers | Bin | Source / reason |
|---|---|---|---|
| h.consts_nonneg: 0 ≤ M0 | all six | A | frequency setting, nonnegative bounds |
| h.consts_nonneg: 0 ≤ Mω | all six | A | frequency setting |
| h.consts_nonneg: 0 ≤ MΩ | all six | A | frequency setting |
| h.tail | all six | A | bpW:w5:freq, pointwise j^(1/2) tail bound |
| h.lipOmega | all six | A | bpW:w5:freq, tangential frequency Lipschitz bound |
| h.lipTail | all six | A | bpW:w5:freq, normal tail Lipschitz bound |
| hH: ∀ ξ∈Par, ∀ (k,l)∈homZ, α*homJap(l)/waveA(τ,k) ≤ abs(divisor) | all six | S | bpW:w4:melnikov, Hα; homZ means (k,l) ≠ 0 and sum abs(l) ≤ 2 |
| ha: 0 ≤ a | all six | A | bpW:w4:index |
| hp: 0 ≤ p | all six | A | bpW:w4:index |
| hpb: p ≤ pb | generalized three | A | generalized smoothing setting; broader helper range retained from round 1 |
| hp1: 1 ≤ p+pb | generalized equation | A | explicit generalized pairing-domain restriction retained from round 1; automatic for pb=p+1, p≥0 |
| hr: 0 < r | all six | S | bpW:w4:lemma1 |
| hτ: 0 ≤ τ | all six | S | bpW:w4:lemma1 |
| hα: 0 < α | all six | S | bpW:w4:lemma1 |
| hσ: 0 < σ | all six | S | bpW:w4:lemma1 |
| hσs: σ < s | all six | S | bpW:w4:lemma1 |
| hξ: ξ ∈ Par | all six | S | parameter membership in Lemma 1 |
| hζ: ζ ∈ Par | Lipschitz two | S | second parameter membership |
| hεL: 0 ≤ εL | Lipschitz two | S | nonnegative source Lipschitz bound |
| hX: ∀ θ y z zb, HomDomain(s,r) → homXnorm(R) ≤ ε | field/equation four | S | given input field bound in Lemma 1; not the output bound |
| hX₁: same bound on R₁ | Lipschitz two | S | first source input |
| hX₂: same bound on R₂ | Lipschitz two | S | second source input |
| hXL: same bound on R₁.homSub R₂ with εL*‖ξ-ζ‖ | Lipschitz two | S | source difference-field bound; HomFieldBound unfolds at ComponentsFirst.lean:32–35 |
| hθ: θ ∈ complexStrip 2 (s-σ) | equation two | S | pointwise source equation domain |

Ordinary data binders, all T: `Par, ω, Ω, M0, Mω, MΩ, τ, α, a, p, s, σ, r, ε`; additionally `pb` only for `_gen`; `ξ,R` for field/equation; `θ,y,z,zb` for equation; and `εL,ξ,ζ,R₁,R₂` for Lipschitz. `R`/`R₁`/`R₂ : HomTaylor_gen` retain the previously audited Taylor class (typed components, holomorphy, periodicity, boundedness, symmetric P/P′ and transposed Q on the strip), not a solution or a gate. These unchanged class semantics are inherited from round 1. Finite-dimensional and Hilbert value types are unchanged. There are no new instances hiding proof premises.

| Wrapper | Expanded S | Expanded A | T data binders | R | E |
|---|---:|---:|---:|---:|---:|
| homLemma1_fieldBound_gen | 8 | 9 | 17 | 0 | 0 |
| homLemma1_equation_all_gen | 9 | 10 | 21 | 0 | 0 |
| homLemma1_lipschitz_gen | 12 | 9 | 20 | 0 | 0 |
| homLemma1_fieldBound | 8 | 8 | 16 | 0 | 0 |
| homLemma1_equation_all | 9 | 8 | 20 | 0 | 0 |
| homLemma1_lipschitz | 12 | 8 | 19 | 0 | 0 |

Absent `0 ≤ ε` hypotheses strengthen these wrappers; they do not introduce a gate. Frequency/Melnikov hypotheses in a uniform-only wrapper include standing Lipschitz data that the proof need not use; they belong to the source frequency setting.

For F1's domain interfaces, the sequence values, frequencies, representative vectors and Taylor values are T; the two `Summable` proofs / `HomOmegaCarrier` are T as evidence restricting the object to its actual convergent source domain. They are explicitly discharged in the source-facing equation and derivative statements. The algebraic identity requires no Melnikov estimate or hidden extra proof premise.

## Declaration dispositions and definition classification

| Node / changed declaration(s), namespace KAM.Wave | Verdict | Reason |
|---|---|---|
| homPair0Raw, homPair0Raw_comm | INTERNAL | disclosed totalized sum and renamed algebraic helper |
| homLieSeqRaw, homWeakBracketRaw, homWeakBracketRaw_eq_neg_lieSeqRaw | INTERNAL | renamed totalized implementation expressions/identity |
| homPair0, homPair0_hasSum | PASS | actual convergent bilinear pairing on evidence-bearing domain |
| homLieSeq | PASS | literal source formula using convergent pairings |
| homSummable_weak_left | PASS | transfers summability under reversal/scalar multiplication |
| homWeakBracket, homWeakBracket_eq_neg_lieN | PASS | convergent source formula and exact two summability hypotheses |
| homPairOmegaRaw_gen, homPairOmegaRaw | INTERNAL | disclosed totalized representative sum and specialized alias |
| HomOmegaCarrier | PASS | literal convergence-domain predicate, not a source-result assumption |
| homPairOmega_gen, homPairOmega_hasSum_gen | PASS | domain restricted; convergent-sum characterization |
| homLieNRaw_gen, homLieNRaw | INTERNAL | disclosed totalized formula and specialized alias |
| homLieN_gen, homLieN_gen_eq | PASS | domain restricted, exact expansion to convergent pairings |
| homOmegaCarrier_of_bound | PASS | summability derived from bounded diagonal pairing |
| homNOmega_embed_term | PASS | exact termwise weight transport |
| homNOmega_embed_gen | PASS | renamed raw endpoint, under unchanged guard and growth hypotheses |
| homOmegaCarrier_of_guard | PASS | derives summability for embedded normal-form pairing |
| homLemma_lie_iv_gen; homLemma_lie_iv | PASS WITH NOTE | general theorem uses carrier evidence; specialized corollary displays the raw formula with all sufficient hypotheses retained |
| homLemma1_fieldBound_of_gates_gen; homLemma1_fieldBound_of_gates | CONDITIONAL | distinctly named helper, not accepted as the source-premise statement |
| homLemma1_lipschitz_of_gates_gen; homLemma1_lipschitz_of_gates | CONDITIONAL | same |
| homLemma1_equation_all_of_gates_gen; homLemma1_equation_all_of_gates | CONDITIONAL | same; all-vector conclusion itself uses carrier evidence |
| homLemma1_fieldBound_gen; homLemma1_fieldBound | PASS | gates discharged from source hypotheses |
| homLemma1_lipschitz_gen; homLemma1_lipschitz | PASS | both multiplier gates and difference gate discharged |
| homLemma1_equation_all_gen; homLemma1_equation_all | PASS | multiplier, growth and convergence evidence discharged |
| homPairOmega_fin_gen, homPairOmega_op_fin_gen, homPairOmega_Rz_gen, homPairOmega_Rzb_gen, homLemma1_equation_gen, homLemma1_equation | DELTA PASS | occurrences mechanically renamed to Raw; finite-support mathematics unchanged, not re-audited |
| homPairOmega_eq_clm_gen and continuity proof occurrences | DELTA PASS | raw expression renamed; source-facing enclosing equation now restricts its domain |

Definitions audit, separate from theorem status:

* Raw formulas / aliases: literal implementation sums, deliberately totalized; BODY_MATCH=OK as implementation formulas, PUBLIC_CARRIER=OK only for their disclosed raw meaning, WELL_DEFINEDNESS=N/A_LITERAL, CHARACTERIZATION=N/A_LITERAL, CHOICE_INDEPENDENCE=N/A. Not source-object certification.
* `HomOmegaCarrier`: literal domain predicate; BODY_MATCH=OK, PUBLIC_CARRIER=OK, WELL_DEFINEDNESS=N/A_LITERAL, CHARACTERIZATION=N/A_LITERAL, CHOICE_INDEPENDENCE=N/A, DEFINITION_VERDICT=PASS.
* `homPair0`, `homPairOmega_gen`: BODY_MATCH=OK, PUBLIC_CARRIER=OK, WELL_DEFINEDNESS=OK via supplied summability, CHARACTERIZATION=OK via respective HasSum theorems, CHOICE_INDEPENDENCE=OK via uniqueness of sums/proof irrelevance, DEFINITION_VERDICT=PASS.
* `homLieSeq`, `homWeakBracket`, `homLieN_gen`: literal combinations of those convergent pairings; BODY_MATCH=OK, PUBLIC_CARRIER=OK, WELL_DEFINEDNESS=OK, CHARACTERIZATION=OK by defining formula (and homLieN_gen_eq), CHOICE_INDEPENDENCE=OK by proof irrelevance, DEFINITION_VERDICT=PASS.

There is no new classical selection, fallback branch, source-result structure, or broadened source normalizer in these repaired definitions. Existing representatives/weights were not changed.

## Checks and limitations

All Lean/Lake invocations were serial under D53. No leanchecker replay or launcher name-check rerun was needed for this tight delta. The launcher reportedly ran those checks, but its output is not visible in this turn; **no independently observed replay exit code is claimed here**.

1. Prescribed lint, exact command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpja
```

Observed output and exit status:

```text
check_lean_modules: PASS (3620 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
exit 0
```

The lunar application exception is the linter's declared file-hash-only scope, unrelated to W4. No application was built.

2. Targeted build of the facade importing all eight changed modules:

```sh
/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpja KAM.Wave.Homological.PPlusOne
```

The driver acquired compile slot 1 and ran precisely its D53-capped invocation:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake build KAM.Wave.Homological.PPlusOne
```

Observed final Lake output: `Build completed successfully (3303 jobs).` Warnings were unused variable/tactic and deprecated-name lint messages; no elaboration error or budget override. **The driver process exited 1 despite Lake's success.** Inspection of `w_build.sh` explains the mismatch: on success the final loop-body command is `[ $rc -ne 0 ] && { ...; exit $rc; }`; its false test becomes the script status. This is an infrastructure return-status caveat, not a claimed exit-0 build-driver run. No script was modified and no redundant build was run.

3. Scratch composition/characterization and axiom probe, exact command:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 env LEAN_PATH=.lake/build/lib/lean:/root/code/KAM-inp/.lake/build/lib/lean lake env lean .lake/abi-scratch/maud-wpja-2-probe.lean
```

**Exit 0; no probe errors.** Thirteen examples checked: the six full source-premise wrapper applications; raw-sequence HasSum characterization and evidence independence; weak bracket identity with both summability proofs; representative HasSum characterization; the source-frequency-to-carrier-to-HasSum composition; and uniqueness of both pairing values from arbitrary competing HasSum witnesses. This verifies actual applications and sum values, beyond declaration reachability. The six wrapper examples used the reviewed source-domain signatures and these argument lists:

```lean
homLemma1_fieldBound_gen h hH ha hp hpb hr hτ hα hσ hσs hξ R hX
homLemma1_equation_all_gen h hH ha hp hpb hp1 hr hτ hα hσ hσs hξ R hX hθ y z zb
homLemma1_lipschitz_gen h hH ha hp hpb hr hτ hα hεL hσ hσs hξ hζ R₁ R₂ hX₁ hX₂ hXL
homLemma1_fieldBound h hH ha hp hr hτ hα hσ hσs hξ R hX
homLemma1_equation_all h hH ha hp hr hτ hα hσ hσs hξ R hX hθ y z zb
homLemma1_lipschitz h hH ha hp hr hτ hα hεL hσ hσs hξ hζ R₁ R₂ hX₁ hX₂ hXL
```

Representative exact characterization/uniqueness probe terms:

```lean
example (x y : ℕ+ → ℂ) (h : Summable fun j => x j * y j) {v : ℂ}
    (hv : HasSum (fun j => x j * y j) v) : v = homPair0 x y h :=
  hv.unique (homPair0_hasSum x y h)
example (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) {W : ℕ+ → ℝ}
    (hC : HomOmegaCarrier ha hp hpb W) (c z : HomL2) {v : ℂ}
    (hv : HasSum (fun j => homLamDiag_gen ha (homPP hp hpb) c j * (W j : ℂ) * z j) v) :
    v = homPairOmega_gen ha hp hpb hC c z :=
  hv.unique (homPairOmega_hasSum_gen ha hp hpb hC c z)
```

The probe executed `#print axioms KAM.Wave.<name>` for all 23 added/renamed theorem commands in the delta, plus the two changed guarded derivative exports. **Every one of the following 25 names printed exactly `[propext, Classical.choice, Quot.sound]`:**

- `homLemma1_lipschitz_of_gates_gen`
- `homLemma1_lipschitz_gen`
- `homOmegaCarrier_of_bound`
- `homLemma1_equation_all_of_gates_gen`
- `homLemma1_equation_all_gen`
- `homLemma1_fieldBound_of_gates_gen`
- `homLemma1_fieldBound_gen`
- `homLieN_gen_eq`
- `homPairOmega_hasSum_gen`
- `homPair0Raw_comm`
- `homWeakBracketRaw_eq_neg_lieSeqRaw`
- `homPair0_hasSum`
- `homSummable_weak_left`
- `homWeakBracket_eq_neg_lieN`
- `homNOmega_embed_term`
- `homNOmega_embed_gen`
- `homOmegaCarrier_of_guard`
- `homLemma1_lipschitz_of_gates`
- `homLemma1_equation_all_of_gates`
- `homLemma1_equation_all`
- `homLemma1_fieldBound`
- `homLemma1_lipschitz`
- `homLemma1_fieldBound_of_gates`
- `homLemma_lie_iv_gen`
- `homLemma_lie_iv`

4. Static delta inspection: no added forbidden proof escapes or budget overrides; every changed file has copyright, module command, imports, module docstring and an exposed public noncomputable section. Maximum physical size among changed files: 380 lines, below 1500. A first ad-hoc substring check expected the literal `public section` and therefore printed false for `public noncomputable section`; the corrected syntax-aware check passed all eight, consistent with the prescribed linter. No source edit was made in response. Frozen/manifest/root/README diff is empty. No provider or DRAFT_SORRY import was added.

Scratch probe removed after recording its successful result. Only this report is added to tracked repository content. No kernel replay, global build, root regeneration, test suite expansion, source repair, commit, or push was performed.


## Errata, deviations and closeout

No new suspected pinned-source defect arose from these changes. Round-1 source/generalization notes remain outside the reopened scope; this report does not silently repair or discharge them. The explicit generalized pairing restriction is preserved. No implementation deviation was introduced by this audit.

F1 is closed for the evidence-bearing source interfaces; raw public helper names remain explicitly raw. F2 is closed for the six reviewed original-name exports; conditional finite-support/coefficient helpers remain conditional. Acceptance is **PASS WITH NOTES for this exact tight delta**, not a fresh package-wide proof/anchor closure claim.
