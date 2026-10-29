# SO-EMB independent audit 1

Audit date: 2026-10-29. Worktree: `/root/code/KAM-inp-soemb`.
Audited HEAD: `d69ba137b45027806e70255da6bc7f1ea31ce48e`.
Comparison ref `inp`: `1fc43308cf334826452c28ce5f66a1a2656b91c9`.

## Scope and verdict

**PASS WITH NOTES** for the SO-EMB package. The four signed theorem exports pass their exact
contracts; the embedding/composition slice is complete. This is infrastructure validation, not a
seal of an I/N/P theorem or a lunar certificate. No provider or frozen theorem is being sealed.
The permitted stale generated root is recorded separately below.

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and the complete SO-EMB handoff.
Controlling specification: `/root/code/KAM/docs/tracks/SO/design/SO-LEAN-DESIGN.md`, Revision 7,
§1 items 5–7, §7 SO-EMB row, Appendix A §D; exact signature source:
`/root/code/KAM-inp/.drafts/design/SOSignatures.lean:653–700` (namespace at line 65).
SO-EMB is a certificate infrastructure slice; unrelated I/N/P blueprint nodes and theorem
anchors are not its specifications. The actual frozen definitions and `IG1Body` consumer were
inspected. The user's exact report location overrides the brief's generic main-worktree location.

Reviewed the complete `git diff inp...HEAD`: four new Lean modules (1232 lines) and the new
213-line handoff, with no other changed source paths. The handoff's 1228-line count and
`59fc468f` tip are stale bookkeeping: current ComposeModels/Compose have 432/472 lines and
HEAD adds the audit request. These differences do not alter the signed interface.

| Signed export (prefix `KAM.Certificate.`) | Verdict | Evidence |
|---|---|---|
| `CertEmbedding.differentiable_eval` | PASS | Exact signature; entire on all `Fin n → ℂ`; only `[CertArith α]`. |
| `CertEmbedding.isPrimaryOnStrip` | PASS | Exact signature; arbitrary width and every integer translate. |
| `CertEmbedding.isRealOnReals` | PASS | Exact signature; every real input, no arithmetic-law premise. |
| `Slp.compose_sound` | PASS | Exact signature; exact slot composition and output length, no domain or nonvanishing premise. |

Both signed structures are textually exact, including field order and types. `CertEmbedding.eval`
is textually exact including its full body. The signed `Slp.compose` header is textually exact.
All names live in `KAM.Certificate`, including the nested `CertEmbedding` and `Slp` names.
Fresh Lean probes copied each signed theorem header to a fresh name and proved it by the
original export applied to exactly its explicit binders in order. The compose definition header
was also copied and implemented by its export. Every probe elaborated without resource overrides.
There is no applicable frozen-provider equality probe because this slice has no provider.

## Soundness and definition classification

The embedding denotes the literal primary lift `(θ + (2π)^dU U, (2π)^dA A)`.
`realComp`, `angleAt`, and `actionAt` denote optional components with mathematical zero for
missing data. Degree lists default to the exponent zero. This is defined for every list shape,
integer degree, dimension (including zero), and arithmetic backend. Law-free real-polynomial
semantics supplies periodicity, reality, differentiability and conjugation; it does not assume
backend zero has value zero. A fresh consumer probe derives precisely
`DifferentiableOn ℂ (K.eval n) (complexStrip n ρ) ∧ IsPrimaryOnStrip ... ∧ IsRealOnReals ...`
from these exports, with no law instance. These are the three corresponding premises at
`KAM/Iso/Charts/Inputs.lean:57`. This does not discharge the other IG1Body premises.

The models denote `(2π)^deg` times polynomial plus a sup-norm remainder on the actual open strip.
`zeroModel`, `ratErrUp`, `constModel`, `realCompModel`, `imulItems`, `phaseTermModel`,
`charPhaseModel`, and `shiftModel` are respectively zero, outward conversion error, constants,
optional actions, rounded imaginary integer products, phase contributions, their degree-zero
sum, and exact character shifts with weighted radii. Backend law hypotheses are used exactly
where computed objects need them. `padKey` truncates/pads to the semantic first `n` coordinates;
`toSortedPoly` and `reflectSorted` change representation order while preserving denotation.
Their names do not assert sorting of arbitrary input: ascending half keys are a precision and
performance convention, never a soundness premise.

`isZeroData`, `angleIsZero`, and `normKey` implement a sufficient syntactic zero test and key
normalization, with law-backed proofs of denotation preservation. False negatives merely require
more witnesses. `findKeyIdx` uses exact list equality and returns the first matching position;
`subAdvice`/`forWitness` filter and re-key untrusted product advice. `charExpFun` is the literal
exponential of the angle displacement phase. None is a replacement for a hard analytic premise.

`Witnesses` contains only data. `ComposeState` contains reverse slots, length, two witness
counters and a character cache, with no proof fields. `slotEntry` caches the polynomial weighted
norm. `slot` and `pushSlot` implement indexed reads and one-cons insertion. `mulN` is the model
multiplication formula with supplied norms; it is not claimed sound for arbitrary supplied norms.
`mulN_supNormUp` is definitional equality to the established multiplication when the supplied
norms are correct, and `SlotsEnclose` proves those equalities at every actual use. Its invariant
also carries exact enclosure of every slot and `CacheValid`. These propositions are proved from
empty state through each operation; no conclusion-shaped assumption is added to `compose_sound`.

`charResolve`, `charEntry`, `charSlot`, `composeStep`, `composeOps`, and `Slp.compose` are total
checker computations. Fresh character entries must pass `expWitnessRadius` against the actual
phase model; cached entries carry the same semantic contract. Reflection uses the conjugated
input (which remains in the strip) and conjugates the output, so it is valid for complex angles,
not merely the real slice. Normalization preserves the exponential; the final shift uses the
original padded key. The phase identity is the exact period-one character identity, with all
`2π` factors retained. Exp pins use SO-EXPW's reduced complex exponential path. Inverses use
`invWitness_sound`, deriving nonvanishing on the strip before enclosing the reciprocal.

`composeStep_sound` handles all seven operations; its multiplication case rewrites both cached
norm equalities before using multiplication soundness. Constant models have zero Fourier keys,
so existing `polyProduct` takes the scalar route; `composeTest_scalar` certifies exact radius zero.
The reverse-list invariant preserves earlier values, identifies the new value via
`Slp.val_snoc_self`, and handles all off-program reads. Forward/self references read zero just
as `SlpOp.step` does (`Expr/Slp.lean:52–61`); out-of-dimension actions and requested slots also
match evaluator zero semantics. These defaults are intended total semantics, not junk values.
`composeOps` folds through `Option.bind`, preserving failure even when failed slots are unwanted.
Unused witness data is harmless. A failed direct character check may use a separately checked
negative-key witness; if neither route succeeds, composition fails. Thus fail-closed means no
unchecked witness can support success, not that one failed candidate prevents a valid alternative.

All `composeTest*` definitions are concrete rational fixtures and witness approximations,
including finite Bessel sums and rounded coefficients. Their approximation formulas need no
external analytic hypothesis: successful checker reductions plus the general soundness contract
supply the rigorous conclusion. Tests cover all seven operations, mixed degrees, scalar products,
conjugation, normalization in dimension two, missing witnesses, failed pins and off-program reads.
All 12 computational tests use `decide +kernel`; the thirteenth theorem instantiates the soundness
contract. No native evaluation is trusted.

## Declaration-by-declaration review

Every declaration below is public under `KAM.Certificate`. Locations are relative to the worktree.
“Data/algorithm” classifies an intended total object; “contract” classifies a proved semantic or
structural property. Each helper has its own name and does not stand in for a signed theorem.

| Node | Lean declaration (after `KAM.Certificate.`) | Location | Verdict | Classification / reason |
|---|---|---|---|---|
| embedding | `CertEmbedding` | `KAM/Certificate/Embedding.lean:32` | PASS | Data structure; no assumed proof fields. |
| embedding | `CertEmbedding.eval` | `KAM/Certificate/Embedding.lean:38` | PASS | Data/algorithm; intended total semantics as classified above. |
| embedding | `realComp` | `KAM/Certificate/Embedding.lean:50` | PASS | Data/algorithm; intended total semantics as classified above. |
| embedding | `CertEmbedding.angleAt` | `KAM/Certificate/Embedding.lean:54` | PASS | Data/algorithm; intended total semantics as classified above. |
| embedding | `CertEmbedding.actionAt` | `KAM/Certificate/Embedding.lean:58` | PASS | Data/algorithm; intended total semantics as classified above. |
| embedding | `CertEmbedding.eval_fst` | `KAM/Certificate/Embedding.lean:61` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| embedding | `CertEmbedding.eval_snd` | `KAM/Certificate/Embedding.lean:64` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| embedding | `differentiable_realComp` | `KAM/Certificate/Embedding.lean:67` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| embedding | `realComp_add_int` | `KAM/Certificate/Embedding.lean:74` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| embedding | `realComp_real` | `KAM/Certificate/Embedding.lean:78` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| embedding | `CertEmbedding.differentiable_eval` | `KAM/Certificate/Embedding.lean:89` | PASS | Exact signed contract; fresh explicit-binder probe passed. |
| embedding | `CertEmbedding.isPrimaryOnStrip` | `KAM/Certificate/Embedding.lean:96` | PASS | Exact signed contract; fresh explicit-binder probe passed. |
| embedding | `CertEmbedding.isRealOnReals` | `KAM/Certificate/Embedding.lean:108` | PASS | Exact signed contract; fresh explicit-binder probe passed. |
| embedding | `character_conj` | `KAM/Certificate/Embedding.lean:127` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| embedding | `CertRealPoly.eval_conj` | `KAM/Certificate/Embedding.lean:134` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| embedding | `realComp_conj` | `KAM/Certificate/Embedding.lean:143` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| embedding | `CertEmbedding.angleAt_conj` | `KAM/Certificate/Embedding.lean:152` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| embedding | `differentiable_angleAt` | `KAM/Certificate/Embedding.lean:156` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `zeroModel` | `KAM/Certificate/Expr/ComposeModels.lean:49` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `ratErrUp` | `KAM/Certificate/Expr/ComposeModels.lean:52` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `padKey` | `KAM/Certificate/Expr/ComposeModels.lean:56` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `constModel` | `KAM/Certificate/Expr/ComposeModels.lean:59` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `CertRealPoly.toSortedPoly` | `KAM/Certificate/Expr/ComposeModels.lean:66` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `realCompModel` | `KAM/Certificate/Expr/ComposeModels.lean:71` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `imulItems` | `KAM/Certificate/Expr/ComposeModels.lean:76` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `phaseTermModel` | `KAM/Certificate/Expr/ComposeModels.lean:81` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `charPhaseModel` | `KAM/Certificate/Expr/ComposeModels.lean:89` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `CertRealPoly.isZeroData` | `KAM/Certificate/Expr/ComposeModels.lean:97` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `CertEmbedding.angleIsZero` | `KAM/Certificate/Expr/ComposeModels.lean:100` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `CertEmbedding.normKey` | `KAM/Certificate/Expr/ComposeModels.lean:107` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `CertPoly.reflectSorted` | `KAM/Certificate/Expr/ComposeModels.lean:111` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `shiftModel` | `KAM/Certificate/Expr/ComposeModels.lean:114` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `findKeyIdx` | `KAM/Certificate/Expr/ComposeModels.lean:118` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `subAdvice` | `KAM/Certificate/Expr/ComposeModels.lean:123` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `ModelConfig.forWitness` | `KAM/Certificate/Expr/ComposeModels.lean:130` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `charExpFun` | `KAM/Certificate/Expr/ComposeModels.lean:136` | PASS | Data/algorithm; intended total semantics as classified above. |
| slot models | `character_certKeyFun_nil` | `KAM/Certificate/Expr/ComposeModels.lean:146` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `findKeyIdx_mem` | `KAM/Certificate/Expr/ComposeModels.lean:149` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `modePhase_add` | `KAM/Certificate/Expr/ComposeModels.lean:164` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `exp_I_modePhase` | `KAM/Certificate/Expr/ComposeModels.lean:168` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `certKeyFun_padKey` | `KAM/Certificate/Expr/ComposeModels.lean:174` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `padKey_length` | `KAM/Certificate/Expr/ComposeModels.lean:178` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `exp_I_modePhase_eval` | `KAM/Certificate/Expr/ComposeModels.lean:181` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `CertPoly.eval_reflectSorted` | `KAM/Certificate/Expr/ComposeModels.lean:187` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `toDeg_deg` | `KAM/Certificate/Expr/ComposeModels.lean:191` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `conj_mem_complexStrip` | `KAM/Certificate/Expr/ComposeModels.lean:198` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `charExpFun_neg_conj` | `KAM/Certificate/Expr/ComposeModels.lean:203` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `zeroModel_encloses` | `KAM/Certificate/Expr/ComposeModels.lean:215` | PASS | Contract; structural invariant or exact function enclosure. |
| slot models | `ratErrUp_ge` | `KAM/Certificate/Expr/ComposeModels.lean:220` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `constModel_encloses` | `KAM/Certificate/Expr/ComposeModels.lean:231` | PASS | Contract; structural invariant or exact function enclosure. |
| slot models | `CertRealPoly.eval_toSortedPoly` | `KAM/Certificate/Expr/ComposeModels.lean:250` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `realCompModel_encloses` | `KAM/Certificate/Expr/ComposeModels.lean:260` | PASS | Contract; structural invariant or exact function enclosure. |
| slot models | `imulItems_spec` | `KAM/Certificate/Expr/ComposeModels.lean:270` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `phaseTermModel_encloses` | `KAM/Certificate/Expr/ComposeModels.lean:295` | PASS | Contract; structural invariant or exact function enclosure. |
| slot models | `charPhaseModel_aux` | `KAM/Certificate/Expr/ComposeModels.lean:324` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `charPhaseModel_encloses` | `KAM/Certificate/Expr/ComposeModels.lean:351` | PASS | Contract; structural invariant or exact function enclosure. |
| slot models | `CertRealPoly.eval_of_isZeroData` | `KAM/Certificate/Expr/ComposeModels.lean:369` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `CertEmbedding.angleAt_of_angleIsZero` | `KAM/Certificate/Expr/ComposeModels.lean:376` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `charExpFun_normKey` | `KAM/Certificate/Expr/ComposeModels.lean:387` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `charExpFun_reflectSorted` | `KAM/Certificate/Expr/ComposeModels.lean:404` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| slot models | `shiftModel_encloses` | `KAM/Certificate/Expr/ComposeModels.lean:415` | PASS | Contract; structural invariant or exact function enclosure. |
| composition | `Witnesses` | `KAM/Certificate/Expr/Compose.lean:51` | PASS | Data structure; no assumed proof fields. |
| composition | `CertModel.mulN` | `KAM/Certificate/Expr/Compose.lean:61` | PASS | Data/algorithm; intended total semantics as classified above. |
| composition | `ComposeState` | `KAM/Certificate/Expr/Compose.lean:73` | PASS | Data structure; no assumed proof fields. |
| composition | `slotEntry` | `KAM/Certificate/Expr/Compose.lean:81` | PASS | Data/algorithm; intended total semantics as classified above. |
| composition | `pair_snd` | `KAM/Certificate/Expr/Compose.lean:83` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| composition | `slotEntry_fst` | `KAM/Certificate/Expr/Compose.lean:86` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| composition | `slotEntry_snd` | `KAM/Certificate/Expr/Compose.lean:89` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| composition | `ComposeState.slot` | `KAM/Certificate/Expr/Compose.lean:94` | PASS | Data/algorithm; intended total semantics as classified above. |
| composition | `ComposeState.pushSlot` | `KAM/Certificate/Expr/Compose.lean:99` | PASS | Data/algorithm; intended total semantics as classified above. |
| composition | `charResolve` | `KAM/Certificate/Expr/Compose.lean:105` | PASS | Data/algorithm; intended total semantics as classified above. |
| composition | `charEntry` | `KAM/Certificate/Expr/Compose.lean:121` | PASS | Data/algorithm; intended total semantics as classified above. |
| composition | `charSlot` | `KAM/Certificate/Expr/Compose.lean:132` | PASS | Data/algorithm; intended total semantics as classified above. |
| composition | `composeStep` | `KAM/Certificate/Expr/Compose.lean:140` | PASS | Data/algorithm; intended total semantics as classified above. |
| composition | `composeOps` | `KAM/Certificate/Expr/Compose.lean:171` | PASS | Data/algorithm; intended total semantics as classified above. |
| composition | `Slp.compose` | `KAM/Certificate/Expr/Compose.lean:180` | PASS | Data/algorithm; intended total semantics as classified above. |
| composition | `CertModel.mulN_supNormUp` | `KAM/Certificate/Expr/Compose.lean:193` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| composition | `CacheValid` | `KAM/Certificate/Expr/Compose.lean:198` | PASS | Data/algorithm; intended total semantics as classified above. |
| composition | `ComposeState.SlotsEnclose` | `KAM/Certificate/Expr/Compose.lean:203` | PASS | Data/algorithm; intended total semantics as classified above. |
| composition | `ComposeState.slotsEnclose_nil` | `KAM/Certificate/Expr/Compose.lean:212` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| composition | `ComposeState.SlotsEnclose.pushSlot` | `KAM/Certificate/Expr/Compose.lean:226` | PASS | Contract; denotation identity, bound, or structural fact used above. |
| composition | `charResolve_sound` | `KAM/Certificate/Expr/Compose.lean:267` | PASS | Contract; structural invariant or exact function enclosure. |
| composition | `charEntry_sound` | `KAM/Certificate/Expr/Compose.lean:310` | PASS | Contract; structural invariant or exact function enclosure. |
| composition | `charSlot_sound` | `KAM/Certificate/Expr/Compose.lean:342` | PASS | Contract; structural invariant or exact function enclosure. |
| composition | `composeStep_sound` | `KAM/Certificate/Expr/Compose.lean:369` | PASS | Contract; structural invariant or exact function enclosure. |
| composition | `composeOps_sound` | `KAM/Certificate/Expr/Compose.lean:434` | PASS | Contract; structural invariant or exact function enclosure. |
| composition | `Slp.compose_sound` | `KAM/Certificate/Expr/Compose.lean:452` | PASS | Exact signed contract; fresh explicit-binder probe passed. |
| tests | `composeTestW` | `KAM/Certificate/Tests/Compose.lean:37` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTest_weight` | `KAM/Certificate/Tests/Compose.lean:39` | PASS | Kernel-decided fixture check. |
| tests | `composeTestPi` | `KAM/Certificate/Tests/Compose.lean:41` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTest_pi` | `KAM/Certificate/Tests/Compose.lean:43` | PASS | Kernel-decided fixture check. |
| tests | `composeTestRound` | `KAM/Certificate/Tests/Compose.lean:46` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTestJ` | `KAM/Certificate/Tests/Compose.lean:49` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTestIPow` | `KAM/Certificate/Tests/Compose.lean:54` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTestRange` | `KAM/Certificate/Tests/Compose.lean:62` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTestCharE` | `KAM/Certificate/Tests/Compose.lean:65` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTestCos` | `KAM/Certificate/Tests/Compose.lean:70` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTestK` | `KAM/Certificate/Tests/Compose.lean:73` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTestProg` | `KAM/Certificate/Tests/Compose.lean:76` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTestInv` | `KAM/Certificate/Tests/Compose.lean:81` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTestWit` | `KAM/Certificate/Tests/Compose.lean:85` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTestCfg` | `KAM/Certificate/Tests/Compose.lean:89` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTestRun` | `KAM/Certificate/Tests/Compose.lean:94` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTest_all` | `KAM/Certificate/Tests/Compose.lean:98` | PASS | Kernel-decided fixture check. |
| tests | `composeTest_scalar` | `KAM/Certificate/Tests/Compose.lean:104` | PASS | Kernel-decided fixture check. |
| tests | `composeTest_conj` | `KAM/Certificate/Tests/Compose.lean:110` | PASS | Kernel-decided fixture check. |
| tests | `composeTest_noChar` | `KAM/Certificate/Tests/Compose.lean:116` | PASS | Kernel-decided fixture check. |
| tests | `composeTest_noExp` | `KAM/Certificate/Tests/Compose.lean:120` | PASS | Kernel-decided fixture check. |
| tests | `composeTest_noInv` | `KAM/Certificate/Tests/Compose.lean:124` | PASS | Kernel-decided fixture check. |
| tests | `composeTest_pinFail` | `KAM/Certificate/Tests/Compose.lean:129` | PASS | Kernel-decided fixture check. |
| tests | `composeTest_offProgram` | `KAM/Certificate/Tests/Compose.lean:133` | PASS | Kernel-decided fixture check. |
| tests | `composeTestK2` | `KAM/Certificate/Tests/Compose.lean:141` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTestProg2` | `KAM/Certificate/Tests/Compose.lean:144` | PASS | Data/algorithm; intended total semantics as classified above. |
| tests | `composeTest_normKey` | `KAM/Certificate/Tests/Compose.lean:146` | PASS | Kernel-decided fixture check. |
| tests | `composeTest_n2` | `KAM/Certificate/Tests/Compose.lean:150` | PASS | Kernel-decided fixture check. |
| tests | `composeTest_sound` | `KAM/Certificate/Tests/Compose.lean:160` | PASS | General enclosure contract instantiated on fixture. |

## Independent validation

Validation receipts are recorded below.
All Lean/Lake invocations below were serialized and inherited `LEAN_NUM_THREADS=1`; Lean
commands ran at niceness 5, and the targeted build used the required compile gate. No clean,
update, cache download, frozen-file change, generated-root regeneration, or state-changing Git
command was performed. Only the report is added to the repository. Temporary audit probes and
logs under `.lake/abi-scratch/` were removed after recording their outputs here.

### Targeted build — exit 0

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-soemb KAM.Certificate.Embedding KAM.Certificate.Expr.ComposeModels \
  KAM.Certificate.Expr.Compose KAM.Certificate.Tests.Compose
```

```text
[inp-gate] slot 1 acquired 19:57:44 for KAM.Certificate.Embedding KAM.Certificate.Expr.ComposeModels KAM.Certificate.Expr.Compose KAM.Certificate.Tests.Compose
⚠ [2840/2961] Replayed KAM.Certificate.Arith.PiHigh
warning: KAM/Certificate/Arith/PiHigh.lean:218:8: This simp argument is unused:
  Nat.succ_eq_add_one
⚠ [2950/2961] Replayed KAM.Certificate.Expr.Basic
warning: KAM/Certificate/Expr/Basic.lean:85:5: Variable name `hS` is not explicitly referenced.
Build completed successfully (2961 jobs).
```

The omitted warning hints only suggest removing unused bindings or disabling the corresponding
linter; no such change or option was used. Neither warning is in an audited file.

### Signature, seal-body-shaped, IG1Body and axiom probe — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOEMBAudit.lean
```

The probe imported `KAM.Certificate.Tests.Compose` and opened `KAM KAM.Certificate`.
Its four fresh theorem declarations used the exact signed headers and these explicit bodies:

```lean
by exact CertEmbedding.differentiable_eval n K
by exact CertEmbedding.isPrimaryOnStrip n K ρ
by exact CertEmbedding.isRealOnReals n K
by exact Slp.compose_sound p K wit hW cfg hpe wanted h
```

The consumer probe, also inside `namespace KAM.Certificate`, was:

```lean
example {α : Type} [CertArith α] (n : ℕ) (K : CertEmbedding α) (ρ : ℝ) :
    DifferentiableOn ℂ (K.eval n) (complexStrip n ρ) ∧
      IsPrimaryOnStrip (K.eval n) ρ ∧ IsRealOnReals (K.eval n) :=
  ⟨(K.differentiable_eval n).differentiableOn,
    K.isPrimaryOnStrip n ρ, K.isRealOnReals n⟩
```

A separate Python comparison checked exact (not whitespace-normalized) theorem headers,
structure declarations, the entire eval definition, and the compose header against the signed
file. All eight comparisons passed. The probe then ran `#print axioms` for all 63 theorem
names found in the four modules. Exact axiom output:

```text
'KAM.Certificate.CertEmbedding.eval_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertEmbedding.eval_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.differentiable_realComp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.realComp_add_int' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.realComp_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertEmbedding.differentiable_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertEmbedding.isPrimaryOnStrip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertEmbedding.isRealOnReals' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.character_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertRealPoly.eval_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.realComp_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertEmbedding.angleAt_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.differentiable_angleAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.character_certKeyFun_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.findKeyIdx_mem' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.modePhase_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.exp_I_modePhase' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.certKeyFun_padKey' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.padKey_length' depends on axioms: [propext, Quot.sound]
'KAM.Certificate.exp_I_modePhase_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertPoly.eval_reflectSorted' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.toDeg_deg' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.conj_mem_complexStrip' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.charExpFun_neg_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.zeroModel_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ratErrUp_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.constModel_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertRealPoly.eval_toSortedPoly' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.realCompModel_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.imulItems_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.phaseTermModel_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.charPhaseModel_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.charPhaseModel_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertRealPoly.eval_of_isZeroData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertEmbedding.angleAt_of_angleIsZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.charExpFun_normKey' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.charExpFun_reflectSorted' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.shiftModel_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.pair_snd' does not depend on any axioms
'KAM.Certificate.slotEntry_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.slotEntry_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.CertModel.mulN_supNormUp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ComposeState.slotsEnclose_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.ComposeState.SlotsEnclose.pushSlot' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.charResolve_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.charEntry_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.charSlot_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeStep_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeOps_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.compose_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_weight' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_pi' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_scalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_conj' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_noChar' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_noExp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_noInv' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_pinFail' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_offProgram' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_normKey' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_n2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.composeTest_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Kernel replay — exit 0

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Certificate.Embedding KAM.Certificate.Expr.ComposeModels \
  KAM.Certificate.Expr.Compose KAM.Certificate.Tests.Compose
```

```text
replaying KAM.Certificate.Tests.Compose
replaying KAM.Certificate.Expr.Compose
replaying KAM.Certificate.Expr.ComposeModels
replaying KAM.Certificate.Embedding
```

### Static hygiene and namespace checks

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py \
  /root/code/KAM-inp-soemb KAM.Certificate.Embedding KAM.Certificate.Expr.ComposeModels \
  KAM.Certificate.Expr.Compose KAM.Certificate.Tests.Compose
```

Exit 0: `short-name check OK (no reused public short name)`. The checker covers KAM,
Mathlib and branch integration collisions, exempting design-signed names. Every explicit
namespace in the four files is `KAM.Certificate`; no root declaration or harmful shadow was found.

```sh
rg -n '\b(sorry|admit|axiom|unsafe|opaque|native_decide|EuclideanSpace)\b|set_option' \
  KAM/Certificate/Embedding.lean KAM/Certificate/Expr/ComposeModels.lean \
  KAM/Certificate/Expr/Compose.lean KAM/Certificate/Tests/Compose.lean
```

Exit 1, no matches (the expected successful negative search).

| File | Lines | Maximum characters per line |
|---|---:|---:|
| `KAM/Certificate/Embedding.lean` | 162 | 100 |
| `KAM/Certificate/Expr/ComposeModels.lean` | 432 | 100 |
| `KAM/Certificate/Expr/Compose.lean` | 472 | 99 |
| `KAM/Certificate/Tests/Compose.lean` | 166 | 98 |

All four have copyright, `module`, public imports, module docstrings and public sections.
The three implementation files use `@[expose] public noncomputable section` for unfoldable
bodies. The tests use `public section`. No resource override, prohibited ambient carrier,
proof escape or native decision was found.

A recursive local import scan found 57 KAM modules, no provider, and only these 11 frozen
modules: `ComplexStrip`, `DotC`, `GramMatrix`, `HamiltonianVectorFieldC`, `InvarianceError`,
`IsPrimaryOnStrip`, `IsRealOnReals`, `NormalFrame`, `OmegaZero`, `Torsion`, `TorsionAverage`,
all under `KAM/Frozen/Defs/`. Each is SEALED in the manifest. No DRAFT_SORRY theorem enters
the package's import closure; the axiom output independently excludes `sorryAx`.

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
git diff --check
```

Each exited 0 with empty output. At final handoff, `git status --short` contains only the
new audit report. No pre-existing tracked worktree changes were present.

### Source lint and frozen/ABI guards

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, with exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1354 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The audit brief explicitly permits the sole generated-root failure and forbids regenerating
that file in this report-only audit. The frozen guard, module checker and ABI checker all pass.
The prover's claim that this was already failing at branch base was not independently rerun
in another checkout; acceptance here uses the brief's explicit exception, not that historical claim.

## Notes, uncertainties, errata and deviations

1. **Generator integration conventions.** At `ComposeModels.lean:123–131` and
   `Compose.lean:112–114,160–169`, witness advice uses `[1,i,j]` for exp,
   `[1,expWit.length+c,j]` for characters, `[2,i]` for inverse, and `[0,slot]` for compose
   products. Advice is re-keyed for individual witnesses. These are unsigned implementation
   choices; arbitrary advice remains sound. Generators must follow them for intended performance.
2. **Canonical order is conditional.** `ComposeModels.lean:62–68` states “If the half keys have
   length `n`, are lexicographically positive and ascending, the keys are ascending”. This is
   an accurate conditional representation claim, not an assumed theorem premise. Malformed or
   unsorted keys remain semantically sound but may prevent merging and worsen enclosures.
3. **Checked alternative character witness.** `Compose.lean:121–129` tries the negative key
   after any direct failure, including a failed pin. The handoff explicitly declares this
   deviation. Design Revision 4 F10 (`SO-LEAN-DESIGN.md:148`) says “A failed reduction makes
   `Slp.compose` return `none` (fail closed)”; read literally per attempted candidate, that wording
   is stronger than this implementation. The implemented behavior is: failed candidate is never
   accepted, a valid separately checked alternative may succeed, and failure of both routes gives
   `none`. This is a documented control-flow deviation with no weakening of the signed success
   theorem, and no analytic defect. Clarifying the design prose would remove the ambiguity.
4. **Minor documentation drift.** `Compose.lean:17` calls the constant key `[]`; actual
   `constModel` uses `padKey n []` (`ComposeModels.lean:59–60`), a length-`n` zero key with
   the same denotation. This is an inaccurate representation description, not an incorrect
   theorem or scalar-route failure. The handoff correctly describes the actual key.
5. **Performance scope.** The untracked lunar timing probe is outside the four audited files.
   Its claimed 14.2 s, witness costs and production extrapolations were not rerun or certified.
   Kernel replay of the committed tests is independently verified. No claim is made that the
   real production-size lunar certificate meets time or memory limits, or that a lunar theorem
   has closed.

No suspected pinned mathematical-source erratum was discovered in this infrastructure slice.
No premise, carrier, quantifier, constant dependence or signed conclusion was silently repaired.
The only specification-prose ambiguity and source-comment error found are items 3–4 above,
with exact locations and quotes. No production source was edited to resolve them.

Report-only audit completed. All 116 public declarations have individual table rows; all 63
public theorems have independently checked axiom receipts. Scratch probes/logs were removed.
