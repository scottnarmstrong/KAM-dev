# SO-SOUND-A independent audit 1

**Verdict: PASS WITH NOTES for the scoped SO-SOUND-A package.** The seven public contracts are
proved, kernel replay passes, and their conclusions feed the literal G1 consumer. One contract,
`TorusCertificate.ham_structural`, is strictly stronger than its signed type because it omits
`[LawfulCertArith α]`; it is not an exact fully quantified signature match. The brief expressly
allows stronger statements. Repository hygiene has the permitted stale generated-root failure;
the requested three-dot protected-path diff is nonempty because of inherited integration history.
These qualifications must accompany acceptance; this report does not certify a clean three-dot
protected-path diff or the complete certificate black box.

Audit date: 2026-10-29. Worktree: `/root/code/KAM-inp-sosounda`.
Audited HEAD: `7a5b4f293e86b45a942511ea1c5bfe2138692371`.
Compared `inp`: `5f9db8047c5a787c78317653ec232f9fe0d904ae` at inspection.
No frozen anchor/provider is introduced or sealed by this package, so an anchor-by-anchor
provider/seal probe is not applicable. The rows below give the corresponding contract verdicts.
Only this report was added to the repository; temporary probes were confined to
`.lake/abi-scratch/` and removed after recording their results. No state-changing git command,
source repair, root regeneration, or manifest change was performed.

## Scope and authorities

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the supplied
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and
`docs/tracks/SO/audits/SO-SOUND-A-handoff.md`, including its AUDIT FOCUS. The user's exact output
path overrides the generic brief's instruction to place reports in the main inp worktree.
The controlling mathematical contracts are `SOSignatures.lean` §G, lines 1002–1070,
`docs/tracks/SO/design/SO-LEAN-DESIGN.md` §4 and Appendix A §G, and
`KAM/Certificate/Defs.lean:303` (`G1Hyps`). Downstream references checked:
`docs/tracks/I/statement.md` I-G1, `blueprint-I/parts/p2-iso-iteration.tex:329`
(`bpI:p2:g1`), `KAM/Iso/Charts/Inputs.lean:46` (`IG1Body`),
`KAM/Iso/Apost/G1.lean:95`, and the sealed
`KAM/Frozen/Iso/Theorems/IsoenergeticKam.lean:44`, with the frozen strip, vector-field,
Gram, primary, real, and related definitions used by these contracts.
SO-SOUND-A implements sub-check contracts, not new I/N/P blueprint theorem nodes.
The historical draft status of the prose Track I statement does not override the sealed Lean type.

Signed source SHA256:
`9a4652019186e914a0ccfdba6e01c903e458b679d0c057ac4cf7b7d353a4c1cc`.

The complete requested `git diff inp...HEAD` was inspected by inventory and the Lean hunks;
it contains 145 files, 44,781 insertions and 2,043 deletions (52,443 diff lines including
non-Lean data, reports, graphs and tooling). Git warns:

```text
warning: inp...HEAD: multiple merge bases, using 379c70977a60ff6a0516216474fb672ddf6b1608
```

`git merge-base --all inp HEAD` reports both `379c70977a60ff6a0516216474fb672ddf6b1608`
and `db3ae048633635ee90390cf9d71c092fd30de189`. This was not silently replaced with a
two-dot or chosen alternate-base comparison. The substantive inherited changes include SO-POS,
N hypothesis assembly, P safety/stopped/geometry/source-object work, copyright cleanup, and
guard/replay tooling. They are recorded as inherited scope, not independently re-certified as
SO-SOUND-A results. The four soundness modules and their engine dependencies are the proof scope.

For attribution only, `git diff b48d78ca..HEAD` (the post-merge package starting point) contains
exactly the four new soundness modules and two handoff/request documents. The package commits
are `ef958608`, `371a0410`, `cb1bc6e7`, `3c4816e0`; handoff/request commits are
`803fb551`, `7a5b4f29`. The four modules contain 521 lines in total.

## Declaration review

All names below are in `KAM.Certificate`. A PASS means the stated local mathematical contract
passes; the overall package retains the notes above. Helpers have no separate signed blueprint
node; their statements are reviewed as the explicitly described supporting facts.

| Contract / node | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| §G static record | `StaticFacts`, Static:28 | PASS | Entire structure text is byte-identical to signed lines 1002–1023; 21 fields, no hidden instance or proof premise. |
| Static frequency helper | `freqNormLo_le_of_forall`, Static:52 | PASS | Fold maximum is below any nonnegative rational dominating each entry; no certificate assumptions smuggled in. |
| Static frequency helper | `freqNormLo_le_norm`, Static:66 | PASS | Exact box length and enclosure imply the lower bound in the Pi sup norm. |
| §G static soundness | `checkStatic_sound`, Static:99 | PASS | Signed header and fully quantified type match, including the unused lawful instance; all static fields extracted from Bool tests. |
| §G ray margins | `checkStatic_freq`, Static:130 | PASS | Signed type matches; positive lower bound excludes zero and pays both ray inequalities. |
| §G structural K | `TorusCertificate.emb_structural`, Static:152 | PASS | Signed type matches, including unused lawful binder; global finite Fourier structural facts imply strip facts. |
| Hamiltonian sum helper | `sumRangeQ_eq`, Ham:30 | PASS | Exact finite rational range-sum identity, all natural lengths. |
| Phase enumeration helper | `sum_phaseNat_eq_sumRangeQ`, Ham:38 | PASS | Bijection covers all 2n indices once, with no dimension restriction. |
| Phase double sum helper | `sum_sum_phaseNat_eq_sumRangeQ`, Ham:45 | PASS | Same bijection in each index, no factor lost. |
| Ball helper | `norm_le_ballMagQ_of_mem`, Ham:52 | PASS | Triangle inequality and complex norm ≤ sum of absolute parts; membership is the source premise. |
| Program slot helper | `Slp.norm_val_le_slotMagQ`, Ham:60 | PASS | All indices, including out-of-range, certified by `BallRel`; no range assumption is needed. |
| §G structural H | `TorusCertificate.ham_structural`, Ham:68 | PASS WITH NOTES | Header text matches; elaborated type is stronger, omitting signed lawful binder. Nonvanishing is derived by the preceding checker contract. |
| §G Hamiltonian bounds | `checkHamBounds_sound`, Ham:81 | PASS | Signed type matches; denominator proof plus all five literal G1 derivative/vector-field bounds. |
| Finite sum helper | `sum_finRange_map_eq`, Embedding:37 | PASS | Exact List/Finset sum identity for any additive commutative monoid. |
| Imaginary-angle helper | `angleImOk_sound`, Embedding:44 | PASS | Both checker branches prove the required imaginary-part bound; width tied to W.rho. |
| §G domain and DK | `checkEmbedding_sound`, Embedding:96 | PASS | Signed type matches; strict open-ball inclusion and the literal operator norm of `fderiv ℂ c.K`. |
| §G Gram | `checkGram_sound`, Gram:27 | PASS | Signed type matches; genuine determinant unit and inverse row sums at the same embedding and strip. |

Files are `KAM/Certificate/Sound/{Static,Ham,Embedding,Gram}.lean`.
Their line counts are respectively 158, 158, 164, 41; maximum line lengths 98, 98, 98, 93.
Each has the required copyright, `module`, public imports, docstring and public section.

## Signature probes and the instance difference

A Python extraction compared each signed theorem's source from `theorem <name>` up to `:=`
with the implementation and compared the entire `StaticFacts` declaration up to the next blank
line. Results: StaticFacts byte-identical; all seven theorem headers byte-identical, even before
whitespace normalization. This is header equality, not equality of proofs with draft `sorry` bodies.

Fresh copies of the signed headers were elaborated in namespace `SOAudit`, under the signed
`{n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]` context, with bodies applying the landed
exports to exactly their explicit binders, in order. All seven applications elaborate.
Bidirectional fully quantified `type_of% @...` assignments pass for six exports. The initial
probe exits 1 solely at both type assignments for `ham_structural`:

```text
error: Type mismatch
  @TorusCertificate.ham_structural
has type
  ∀ {n : ℕ} {α : Type} [CertArith α] (c : TorusCertificate n α), ...
but is expected to have type
  ∀ {n : ℕ} {α : Type} [inst : CertArith α] [LawfulCertArith α]
    (c : TorusCertificate n α), ...
```

`Ham.lean:68` is before `variable [LawfulCertArith α]` at line 79; signed line 1050 is after
that binder at line 1025. Thus the signed fully quantified type and actual type are not identical.
A second probe kept the six exact bidirectional checks and checked the stronger theorem against
the signed type by the explicit specialization:

```lean
example : type_of% @contract4 :=
  fun {n} {α} [a : CertArith α] [LawfulCertArith α] =>
    @KAM.Certificate.TorusCertificate.ham_structural n α a
```

This probe exits 0. No weakening, extra mathematical assumption, or consumer conversion is
required. Under the brief's “A strictly stronger statement is fine; record it” rule, this is a
nonblocking interface deviation, not an exact-signature PASS. If literal ABI identity is desired,
the law binder must be restored by the owner/prover; the auditor made no source edit.
The unused law binders in `checkStatic_sound` and `emb_structural` are exactly the signed types.
The handoff's unqualified “Signed statements are exactly” claim therefore needs this exception.

## Definition and hypothesis classification

The only new `def`/`abbrev`/`structure` among these four modules is the Prop-valued `StaticFacts`.
It is an exact predicate packaging the intended omega-free checker consequences, not a data
object with a junk branch, not a provider instance, and not a premise of the checker soundness
result. `checkStatic_sound` constructs it from the checker success. There are no new computational
definitions, fallbacks, or choice/default objects in the scoped modules.

The consumed pre-existing defaults were checked against their semantic specifications:

- `freqNormLo` (Defs:134) is a maximum folded with 0. The exact `freqBox.length = n` check
  makes every actual coordinate correspond to a stored interval. `FreqEncloses` supplies
  `|omega_i - centre_i| ≤ radius_i`, and `|centre_i| - radius_i ≤ |omega_i| ≤ ‖omega‖`.
- `HamExpr.jet` (Expr/Diff:332) is computed from the expression; it is not a user-supplied
  arbitrary derivative table. The compiler starts with `.const 0 0 0`. Missing/folded derivative
  entries default to slot 0, whose value is proved zero (`zero_slot_val`, line 344).
- `Slp.val` (Expr/Slp:59) reads 0 beyond the program. `slotMagQ` (Defs:141) reads `ballZero`
  beyond its ball list. `BallRel` (Expr/Ball:204) includes equal lengths and an enclosure for
  **every** natural index; `ballsAux_sound` at line 318 establishes it from the empty relation.
  So the helper really covers all indices. Slot 0's ball need not be literally `ballZero` after
  rounded ball evaluation; it still encloses its exactly zero value. The out-of-range ball is
  literally `ballZero`. These are different defaults, and neither is an unchecked assertion.
- The `d1.getD ... 0`, `d2.getD ... [] ... 0`, `d3.getD ... [] ... [] ... 0` reads in the bound
  checks are precisely the reads in `jet_d1/d2/d3` (Expr/Diff:368,384,410). Those theorems identify
  them with actual derivatives on an open nonvanishing domain. A zero fallback cannot hide a
  nonzero derivative: the proved identity would then force that derivative to be zero.
- Missing embedding components denote the same zero functions in `realComp` and their models;
  degree/default reads are shared. Domain centre/radius reads are likewise the same `getD` reads
  in `certDomain` (Expr/Basic:175) and the inclusion proof. Static additionally checks list lengths.

No helper assumes its own conclusion or a hard soundness step. `LawfulCertArith` is the standing
arithmetic law interface. Model enclosures, jet identities and Gram invertibility are invoked
as proved engine theorems. `ham_structural`'s nonvanishing hypothesis is an explicit source
condition, produced by `checkHamBounds_sound`, not a hidden unproved assembly obligation.

## Focused proof review and G1 attachment

**Frequency.** Static:66–95 transfers the rational maximum to the real sup norm using coordinate
bounds and rational density. Static:130–148 uses positive `freqNormLo` and its norm lower bound
to prove `omega ≠ 0`. Both factors `s - 1` and `sigma_omega - s` are nonnegative from checked
strict inequalities, so multiplication preserves the lower bound and yields both nu margins.
No Euclidean norm or dimension-dependent normalization is substituted.

**Hamiltonian.** Ham:87–121 derives `1 ≤ n`, nonvanishing and open-domain smoothness before
using derivative bridges. The five Bool conjuncts at Defs:150–159 map as follows:

| Checked bound | Proof / target |
|---|---|
| Sum of all first-derivative magnitudes | `norm_fderiv_le_sum_partials`: `‖fderiv ℂ H z‖ ≤ M`. |
| Each first-derivative magnitude | `hamiltonianVectorFieldℂ_sumVec`, sign and phase swap: `‖X_H z‖ ≤ M`. |
| Every second-derivative row sum | `norm_fderiv_hamiltonianVectorFieldℂ_le`: `‖fderiv ℂ X_H z‖ ≤ M`. |
| Every third-derivative double row sum | `norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le`: `‖iteratedFDeriv ℂ 2 X_H z‖ ≤ M`. |
| Full sum of second-derivative magnitudes | `norm_iteratedFDeriv_two_le_sum_partials`: `‖iteratedFDeriv ℂ 2 H z‖ ≤ M`. |

`phaseNat` enumerates all phase rows bijectively; the `a.swap` rows for X_H are included.
The two vector-field derivative bridges receive `1 ≤ n` and the actual `ContDiffAt` consequences.
No derivative is silently replaced by a coordinate bound or a totalized derivative at a
non-differentiable point: open-domain nonvanishing gives the required smoothness.

**Embedding.** Embedding:44–94 proves both disjuncts of `angleImOk`:
(1) the imaginary part is bounded by the full complex norm of the enclosed component;
(2) derivative component enclosures bound `‖DU_i‖` by the rounded sum S, and mean value from
`x = Re theta` gives `|Im U_i(theta)| ≤ S * ‖theta - x‖ ≤ S * rho`.
The weight check makes rho positive, hence x is inside the open strip. The strip is convex,
so the whole segment from x to theta stays there. Real Fourier data gives `Im U_i(x) = 0`.
The proof establishes `S ≥ 0` before using all multiplication and upward-rounding inequalities.
The helper deliberately requires the angle-check width to be `W.rho`; Static supplies the exact
`weight.rho = params.rho` equality when applying it.

For a point w in the **open** mu-ball, coordinate perturbations have norm strictly less than mu.
Checked angle displacement is ≤ `rho_H - rho - mu`, and `|Im theta_i| < rho`, so the sum is
strictly < rho_H. Checked action displacement from its centre is ≤ `r_i - mu`; adding the
strict perturbation < mu gives strictly < r_i. Equality in either checker slack is therefore
safe. The proof does not assert inclusion of the closed mu-ball or replace open D by its closure.

For DK, `dkModels_encloses` bounds every entry of `tangentMat c.K theta`, including the identity
in angle rows. `sumUp_ge` yields each full row sum ≤ `sigma_K - mu`. A row exists since n ≥ 2;
its nonnegative sum proves the bound itself nonnegative. `norm_colMat` and
`KAM.norm_le_iff_forall_rowSum` then give the actual continuous-linear-map operator norm in the
Pi/product sup norms. There is no unaccounted n or 2n factor.

**Gram.** Gram:27–39 extracts an actual `some deltaBeta` witness from `isSome = true` and applies
`gramCheck_sound` with checked weight, pi enclosure, n ≥ 1 and the exact sigma_B - mu. It
transports the strip width via equality, then returns the true `gramMatrix c.K` inverse row
sums and unit determinant. It never identifies the witness polynomial with an exact inverse.

The outputs match `G1Hyps` fields literally:
Static → scalar fields; frequency → `hωstar hν1 hν2`; structural K → `hK hKp hKr`;
Ham bounds → `hbd`; structural H → `hopen htransl hholo hper hreal`;
Embedding → `hball hDK`; Gram → `hG`. They use `complexStrip`, `fderiv ℂ`, the frozen
`hamiltonianVectorFieldℂ`, and `iteratedFDeriv ℂ 2` on precisely the functions in `IG1Body`.
Rational-to-real coercions are the signed coercions. No norm conversion is required by SO-SOUND-B.

A fresh audit-only consumer application (reproduced below) elaborated against `g1_explicit` with
these exact seven outputs and only the still-unproved SO-SOUND-B/torsion/error/smallness and
Diophantine obligations supplied separately. This verifies applicability; it does not prove
those remaining obligations or `checkTorusCertificate_sound`.

## Hygiene receipts

Every Lean/Lake invocation below was serialized and used `LEAN_NUM_THREADS=1` and `nice -n 5`.
No heartbeat, synthesis-heartbeat, or recursion-depth override was used. No full library build,
clean, package-cache mutation, or package update was run.

Targeted gated build (exit 0):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sosounda KAM.Certificate.Sound.Static KAM.Certificate.Sound.Ham KAM.Certificate.Sound.Embedding KAM.Certificate.Sound.Gram
```

```text
[inp-gate] slot 1 acquired 21:38:58 for KAM.Certificate.Sound.Static KAM.Certificate.Sound.Ham KAM.Certificate.Sound.Embedding KAM.Certificate.Sound.Gram
Build completed successfully (3253 jobs).
```

The wrapper itself executes `nice -n 5 lake build`. Replayed inherited warnings:
Arith/PiHigh:218 unused simp argument, Expr/Basic:85 unused variable.
New-module warnings: Static:99 and :152 unused `[LawfulCertArith α]`, Ham:68 unused
`[CertArith α]`. The handoff reports only the two Static warnings; this run also reports the Ham
warning. No elaboration error or resource-limit failure occurred.

Probes (first intentionally refutes exact equality of ham_structural, subsequent probes pass):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOSoundAudit.lean
# exit 1: exactly two ham_structural fully quantified type-mismatch errors
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOSoundAuditPass.lean
# exit 0: six exact bidirectional type checks, seven signed applications,
#         explicit lawful specialization of the stronger seventh type, and all axioms
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOSoundConsumer.lean
# exit 0; output empty
```

`#print axioms` was executed for every one of the 16 new public theorems. Exact output:

```text
'KAM.Certificate.freqNormLo_le_of_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.freqNormLo_le_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkStatic_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkStatic_freq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.TorusCertificate.emb_structural' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumRangeQ_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sum_phaseNat_eq_sumRangeQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sum_sum_phaseNat_eq_sumRangeQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.norm_le_ballMagQ_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.Slp.norm_val_le_slotMagQ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.TorusCertificate.ham_structural' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkHamBounds_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sum_finRange_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.angleImOk_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkEmbedding_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkGram_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel replay, one invocation, exit 0:

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Sound.Static KAM.Certificate.Sound.Ham KAM.Certificate.Sound.Embedding KAM.Certificate.Sound.Gram
```

```text
replaying KAM.Certificate.Sound.Gram
replaying KAM.Certificate.Sound.Embedding
replaying KAM.Certificate.Sound.Ham
replaying KAM.Certificate.Sound.Static
```

This replays the declarations of these four target modules; it is not a claim of a fresh kernel
replay of all imported Mathlib/KAM dependencies. A source import-closure traversal found 102 KAM
modules, no provider import, no frozen theorem import, and exactly 19 frozen definition modules,
all manifest SEALED. All manifest entries are currently SEALED. Thus no DRAFT_SORRY or provider
quarantine dependency enters the scoped proof chain.

Repository lint, exit 1 solely for the allowed generated-root staleness:

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1374 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The ABI probe inside lint ran after the preceding Lean process completed. No other forbidden
construct, size, line-length, module, or errata-rendering failure was printed. The generated root
was left untouched as required.

Protected-path comparison:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

**Nonempty**: KAM.lean adds 33 imports; README.md is updated; the unrelated planetary frozen
`PlanetaryExponentialSafety.lean` replaces its authorized proof body `by sorry` with
`by exact KAM.Provider.Planetary.planetaryExponentialSafety hn B hB`; the manifest changes that
anchor from DRAFT_SORRY to SEALED. These are already present at `b48d78ca`.
The supplementary `git diff b48d78ca..HEAD -- KAM/Frozen manifest KAM.lean README.md`
is empty (exit 0). Therefore the brief's literal empty three-dot condition is not met, but no
SO-SOUND-A commit edits protected paths; current frozen byte/ABI guards pass. This is an explicit
inherited-history qualification, not a suppressed clean-diff claim.

`git diff --check inp...HEAD` exits 0 with only the multiple-merge-base warning;
`git diff --check` exits 0 with no output.

## Errata candidates, deviations and remaining scope

No suspected pinned mathematical source or blueprint defect was found in these contracts.
No frozen declaration appears false or requires alteration. The only scoped signature deviation
is the stronger law-free `ham_structural` type, at Ham:68 versus signed line 1050 under line 1025.

Documentation corrections for the handoff:

1. Handoff: “Signed statements are exactly as in SOSignatures §G (names, binders, types).”
   This is false for the implicit lawful binder of `ham_structural`; header text alone hides it.
   The stronger theorem is accepted under the audit brief, and its signed application passed.
2. “two unusedSectionVars linter warnings” understates this independent build: Ham:68 also
   reports unused `[CertArith α]`. This does not weaken any theorem.
3. The AUDIT FOCUS calls its list “seven signed declarations” while also listing `StaticFacts`:
   there are seven theorems and one structure. All eight were reviewed.
4. “out-of-range reads give 0/ballZero” is correct for out-of-range program/ball indices;
   missing derivative-table entries first select the existing compiled zero slot. That slot's
   ball need only enclose zero; the proof never assumes it is an exact zero-radius ball.

No audit changes were introduced to production Lean or source statements. The package is ready
for integration with these notes. Invariance, energy, torsion, smallness and the final black-box
assembly remain outside this package's proved surface; numerical certificates and lunar
confinement are not established by this audit.

## Reproduced consumer probe

```lean
import KAM.Certificate.Sound.Ham
import KAM.Certificate.Sound.Embedding
import KAM.Certificate.Sound.Gram
import KAM.Iso.Apost.G1
open KAM KAM.Torus KAM.Certificate
open scoped Matrix.Norms.Operator
-- Audit-only application: the remaining SO-SOUND-B obligations are explicit inputs.
example {n : ℕ} {α : Type} [CertArith α] [LawfulCertArith α]
    (c : TorusCertificate n α) (ωstar : Fin n → ℝ)
    (hs : checkStatic c = true) (hh : checkHamBounds c = true)
    (he : checkEmbedding c = true) (hg : checkGram c = true)
    (hω : FreqEncloses n c.freqBox ωstar)
    (hdio : IsDiophantine c.params.γ c.params.tau ωstar)
    (hTu : IsUnit (KAM.Iso.extendedTorsionAverage c.H c.K
      ((c.params.s : ℝ) • ωstar)).det)
    (hTb : ∀ i, ∑ j, ‖(KAM.Iso.extendedTorsionAverage c.H c.K
      ((c.params.s : ℝ) • ωstar))⁻¹ i j‖ ≤ (c.params.σT : ℝ) - c.params.μ)
    (hE : ∀ θ ∈ complexStrip n c.params.rho,
      ‖invarianceError c.H c.K ((c.params.s : ℝ) • ωstar) θ‖ ≤ c.params.err)
    (hEn : ‖KAM.Iso.energyAverage c.H c.K - ((c.params.E0 : ℝ) : ℂ)‖ ≤ c.params.err)
    (hC1 : Iso.Apost.isoC1 n c.params.tau c.params.rho c.params.rhoInf
      c.params.M c.params.σK c.params.σB c.params.σT c.params.μ c.params.nuRay
      c.params.γbar * c.params.err /
      ((c.params.γ : ℝ) ^ 4 * (c.params.rho : ℝ) ^ (4 * (c.params.tau : ℝ))) < 1) : True := by
  have st := checkStatic_sound hs
  obtain ⟨hw0, hν1, hν2⟩ := checkStatic_freq hs hω
  obtain ⟨hnv, hbd⟩ := checkHamBounds_sound hs hh
  obtain ⟨hopen, htransl, hholo, hper, hreal⟩ := c.ham_structural hnv
  obtain ⟨hK, hKp, hKr⟩ := c.emb_structural
  obtain ⟨hball, hDK⟩ := checkEmbedding_sound hs he
  have hG := checkGram_sound hs hg
  have g1 := Iso.Apost.g1_explicit st.hn st.hτ st.hρinf st.hρinfρ
    st.hM st.hσK st.hσB st.hσT st.hμ st.hγbar st.hσω st.hν ωstar hw0
  have result := g1.2.2.2 c.D c.H c.K c.params.s c.params.γ c.params.err c.params.E0
    hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb
    st.hs1 st.hsσ hν1 hν2 st.hγ st.hγγbar hdio st.he0 hE hEn hC1
  trivial
```
