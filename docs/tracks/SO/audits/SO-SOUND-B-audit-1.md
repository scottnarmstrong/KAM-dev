# SO-SOUND-B independent audit 1

Audit date: 2026-10-29. Checkout: `/root/code/KAM-inp-sosoundb`.
Audited HEAD: `e2628f4b850e24de841cd818f7d36702d3a45215`.

## Verdict and scope

**PASS WITH NOTES for part B**. All six signed
contracts pass statement and proof review. These are ordinary implementation theorems, not six
new frozen anchors: no new seal is needed or performed. This verdict does not independently
approve part A, unrelated inherited packages, lunar data, or the final lunar confinement result.
Part A's signed contracts are treated as given, as required by the AUDIT FOCUS.

Read: AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, the supplied package brief and handoff,
SO-LEAN-DESIGN.md §4 and §G, the current main-worktree SOSignatures.lean §G,
SPIN-ORBIT-PLAN.md, track I's statement, IG1Body, g1_explicit, and the relevant frozen
invariance, energy, and torsion definitions and I-G1 statement. There is no SO/statement.md;
the SO design and signed §G are the controlling package statements. N/P anchor probes are
inapplicable to these five ordinary certificate modules.

### Mandatory comparison and inherited changes

`git diff inp...HEAD` is **not** a clean package-only diff. Git warns:

```
warning: inp...HEAD: multiple merge bases, using 379c70977a60ff6a0516216474fb672ddf6b1608
```

`git merge-base --all inp HEAD` returns that base and
`db3ae048633635ee90390cf9d71c092fd30de189`. The selected three-dot diff has 150 files,
45275 insertions and 2043 deletions, including inherited SO infrastructure/data, I/N/P work,
graph/docs updates, and copyright cleanup. Scope was assessed from this comparison and the
B-owned commits `cc8e2432`, `c2dc6683`, and `e2628f4b`, rather than assuming the full branch
history belongs to B.

The brief's literal protected-path condition fails at branch-comparison level:
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is nonempty. Its paths are
`KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean`,
`manifest/frozen-anchors.json`, `KAM.lean`, and `README.md`. The frozen change replaces
`by sorry` by the Planetary provider seal; the manifest changes its state from DRAFT_SORRY
to SEALED. Generated root imports and README have inherited updates. This is a provenance
note, not a claim that the requested empty diff passed.

`git diff 803fb551 HEAD --stat` contains exactly the five B Lean modules (482 lines) and
its 79-line handoff. `git diff 803fb551 HEAD -- KAM/Frozen manifest KAM.lean README.md` is
empty. Thus the handoff's untouched-files claim holds for B's contribution relative to
merged A, but not literally for the mandatory three-dot comparison against inp.

## Declaration review

All names below are in `KAM.Certificate`. Node locators refer to SO design §4/§G and the
corresponding signed sub-check contract, rather than invented I/N/P graph nodes.

| Node / contract | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| Smallness | `checkSmallness_sound`, Sound/Smallness.lean:26 | PASS | Exact signed type; upper rational constants, nonnegative err, positive denominators; strict threshold retained. |
| Hamiltonian coordinates | `sumVec_hamiltonianVectorFieldℂ`, Sound/Invariance.lean:30 | PASS | Exact signed Hamiltonian coordinate swap and sign, for arbitrary H and z; no differentiability premise needed for this linear identity. |
| Tangent coordinates | `sumVec_fderiv_apply`, Sound/Invariance.lean:38 | PASS | Expands the entire vector in the Pi basis; every derivative coordinate is included. |
| Frequency times DK | `dkFreqModel_encloses`, Sound/Invariance.lean:47 | PASS | Uniform for every exact real vector satisfying box membership; all n products summed before degree conversion. |
| Conditional invariance | `checkInvariance_sound_of`, Sound/Invariance.lean:74 | PASS | Distinct helper; extra premises exactly A's Ham/Embedding conclusions. |
| Invariance | `checkInvariance_sound`, Sound/Invariance.lean:142 | PASS | Byte-identical signed type, exact frozen invarianceError at s • ωstar. |
| Conditional energy | `checkEnergy_sound_of`, Sound/Energy.lean:31 | PASS | Distinct helper; extra premises exactly A's Ham/Embedding conclusions. |
| Energy | `checkEnergy_sound`, Sound/Energy.lean:104 | PASS | Byte-identical signed type; exact period-one frozen energyAverage. |
| Conditional torsion | `checkTorsion_sound_of`, Sound/Torsion.lean:32 | PASS | Distinct helper; actual gramCheck witness, literal frozen torsion enclosure and average, same n. |
| Torsion | `checkTorsion_sound`, Sound/Torsion.lean:68 | PASS WITH NOTES | Exact signed type; hg is deliberately unused because checkTorsion repeats gramCheck. |
| G1 hypotheses | `checkTorusCertificate_hyps`, Soundness.lean:33 | PASS | Exact signed type; every field constructed from checks and structural facts. |
| Black box | `checkTorusCertificate_sound`, Soundness.lean:62 | PASS | Exact signed type; applies implementation g1_explicit with exact denoted data and replaces only the two displacement estimates. |

### Signature and helper probes

Python extracted each theorem header through (but excluding) `:=` from the current
`/root/code/KAM-inp/.drafts/design/SOSignatures.lean` and its implementation. All six were
**byte-identical**, including binder order and coercions. This compares declarations, not
proof bodies or differing explanatory docstrings.

A fresh scratch module imported `KAM.Certificate.Soundness`, reproduced each signed
declaration under `audit_<name>`, and supplied exactly its explicit binders, in order:

```
checkSmallness_sound hs h
checkInvariance_sound hs hh he h hω
checkEnergy_sound hs hh he h
checkTorsion_sound hs hh he hg h hω
checkTorusCertificate_hyps h hω
checkTorusCertificate_sound h hω hdio
```

For each it also checked `example : type_of% @<name> := @audit_<name>`.
This is the ordinary-implementation analogue of the brief's provider/frozen seal probes;
no production provider import was added. Elaboration exited 0 at default resource limits.

Text extraction separately confirmed all six helper-premise comparisons: each hH and hE
is verbatim the conclusion of `checkHamBounds_sound` and `checkEmbedding_sound`, respectively.
The signed Energy/Invariance theorems simply apply the corresponding helper with those
proved conclusions; Torsion does the same after `have _ := hg`. None substitutes a conditional
helper for the signed result. The helpers assume no invariance, smallness, energy or torsion
conclusion. No new public statement weakens its signed contract.

## Mathematical checks

**Smallness.** Smallness.lean:42–50 obtains `isoC1 ≤ isoC1Q` and `isoC2 ≤ isoC2Q` under the
static inequalities. Multiplication preserves those directions using `S.he0`. Lines 52–59
identify real exponents 4τ and 2τ with natural powers and prove both denominators positive.
The first conclusion uses `div_lt_one` and a strict rational inequality; the second uses
`div_le_iff₀` and retains `≤ disp`. No rounding direction is reversed and err = 0 is allowed.

**Invariance.** Invariance.lean:97–111 attaches every composed d1 slot to the literal complex
Fréchet derivative of c.H at c.K θ, using nonvanishing on the open certificate domain and
membership obtained from the positive μ-ball. Lines 114–133 account for the Hamiltonian
swap/sign and subtract the entire DK(s • ωstar) sum. `freqModel_encloses` supplies the same
scaled vector uniformly over the box, `dkModels_encloses` pays every tangent entry, and
`modelSum_encloses` pays all n terms. Lines 134–140 use norm_sumVec and the Pi max norm,
not a Euclidean norm or a dimensional estimate with an omitted factor. The final bound is
on the literal frozen `KAM.invarianceError`.

**Energy.** Energy.lean:45–57 proves H∘K continuous on the strip before averaging;
`Slp.compose_sound` and `jet_v0` attach the singleton to c.H∘c.K. The degree-zero shifted
model encloses H∘K−E0. Lines 85–95 explicitly identify its integral with the frozen
`KAM.Iso.energyAverage c.H c.K − E0`, using integrability from continuity and volume([0,1]^n)=1.
The final estimate includes both the zero-mode coefficient-ball radius and model remainder,
with upward arithmetic bounds followed by the check against a downward-rounded err.
There is no replacement of energy by a proxy, point value, or unnormalized integral.

**Torsion.** Torsion.lean:48–63 obtains Kθ∈D from A's μ-ball and μ>0, passes the successful
check's own δβ to `torsionModels_sound`, and uses the returned literal frozen extended-torsion
enclosure and continuity in `torsionAvgCheck_sound`. Both use the certificate's n and the
same s • ωstar; the checker verifies the (n+1)×(n+1) dimensions. The shape conjunct is not
needed again in this assembly. The redundant hg premise is harmless and matches the signed
interface. It is not used as a substitute for the internal gramCheck success.

**Black box and hypothesis provenance.** Defs.lean:303–350 (G1Hyps) and :356–369
(CertifiedTorus) are byte-identical to the corresponding signed declarations/bodies.
Soundness.lean:43–55 constructs every field as follows:

| Fields | Provenance |
|---|---|
| hn, hτ, widths, positive constants, hs1, hsσ, hγ, hγγbar, he0 | checkStatic_sound |
| hωstar, hν1, hν2 | checkStatic_freq with hω |
| hopen, htransl, hholo, hper, hreal | ham_structural with checked Hamiltonian nonvanishing |
| hbd | checkHamBounds_sound |
| hK, hKp, hKr | emb_structural (representation identities) |
| hball, hDK | checkEmbedding_sound |
| hG | checkGram_sound |
| hTu, hTb | checkTorsion_sound |
| hE | checkInvariance_sound with hω |
| hEn | checkEnergy_sound |
| hC1, hdisp | checkSmallness_sound |

Soundness.lean:67–74 calls `KAM.Iso.Apost.g1_explicit` (G1.lean:95) with
`(n, τ, ρ, ρinf, M, σK, σB, σT, μ, γbar, σω, ν, ωstar)` exactly as its docstring specifies,
where the certificate scalars are projections of c.params. It applies the resulting IG1Body
to `(c.D, c.H, c.K, c.params.s, c.params.γ, c.params.err, c.params.E0)` and the checked
fields in source order; hdio is the sole additional Diophantine input. No G1 hypothesis is
assumed as a bundled external record. The three positivity conjuncts are discarded, not
replaced by assumptions. The eleven output clauses are preserved: bounds on sinf, holomorphy,
primary/real properties, invariance, pointwise energy, ball and derivative margins, and both
closeness estimates. Since G1 chooses C2=C3=isoC2, the same checked hdisp pays both final
estimates. CertifiedTorus claims precisely those clauses and no new embedding/Lagrangian
property beyond the source conclusion.

## Definition classification and imports

The five B files introduce **no def, abbrev, structure, instance, or data fallback**.
All twelve new declarations are public theorems. The proof-local let L in dkFreqModel_encloses
is the actual finite list of n products, not a substitute carrier. Existing totalized list
accesses are used under successful check/length/range guards; no junk default supports a result.
Existing G1Hyps is a proposition listing source premises and is constructed, never an input
to the signed black box. Existing CertifiedTorus is the literal existential output described
above. Existing Boolean checkers reject failed constructions; their fallback branches are
eliminated by the success premise. None of these existing definitions was changed by B.

A recursive source-import traversal of Soundness found 147 KAM modules, **zero providers**,
**zero frozen theorem imports**, and all reachable frozen definition modules SEALED in the
manifest. Thus no DRAFT_SORRY anchor is imported, directly or transitively. The g1_explicit
implementation is used without importing its frozen anchor.

## Independent validation receipts

All Lean/Lake invocations were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`
(the compile gate supplies nice itself). No clean, update, cache fetch, heartbeat override,
source repair, root regeneration, or state-changing git command was used.

Build command:

```
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-sosoundb KAM.Certificate.Soundness
```

Exit 0. Output: `[inp-gate] slot 1 acquired 21:43:40 for KAM.Certificate.Soundness`;
`Build completed successfully (3299 jobs).` Replayed dependency warnings occurred in
Arith/PiHigh.lean:218, Expr/Basic.lean:85, Sound/Static.lean:99,152 and Sound/Ham.lean:68;
none was emitted from B's five files.

Probe command:

```
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOSoundBAudit.lean
```

Exit 0. All six type/seal-shaped checks elaborated. `#print axioms` returned exactly
`[propext, Classical.choice, Quot.sound]` for **every one** of the twelve rows in the
declaration table and for `KAM.Iso.Apost.g1_explicit`. No sorryAx or additional axiom. Exact axiom output:

```
'KAM.Certificate.checkSmallness_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumVec_hamiltonianVectorFieldℂ' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.sumVec_fderiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.dkFreqModel_encloses' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkInvariance_sound_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkInvariance_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkEnergy_sound_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkEnergy_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorsion_sound_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorsion_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorusCertificate_hyps' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Certificate.checkTorusCertificate_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Apost.g1_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Kernel command (one invocation):

```
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Soundness KAM.Certificate.Sound.Smallness KAM.Certificate.Sound.Invariance KAM.Certificate.Sound.Energy KAM.Certificate.Sound.Torsion
```

Exit 0. Complete output:

```
replaying KAM.Certificate.Sound.Torsion
replaying KAM.Certificate.Sound.Energy
replaying KAM.Certificate.Sound.Invariance
replaying KAM.Certificate.Sound.Smallness
replaying KAM.Certificate.Soundness
```

Lint command:

```
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit 1, solely for the explicitly permitted generated-root exception. Complete output:

```
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1379 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

All other source, module, frozen-anchor and ABI checks passed. KAM.lean was left untouched.

File sizes: Smallness 71, Invariance 149, Energy 109, Torsion 77, Soundness 76 lines.
All five have the copyright header, module command, public imports, module docstring, and
public section. No new definition needs expose. Forbidden proof escapes, forbidden ambient
carriers and resource overrides were checked by the source lint. `git diff --check` exited 0.

## Notes, uncertainties, errata and deviations

1. The inherited protected-path diff is nonempty, as documented above. This prevents an
   unqualified whole-branch hygiene PASS. B itself has no such edits.
2. Generated-root staleness is allowed only as the brief's explicit exception; it is not
   repaired during this report-only audit.
3. The signed torsion docstring in SOSignatures.lean near :1081 says `hG from checkGram`.
   The implementation instead obtains the exact success witness by unfolding checkTorsion,
   which repeats gramCheck. SO design §4's Gram dependency is correspondingly redundant at
   the signed-wrapper level. This is an explanatory provenance refinement, not a false
   statement, source erratum, missing premise, or mathematical deviation.
4. Part A's proof fidelity remains the separate SO-SOUND-A audit's responsibility. The
   present result establishes B's composition against those contracts. No concrete
   certificate acceptance or lunar theorem is asserted here.

No suspected mathematical defect in the signed design, frozen statement, or pinned source
was found in this scope. No mathematical deviation was introduced by the auditor. Only this
report is retained; scratch probes/logs are removed after their receipts are recorded.
