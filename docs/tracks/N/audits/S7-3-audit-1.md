# Independent audit 1: S7-3

**Overall verdict: PASS WITH NOTES.** The three S7-3 public results pass statement fidelity,
proof review, exact-type elaboration, axiom inspection and kernel replay. They are ready to land
as helper results. No frozen anchor is sealed by this package, and this verdict does not certify
N-HEAD-C or any I/N/P root theorem.

## Scope and immutable inputs

Tier-2, refute-first review under `inp-audit-package.md`, the handoff's AUDIT FOCUS, `AGENTS.md`,
`docs/PLAN.md` and `docs/DECISIONS.md`. Only `Conjugation.lean` and `Transfer.lean` are audited
implementation files. S7-1 and generic ODE/canonical results were inspected at their points of
use, not re-audited as packages. The track-N statement conventions and relevant frozen field
and theorem interfaces were read for context. The manuscript-audit and lean-statement-audit
skills supplied the statement/semantic checks. No subagents or network sources were used.

The user's exact absolute report destination overrides the generic brief's main-worktree
output instruction. Only this report is retained; temporary probes were confined to
`.lake/abi-scratch/`. No source, frozen file, manifest, generated file, git state or source
errata ledger was edited.

Snapshot `frozen-v1`, 2026-10-28:

| Input | Commit or SHA-256 |
|---|---|
| Package HEAD | `640de98a4a5245af9a5830c7d7341f765d87cda8` |
| `inp` at intake | `88983f74ff9952994d1de31d0ed671307437b563` |
| Merge base at intake | `00cf49c93cbcea2fd371edf0865258fadd64a43d` |
| `KAM/Nekhoroshev/Stability/Conjugation.lean` | `d3f363c11ce374b00bdcf6b19b56708ca5e8a033229d8008784b6394b145417f` |
| `KAM/Nekhoroshev/Stability/Transfer.lean` | `780d290d207a7ec62df6dfe92a88b139218ae225309413a081a599ebba6638ed` |
| Design v2, `docs/tracks/N/design/PART67-LEAN-DESIGN.md` | `9376271a6f311a2fa9bdf530680433ae2b759a84747a05aa1aa8ad07d2e53be2` |
| Supplied `/root/code/KAM-inp/.drafts/design/NPart67Signatures.lean` | `c588818b1772d3f7e106aac256b8207623c8a142cf40ef0e778f0507b1945c9f` |
| `blueprint-N/parts/p7-stability.tex` | `f3d6e993abd74759469db1c9ae3c2c6d7cc65555a6d13167e8bfc7c38493e4bd` |
| Untracked supplied `docs/tracks/N/audits/S7-3-handoff.md` | `9f61930a2011c5990d0e5602c8a2a6a4d00c29b75d0335c5b7f839b298889e4c` |

`git diff inp...HEAD` at intake adds exactly the two audited files, 141 and 265 lines
respectively (406 total). The `inp` ref advanced during this audit; the intake hash above pins
the comparison. All code locators below refer to this package HEAD. The earlier design audits
were checked, especially audit-1 F1 and audit-2's corrected norm fields. Their design approval
was not treated as proof evidence.

## Declaration ledger and fidelity

| Node / role | Lean declaration (namespace `KAM.Stability`) | Verdict | Reason |
|---|---|---|---|
| `bpN:p7:conjugation` | `conjugation` (`Conjugation:89`) | PASS | Exact design v2 type; genuine orbit of H obtained from an H′ orbit. |
| `bpN:p7:stopped-extension` | `stopped_extension` (`Transfer:86`) | PASS | Exact design type; both confinement and domain membership, for arbitrary extension F and both time directions. |
| `bpN:p7:transfer` | `transfer` (`Transfer:156`) | PASS WITH NOTES | Exact T1–T3 type and bound ϱ+2d; unused signature-mandated hϱ is harmless. |
| Private real-value identity | `psi_real_eq` (`Conjugation:35`) | PASS | Range membership identifies Ψιx with ι(reMap Ψ x). |
| Private domain bridge | `reMap_mem` (`Conjugation:47`) | PASS | Uses map/reality assumptions and positive target strip width. |
| Private derivative bridge | `reMap_hasFDerivAt` (`Conjugation:56`) | PASS | Real restriction derivative, with intertwining identity for every real direction. |
| Private open domain | `isOpen_realStrip'` (`Transfer:39`) | PASS | Product openness from the literal real neighbourhood. |
| Private first exit | `stay_forward` (`Transfer:49`) | PASS | Closed C inside open V prevents first exit on each admissible initial segment. |

Each public theorem's header, after removing line comments and normalizing whitespace, is
identical to both Appendix A of design v2 and the supplied signature file. A separate Lean
probe copied each design type under a fresh name and applied the implementation to every
explicit binder in order; all three elaborated. There is no provider/frozen seal pair in S7-3,
so provider-equality and seal-body probes are inapplicable here.

Blueprint anchors: p7 lines 64–72, 92–108 and 110–117. In particular the transfer conclusion is
“≤ϱ+2d_*”, and stopped-extension requires the “genuine two-sided derivative ... endpoints
included”. Both are preserved. `IsOrbit` unfolds to actual membership and `HasDerivAt` at
every time, through `KAM.ODE.IsSolutionIn`, rather than a confinement proxy. The design's
symmetric-monotone predicate `adm` generalizes a fixed time cutoff: it includes infinite time
and does not require division by perturbation size. Stopped-extension additionally drops the
blueprint's holomorphy/reality assumptions on H: these are unnecessary once hconf is supplied,
and this is a stronger theorem, already explicit in the approved design.

### Expanded logical inputs

C = conjugation, T = transfer, S = stopped_extension. Each row denotes the indicated binder
in every listed theorem. SOURCE premises cite the corresponding blueprint lemma above;
positive strip widths use design §0 conventions. STANDING, RULED and EXCESS counts are zero.
All nested quantifiers retain their source scope; no constant is existentially chosen with
extra dependence.

| Theorems | Binder | Bin | Meaning / authority |
|---|---|---|---|
| C,T | hs | SOURCE | Positive target strip width. |
| C,T | hs′ | SOURCE | Positive input strip width. |
| C,T | hH | SOURCE | H holomorphic and period-one on target domain. |
| C,T | hHr | SOURCE | H real on real target points. |
| C,T | hH′ | SOURCE | H′ holomorphic and period-one on input domain. |
| C,T | hH′r | SOURCE | H′ real on real input points. |
| C,T | hΨ | SOURCE | Holomorphic Ψ on input domain. |
| C,T | hΨmap | SOURCE | Ψ maps input domain into target domain. |
| C,T | hΨreal | SOURCE | Ψ real at real points of input domain. |
| C,T | hΨsympl | SOURCE | Preservation of symplectic form for all v,w. |
| C,T | hconj | SOURCE | H′=H∘Ψ throughout input domain. |
| C | hz | SOURCE | Genuine H′ orbit on J. |
| T,S | hadm | SOURCE | Design §0.5 symmetric-monotone encoding of source time cutoff. |
| T,S | hN.continuous | SOURCE | Continuity of source norm. |
| T,S | hN.map_zero | SOURCE | Source norm vanishes at zero. |
| T,S | hN.add_le | SOURCE | Source norm triangle inequality. |
| T,S | hN.neg | SOURCE | Source norm symmetry. |
| T,S | hN.smul | SOURCE | Source norm real absolute homogeneity. |
| T,S | hN.norm_le | SOURCE | Explicit source domination of max norm. |
| T | hT1 | SOURCE | Uniform action displacement ≤d on input real strip. |
| T | hT2 | SOURCE | Real preimage of every point over D. |
| T | hϱ | SOURCE | Positive confinement radius in T3. |
| T | hdϱ | SOURCE | Strict d+ϱ<r′ in T3. |
| T | hT3 | SOURCE | A priori confinement for every H′ orbit near each Iy∈D. |
| S | hϱ | SOURCE | Positive confinement radius. |
| S | hϱr | SOURCE | Strict radius smaller than r. |
| S | hconf | SOURCE | Explicit source assumption: confinement of every H orbit. |
| S | hF | SOURCE | F agrees with the Hamiltonian field on real strip. |
| S | hJ | SOURCE | J is an interval (OrdConnected). |
| S | h0 | SOURCE | 0∈J. |
| S | hz | SOURCE | Actual two-sided derivative of total z at every t∈J. |
| S | hz0 | SOURCE | Initial action in D. |

Expanding InClass contributes differentiability and period-one shift equality (two inputs
per occurrence); RealOn is exactly imaginary-part zero on real domain points. IsOrbit
contributes domain membership and the ordinary derivative equality (two inputs). These are
source data, not bundled proof obligations. Counting expanded top-level logical inputs gives
C: 15 SOURCE, T: 25 SOURCE, S: 15 SOURCE; STANDING=RULED=EXCESS=0 for each. Internal universal
variables/restrictions within these predicates are retained as written in the matching types.

The remaining outer binders are TYPING, each with its source carrier: C has n,D,r,s,r′,s′,H,H′,Ψ,
J,z (11); T has n,D,r,s,r′,s′,d,ϱ,Nrm,adm,H,H′,Ψ (13); S has n,D,r,ϱ,Nrm,adm,H,F,J,z (10).
The universally quantified J,z,t and their interval/orbit/admissibility premises in T's
conclusion remain universally quantified, in the same order, as in the blueprint/design.
There are no added instance assumptions or conclusion-shaped hypotheses. hT3 and hconf are
confinement assumptions because these two source results explicitly transfer a priori
confinement; neither is presented as proving that confinement from scratch.

## Definitions and proof review

There are **no new def, abbrev, structure or instance declarations** in the audited files.
Definition classification for S7-3 is therefore N/A. Existing literal objects were expanded
at use: realNbhd is a strict max-norm tube, realStrip is its product with all lifted angles,
realH and reMap take real parts after real inclusion, Dom is the complex strip/tube,
InClass is holomorphy plus period-one periodicity, and RealOn is reality on real points.
Their total-function carriers introduce no fallback used by these proofs. The frozen real
and complex Hamiltonian fields both have order (∂I H,−∂θ H).

The pre-existing IsActionNorm has all six fields, including the zero and real homogeneity
fields added after design-audit-1 F1. In particular the shifted norm ‖v‖+1 from that earlier
counterexample is excluded. This is not an assumed confinement result.

- **Conjugation, lines 35–133:** hΨreal identifies the real map. Scalar restriction and real
  projection produce its derivative. Equality of the two real-valued maps holds on an open
  neighbourhood, so uniqueness of derivatives gives the full intertwining identity. The
  local Hamiltonian equality yields equality of derivatives on the complex open domain.
  `map_hamiltonianJ_comp` proves the field identity from symplecticity; real_system(b) and
  injectivity of real inclusion transport it to the real field. The chain rule then proves
  HasDerivAt at every orbit time, including endpoints. No inverse map, global injectivity or
  unproved determinant assertion is assumed.
- **Stopped extension, lines 49–152:** on each closed initial segment inside the open strip,
  hF makes the total curve a genuine H orbit, allowing hconf. A first exit tstar>0 would be
  in the closure of the preceding half-open segment; continuity and the closed cylinder
  C={Nrm(I−I₀)≤ϱ} place its value in C⊆W_r, a contradiction. The norm domination and ϱ<r
  prove this strict inclusion. Negative times use the continuous reversed curve, applying
  hconf to original-time orbits on [−s,0]. No assertion that reversal solves F is made.
- **Transfer, lines 179–259:** T2 gives an initial preimage, and T1 plus norm symmetry
  supplies the T3 initial bound. A maximal H′ orbit exists by real_system(c). Its actions
  lie in the closed Nrm ball K on admissible times; K is compact as a closed subset of the
  finite-dimensional max-norm closed ball. The displacement bound and d+ϱ<r′ put K strictly
  inside the real tube. Assuming an admissible t beyond either maximal endpoint places
  all intermediate actions in K (using hadm); periodic continuation contradicts that
  endpoint being finite. Uniqueness identifies the two H orbits on their interval
  intersection. The final triangle estimate uses T1 twice and T3 once, giving ϱ+2d.

Refutation pass: checked the missing-zero norm counterexample against the actual six-field
structure; checked boundary times and singleton intervals against the genuine derivative
predicate; checked negative-time signs and time monotonicity; checked that compactness is
needed only in actions and periodicity is supplied for H′; checked the T3 centre Iy and its
initial d bound; checked both displacement signs in the final estimate. All suspected failure
modes were discharged by the actual premises/proofs. No reportable mathematical finding
remains. This was a separate adversarial pass by the independent auditor, without delegation.

## Verification receipts

All auditor-started Lean/Lake/leanchecker operations were serialized with LEAN_NUM_THREADS=1
and nice level 5. No heartbeat, recursion-depth or synthesis override was used; no clean,
cache, update or library rebuild was requested. The targeted build used the prescribed gate.

```text
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-s73 KAM.Nekhoroshev.Stability.Conjugation \
  KAM.Nekhoroshev.Stability.Transfer
[inp-gate] slot 1 acquired 06:42:10 for ...
Build completed successfully (3214 jobs).
exit 0
```

This was an incremental build with replayed artifacts. Diagnostics were the existing
KAM.ODE.Exit unused NormedSpace section-variable warning and Transfer:174 unused hϱ warning.
No S7-3 sorry warning occurred.

The transient `.lake/abi-scratch/S73Audit1.lean` imported Transfer, opened the source
namespaces and copied the three design headers under fresh names. Its proof applications:

```lean
exact KAM.Stability.conjugation hs hs' hH hHr hH' hH'r
  hΨ hΨmap hΨreal hΨsympl hconj hz
exact KAM.Stability.transfer hs hs' hN hadm hH hHr hH' hH'r
  hΨ hΨmap hΨreal hΨsympl hconj hT1 hT2 hϱ hdϱ hT3
exact KAM.Stability.stopped_extension hN hϱ hϱr hadm hconf hF hJ h0 hz hz0
```

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S73Audit1.lean
'KAM.Stability.conjugation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Stability.stopped_extension' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

```text
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.Nekhoroshev.Stability.Conjugation KAM.Nekhoroshev.Stability.Transfer
replaying KAM.Nekhoroshev.Stability.Transfer
replaying KAM.Nekhoroshev.Stability.Conjugation
exit 0
```

One invocation replayed both requested module names. The mechanical KAM import closure
contains 60 modules, including 19 frozen definition modules and **no frozen theorem modules,
provider modules or DRAFT_SORRY imports**. This also prevents hidden dependence on a pending
root theorem. The allowed axiom lists cover transitive proof dependencies.

```text
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (428 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
exit 1
```

The sole failure is the generated-root diagnostic explicitly excepted by the brief. All
other lint stages pass, including the 100-character limit, frozen byte guard and elaborated
ABI hashes. This is PASS under the stated lint exception, not an unqualified zero-exit lint
receipt.

Both files have the copyright, module command, public imports, module docstring and public
noncomputable section. Total line counts are 141 and 265; maximum Unicode line length is
exactly 100 in each. No forbidden proof escape or resource override appears. No ambient
EuclideanSpace type is used. `git diff --check inp...HEAD` exits 0 with no output, and
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty at intake.

## Notes, errata and closeout

1. `Transfer:174`: “(hϱ : 0 < ϱ)” is unused in transfer's proof. It belongs to the exact design
   and T3 source statement; retain it for fidelity. No correction is needed for this package.
2. Root generation remains the orchestrator's integration task. Its expected lint diagnostic
   does not authorize this auditor to edit KAM.lean.
3. The proof routes differ slightly from the prose plan: conjugation works first with the
   complex field and restricts to reals; stopped-extension uses gen_exit and closed-segment
   arguments instead of explicitly constructing a connected component. These are sound
   implementation choices with unchanged types, not source deviations or errata.

No new suspected pinned-source or blueprint defect was found. No frozen statement was
repaired. No unresolved mathematical uncertainty remains within S7-3. Consumer assembly,
other packages, external pinned-PDF proofs and I/N/P root closure are outside this audit.
The only persistent auditor artifact is this report at the exact user-requested worktree
path. Scratch removal and final hash/status checks are recorded below.

Final closeout: all 8 declarations classified; all 3 public exact-type/axiom checks passed;
kernel replay exit 0; lint has only the permitted generated-root failure; no open finding.
The auditor probe was deleted. Both audited source SHA-256 hashes and package HEAD were
rechecked unchanged. `git diff --check` passes. The final three-dot comparison still adds only
the two S7-3 files; the protected-path diff remains empty. Status contains only the supplied
untracked handoff and this new report.
