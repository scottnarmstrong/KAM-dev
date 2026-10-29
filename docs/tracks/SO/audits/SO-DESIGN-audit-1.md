# SO-DESIGN independent design audit 1

**Verdict: FAIL — revise before releasing the general checker design to implementation.**

Audited worktree `/root/code/KAM-inp-design-so`, HEAD `628569c93a81f4dd9c75ee1696594bc526f7168d`, against `inp` (`836e8efe03c1f2e23422a12dd35058c9bc7101a6`) using the complete `git diff inp...HEAD`. The diff adds only `docs/tracks/SO/design/SO-LEAN-DESIGN.md` (1376 lines). This is a **design verdict**, not a proof-package or seal-readiness verdict. There are no new providers or anchors to seal. The existing `g1_explicit` engine passed the targeted build, axiom probe and kernel replay; that does not establish the proposed checker.

The user's exact report destination overrides both the generic brief's main-worktree destination and the handoff's `SO-DESIGN-design-audit-1.md` filename. Only this report was added to repository content. Scratch probes lived in this worktree's `.lake/abi-scratch/` and were removed. No git state-changing command was used.

Authorities read: AGENTS.md, PLAN, DECISIONS, the package-audit brief, SO-DESIGN handoff and full design/signatures, the pinned SO plan/proposal/pilot, `IG1Body`, `g1_explicit`, their relevant frozen definitions, the track I/N/P statement conventions, and blueprint I's `bpI:p2:g1`. No SO blueprint nodes or frozen SO statements exist in this change; Appendix A is the proposed surface. All six input hashes in the design's input table match current files. Appendix A, the design draft, the existing scratch draft and the main inp draft agree byte-for-byte after accounting for the Markdown fence's terminal newline.

## Numbered findings

### F1 — BLOCKING: the frequency representation makes every n ≥ 3 application vacuous

**Location:** design §1.10 (lines 88–90), §2; Appendix A / `.drafts/design/SOSignatures.lean:649–658` (`CertFreq`, `CertFreq.toReal`), and lines 827–830 (`checkTorusCertificate_sound`).

The scope promises “any `n ≥ 2`” and a “FULLY GENERAL checker”, but every coordinate is `a_i + b_i √d` for rational `a_i,b_i` and a **single** `d`. For `n ≥ 3`, the two rational linear equations

```
Σ k_i a_i = 0,     Σ k_i b_i = 0
```

have a nonzero rational solution. Clearing denominators gives a nonzero integer vector `k` with `k·ωstar = 0`. This includes lower-rank and square-d cases. With `γ > 0`, the frozen `IsDiophantine` inequality has a strictly positive left side for this nonzero `k` and zero right side. Thus no passing certificate in any dimension ≥ 3 can supply the external mathematical premise. A dimension-polymorphic statement is not the promised general black box when its admissible frequencies are all resonant in those dimensions.

**Required change:** provide a frequency interface that can represent rationally independent n-tuples: for example, certified real algebraic coordinates in fields of sufficient degree, or an exact real-vector denotation with a proved enclosure interface. Retain the quadratic implementation as the lunar specialization. Keep Diophantine membership external; do not repair this by weakening it or silently restricting the headline to n=2. Include a genuine n=3 nonresonant design/example.

### F2 — HIGH: the structural reality API omits necessary arithmetic laws

**Location:** Appendix A / draft lines 54–88 (`CertArith`, `LawfulCertArith`), 196–203 (`CertRealPoly.toPoly`, `conjugateSymmetric`, `eval_real`), 457–471 (`CertEmbedding.eval`, `isRealOnReals`).

The proposed conjugate-symmetry and reality theorems quantify over `[CertArith α]` alone. This class is data, with no laws about `ofInt 0` or `neg`; those laws are deliberately in `LawfulCertArith`. The intended half-lattice expansion needs both.

A concrete obstruction is `α = Unit`, `val () = 1`, with every data operation returning `()`. This is a valid raw `CertArith`. Every `CC α` denotes `1+i`; there is no backend representation of imaginary zero or a conjugate coefficient. A nonempty `CertPoly` evaluates at θ=0 to `N(1+i)` for positive integer N. In particular, the promised real constant `P.zero = ()`, `P.half = []` cannot be represented by its intended full polynomial (the empty polynomial denotes zero, not the required real constant 1). No implementation can simultaneously preserve the specified denotation on this carrier and prove the advertised unconditional reality theorem. Discarding input data to make the theorem true would be the forbidden junk-value repair.

**Required change:** add `[LawfulCertArith α]` to reality/conjugate-symmetry results and other correctness results using these laws, or strengthen/restructure the base interface so the needed laws are structural. Add an explicit `toPoly` denotation theorem stating the constant plus conjugate-pair sum. Definitions can remain computational and law-free; their correctness theorems need the appropriate laws. Recheck all inherited/default zero and exact-conjugation uses. Differentiability and periodicity of an already denoted finite complex polynomial do not themselves need arithmetic laws.

### F3 — MEDIUM: the hardest torsion producer-to-consumer contract is absent

**Location:** draft lines 568–590 (`torsionModels`, `torsionAvgCheck_sound`), 804–819 (listed sub-check soundness statements); design §1.9 and §7 SO-TORS/SO-SOUND.

The averaging theorem assumes `hT : T.Encloses … (extendedTorsion H K ω)` and continuity, which are legitimate intermediate premises. But Appendix A gives no `torsionModels_sound` signature producing that enclosure from successful model construction. In particular, its computational `ω : List (CC α)` / `ωRad` inputs are not linked by any stated theorem to the exact real `s • ωstar`, nor is there a stated contract transferring a successful Gram certificate into the derivative-of-inverse formula. Only static/Hamiltonian/invariance sub-check soundness signatures are listed; static soundness itself exports just three of the many required fields.

This is an interface gap, not a claim that the Neumann or averaging inequality is false. It leaves the main unproved assembly obligation hidden inside the global `checkTorusCertificate_hyps` placeholder, despite the design's exact-signature/package-splitting purpose.

**Required change:** state the torsion-model correctness theorem with explicit weight/π validation, successful construction/Gram conditions, componentwise frequency enclosure, exact frequency, and resulting enclosure of the literal frozen extended torsion (including `DH(K)N` and `DN[ω]`). State the remaining sub-check contracts and an acyclic assembly route to every `G1Hyps` field. Do not turn `hT`, Gram invertibility, or torsion continuity into external certificate assumptions.

### F4 — MEDIUM: the zero-error Diophantine toy is not represented by the selected coefficient backends

**Location:** design §8, lines 308–309; §5 and draft `SoBackend`, `CertEmbedding`.

The proposed positive toy uses `K(θ)=(θ,(ν,−ν²/2))`, with `ν ∈ ℚ(√5)`, and promises zero invariance error. For an irrational quadratic ν, neither rational nor dyadic coefficients represent the nonzero constant ν exactly. Degree tagging does not fix this: a rational times an integer power of `2π` is rational at degree zero and transcendental at nonzero degree, never a nonrational algebraic number. Finite nonzero Fourier modes cannot turn an embedding action into that missing constant. Choosing rational ν makes the toy representable, but the reference vector proportional to `(ν,1)` is resonant and cannot support the intended Diophantine black-box application.

**Required change:** use rational approximations with a checked positive residual/energy budget for a genuine Diophantine toy, or explicitly extend the exact coefficient representation. A rational zero-error test can remain a checker-only test if clearly labelled as lacking the external Diophantine premise. Specify the toy's reference vector/ray scalar and distinguish these two tests.

### F5 — MEDIUM: independent Fourier J data require fresh quantitative attachment to pilot margins

**Location:** design §3 (paragraph following upstream interfaces), §6; handoff deviation (b); pilot §§1, 3–5.

The pilot sets `J₀ = −p²/2−V(K)` exactly. The design instead supplies a Fourier polynomial `J̃=J₀+ΔJ`. This is mathematically allowed by G1, but the pilot's full-residual identity and zero energy error no longer apply unchanged. With the other components held fixed,

```
H(K̃) = ΔJ,
(Ẽ − E)_J = −D_(sωstar) ΔJ.
```

The energy-average error is bounded by `sup|ΔJ|`; the new invariance contribution needs `sup|D_(sωstar)ΔJ|`. Embedding/Gram/torsion bounds also need control of derivatives through order two. Tiny unweighted coefficient errors alone do not pay these strip-weighted derivative bills. The report's numerical threshold is about `1.3366e−100`, with a planned common error `1e−103`; no bound for this new ΔJ is supplied in this design. Therefore this audit cannot confirm that deviation (b) stays within the pilot margins.

**Required change:** have SO-GEN produce exact finite data and explicit strip-weighted ΔJ/derivative error budgets, or evaluate all affected sub-checks afresh on the actual four-component candidate. Record those margins independently of the scalar pilot. No exact energy identity may be reused for J̃. This is a pending feasibility attachment, not a proof that the lunar route fails.

### F6 — MEDIUM: distinguish pre-gate interface work from backend implementation

**Location:** design §7, lines 280–304; handoff “can start at once”; controlling SO plan, “Replay gate first” and W1.

The package table makes SO-ARITH depend on the replay verdict and SO-EXPR depend on SO-ARITH, yet the accompanying text starts both immediately. The controlling plan measures replay cost **before the checker is built**. The draft also places `phaseBasis` in NormBridge (§E) although Expr/Diff uses it (§D); the module DAG omits that import.

**Required change:** separate the backend-neutral arithmetic interface from backend implementations and state the scheduling gate explicitly. SO-CONST and the engine-only clock proof can proceed without a backend verdict. Backend-neutral expression syntax/denotation, norm bridges, and interface specifications can proceed once their dependency split is fixed; backend selection, performance-sensitive convolution/model implementation and generated data should await SO-REPLAY. Put `phaseBasis` in a shared basic module or add the actual dependency. This is dependency/scheduling repair, not authorization to launch packages.

## Binder-by-binder engine comparison

The application itself is correct. A scratch copy of the full signatures followed by a proof **without any new `sorry` in that bridge** elaborated: `(g1_explicit …).2.2.2` accepts the fields below in the literal engine order. The bridge returns `CertifiedTorus c`, using `hdisp` for both final inequalities because the engine has `C₂=C₃=isoC2`. Its dependencies still include draft `sorryAx` through unfinished denotations; it is interface validation, not a checker proof.

| Engine binder / conclusion | Draft field / attachment | Verdict |
|---|---|---|
| n≥2; τ≥n−1; 0<ρinf<ρ | `hn`, `hτ`, `hρinf`, `hρinfρ` | PASS (shape) |
| positive M, σK, σB, σT, μ, γbar; 1<σω; 0<ν; ωstar≠0 | corresponding fields through `hωstar` | PASS (shape) |
| D,H,K,s,γ,e,E₀ | `c.D,c.H,c.K,c.params.s,c.params.γ,c.params.err,c.params.E0` | PASS |
| open D; integer-translation membership | `hopen`, `htransl` | PASS |
| H holomorphic, periodic, real | `hholo`, `hper`, `hreal` | PASS (F2 affects structural proof of K reality) |
| five norms ≤M, in frozen conjunction order | `hbd`: DH, XH, DXH, D²XH, D²H | PASS |
| K holomorphic, primary, real | `hK`, `hKp`, `hKr` | PASS (shape); F2 |
| μ-ball containment; DK≤σK−μ | `hball`, `hDK` | PASS |
| Gram determinant unit and inverse row sums | `hG` | PASS |
| averaged extended torsion determinant unit; inverse row sums | `hTu`, `hTb` | PASS (shape); F3 |
| 1<s<σω; both ν ray margins | `hs1`, `hsσ`, `hν1`, `hν2` | PASS |
| 0<γ≤γbar; Diophantine reference vector | `hγ`, `hγγbar`, external `hdio` on **ωstar**, not sωstar | PASS (shape); F1 |
| e≥0; full vector invariance error; energy-average error | `he0`, `hE`, `hEn` | PASS (shape); F5 |
| C₁e/(γ⁴ρ^(4τ))<1 | `hC1`, exact isoC1 parameter order μ,ν,γbar | PASS |
| entire IG1Body conclusion, including pointwise energy, half margins and frequency displacement | `CertifiedTorus`, both bounds enlarged via `hdisp` | PASS |

`nuRay` is the engine's margin ν; the lunar rotation ν± is in `ωstar`. For the lunar instantiation, `s=2`, `ωstar=(ν±/2,1/2)` gives input frequency `(ν±,1)`. The clock lemma forces the exact output ray scalar to 2. No conclusion-shaped hypothesis appears in `TorusCertificate`: it carries numerical data/witnesses, not proofs of invertibility, residual bounds, exact tori, or G1. `G1Hyps` is a derived proposition, not an input to the public soundness theorem. `LawfulCertArith` is a backend correctness premise, to be proved once; “only external mathematical input” is accurate only with that standard backend qualification.

## Semantic and lunar assessment

- **Hamiltonian semantics:** the displayed recursive `HamExpr.eval` is the intended entire, real-on-reals, angle-periodic function for every constructor. Integer modes have the correct period-one `2π`. No denominator singularities are hidden. Excluding division is a sound v1 language restriction, but O2 remains an explicit scope ruling; this language does not represent every analytic expression on a restricted domain (e.g. arbitrary inverses). Do not call that broader coverage approved by this audit. The natural τ restriction is explicit; a client with a real Diophantine exponent needs its own justified conversion before using a natural exponent.
- **Open strips:** there is no closed-strip mismatch. Frozen `complexStrip` is `∀ i, |Im θ_i|<ρ`; IG1Body quantifies on exactly this open strip. Uniform pointwise model radii suffice. Real unit-cube averages lie inside it when ρ>0. Non-strict checked clearance inequalities are sufficient because the input strip and metric μ-ball are strict. Empty-strip/vacuous enclosures must not feed real-point bounds: static checks must establish positive widths (and positivity guards must accompany standalone consumers as needed).
- **Models and degree tags:** the Encloses formula correctly bounds the function minus the scaled polynomial, with positive real `(2π)^deg`. Exact list sums/filter-sums handle duplicates and short/padded keys on the whole carrier; no sortedness is needed for their denotation. Optimized algorithms must validate/canonicalize key lengths and shapes before relying on them. Finite products plus weighted discarded terms give a sound sup model. Negative degrees need lower π bounds when forming upper reciprocal bounds; “uses piUpQ” in `supBound`'s comment alone is insufficient. Use validated positive intervals or the global coarse lower bound. General mixed-degree cancellation may require the optional high-precision π package; coarse bounds preserve soundness but need not preserve feasibility.
- **Exponential witnesses:** the analytic mechanism is sound. Apply the residual argument to the degree-zero polynomial part g₀, not to an unknown-radius tail's derivative. If `|g₀|≤B`, pin error ε₀ and residual bounds r_j give a conservative error `exp(2B)(ε₀+Σ_j(1/2+ρ)r_j)` on the strip; add `exp(B)(exp(η)−1)` for an argument tail of radius η. Periodic representatives and their straight segments stay inside the convex strip. The scalar pin is necessary. Sharing a character witness is legitimate only for identical normalized `k·U`; retaining the external character shift is essential. The current signatures leave the constants/halving implementation unproved; no actual replay/slack conclusion follows from the analytic mechanism alone.
- **Gram/torsion:** a square-matrix left-inverse Neumann defect `‖1−BG‖<1` is sufficient; the bounds β/(1−δ) and δβ/(1−δ) are correct. No Hermitian positivity is needed or justified. The frozen bilinear Gram and the extended torsion's last row `DH(K)N` are the right objects. Differentiating the inverse using `−G⁻¹(DG)G⁻¹`, rather than differentiating an unknown enclosure remainder, is the right route. Entrywise zero modes plus radii enclose the average, and `‖1−SC‖+‖S‖‖R‖<1` pays the averaged inverse defect. F3 is the missing formal contract between these valid ingredients.
- **Positivity:** an SOS check must actually pay the residual: from `Re f−m₀=|g|²+h`, `|h|≤r`, one gets `Re f≥m₀−r`. To certify m, check `m≤m₀−r`; a small residual without this slack does not imply `Re f≥m₀`. The current body is unspecified, so this is an implementation requirement rather than a demonstrated accepting counterexample.
- **Lunar geometry/global solutions:** the clock plus transferred positive θ₀-derivative gives the proposed continuous graph, since the clock angle differs from θ₁ by a constant and the lifted q-map has degree one. Cauchy on the output strip gives the real derivative transfer `disp/rhoInf`; the graph check must enforce a strict positive remaining monotonicity margin. Candidate p-bounds widen by disp directly, without graph-error transport. Two continuous ordered invariant graphs give an invariant open slab. The smooth globally Lipschitz physical field admits unique global solutions; alternatively bounded p and periodic force give continuation in both directions. The generic `so_confinement` permits arbitrary barrier ranges, so its proof cannot universally use the lunar-only `|p|≤2` set: use a bound derived from the barrier endpoints or global Lipschitz existence.
- **D30:** the proposed final signatures have the correct 33/1000 bound, all real times, any initial angles, a nonempty momentum window, and uniqueness among global solutions. The pilot's extrema leave about 0.001 headroom in the 3.3% band and numerically suggest `(0.9819,1.0181)` as a window, but neither is certified here. O1 changes the proposal's graph-defined initial region to a smaller constant window; that is a reported deviation, not silently equivalent to proposal §3.2. Literal rational endpoints and O1 approval must precede the final statement freeze. Upper-certificate ham/pass/graph-pass companions, omitted from the displayed lower-only list, are also needed in the implementation.

## Feasibility and package order

The broad 21–37k plan allowance is plausible as a planning range, not independently established by signature elaboration. The table actually sums to **14,900** hand-written lines including optional SO-PI, excluding wave 0; adding the stated ≈1,500 wave-0 lines gives ≈16,400. Thus “16–17k plus wave 0” double-counts some allowance or needs clarification. A 30–40% overrun on the inclusive figure gives roughly 21–23k. SO-EXPR's third-order shared jet correctness, fixed-point polynomial error accounting, SO-EXPW's complex path argument, torsion continuity/derivative models, and graph inversion are substantial estimation risks. Splitting files as shown can respect the 1500-line cap, but the estimates do not prove this.

SO-CONST, the engine-only part of SO-CLOCK, basic syntax/semantics/norm bridges and interface drafting are useful backend-independent work (subject to F2/F6). The backend implementation, convolution strategy, shard sizes and data proofs need actual SO-REPLAY results at the generator's support/precision. The current one-polynomial witness interface also needs to make any proposed `exp(g/2)`/squaring fallback concrete before counting on it. No replay timings, support-size measurements, roundoff budgets, or valid n≥3 example were supplied. Neither a one-hour stage target nor tiny pilot residuals establish feasibility of kernel reduction.

## Checks and exact results

No Lean/Lake/kernel commands were launched concurrently by this audit. Signature, bridge, targeted engine build, kernel replay, and the final lint/ABI run were serialized. Direct signature/build/kernel commands and the final lint used `LEAN_NUM_THREADS=1` and `nice -n 5`; the signature/build wrappers supply `nice` themselves. Execution deviation: an initial direct lint run omitted the explicit environment/nice prefix and also passed; it was repeated under the required prefix below because lint internally launches an ABI Lean probe. There was no overlapping audit-launched Lean process.

1. `git diff inp...HEAD` — inspected the entire one-file addition, including Appendix A. `git diff --stat inp...HEAD`: `1 file changed, 1376 insertions(+)`.
2. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` — empty. No package import/proof/anchor changes exist. Provider=frozen-type and seal-body probes therefore have no new provider target.
3. `git diff --check inp...HEAD` — exit 0, no output.
4. Six `sha256sum` results match the design's input pins. Appendix extraction and draft byte comparisons: true for the local design draft, local existing scratch draft and `/root/code/KAM-inp/.drafts/design/SOSignatures.lean`.
5. Exact handoff rerun:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-so .drafts/scratch/SOSignatures.lean
   ```

   Exit **0**; **109** diagnostics saying “warning: declaration uses `sorry`”; **0** errors. Full captured output: `/tmp/SO-DESIGN-audit-1-signatures.log`. This establishes elaboration only. The existing scratch draft was read, not modified.
6. G1 bridge and all 66 explicit draft theorem axiom probes, appended to a copy in `.lake/abi-scratch/SODesignAudit.lean`, run with:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-so .lake/abi-scratch/SODesignAudit.lean
   ```

   Exit **0**, no errors. The bridge proof applies every engine field in the table above and enlarges both output bounds using `hdisp`. Full output: `/tmp/SO-DESIGN-audit-1-probe.log`. Exact engine output:

   ```text
   'KAM.Iso.Apost.g1_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
   '_private._stdin.0.auditG1' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
   ```

   Of the 66 draft theorem outputs, 65 are exactly `[propext, sorryAx, Classical.choice, Quot.sound]` and `lunarPLo_lt_lunarPHi` is exactly `[sorryAx]`. The declaration inventory below maps each to its output. This is expected for a transient design draft; **none is proof-closed**. In particular the draft black-box and lunar conclusions have `sorryAx`. The bridge's `sorryAx` comes through draft definitions; its own proof contains no placeholder.
7. Targeted existing engine build:

   ```sh
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-design-so KAM.Iso.Apost.G1
   ```

   Exit **0**:

   ```text
   [inp-gate] slot 1 acquired 11:09:57 for KAM.Iso.Apost.G1
   Build completed successfully (3224 jobs).
   ```

   This was the targeted existing dependency closure using the worktree snapshot, not a clean/library-wide rebuild. There are no new production SO modules to build.
8. Kernel replay:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Iso.Apost.G1
   ```

   Exit **0**, exact output `replaying KAM.Iso.Apost.G1`. No proposed checker/provider module exists for replay; replaying unfinished signatures would not prove their claims.
9. Final lint:

   ```sh
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **0**, exact output:

   ```text
   check_lean_modules: PASS (1281 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No generated-root exception was needed. Lint excludes `.drafts`; its success does not sanction importing a draft into production. The draft is 1008 physical lines, has copyright, `module`, nine `public import`s, module docstring and exposed public noncomputable section. A comment/string-masked scan found no forbidden escape/resource-override tokens or `EuclideanSpace` in draft code. `sorry` placeholders are confined to this excluded transient design surface, not newly added production Lean. A declaration scan found no reused undotted draft name in the current KAM tree; dotted API names are intentional. Stand-in SO-MODEL/SO-DIO names require reconciliation when those sibling implementations land; this audit's elaboration uses the actual current baseline and cannot prove future sibling compatibility.

## Definition classification and declaration inventory

All **173 explicit declarations** are listed below; automatically generated structure projections/constructors inherit their parent's classification. Verdicts here concern design fidelity, not proved status. “PASS WITH NOTES / placeholder” means the proposed object/statement is intelligible but its body is unfinished and no theorem is accepted as proved. “Concrete” means the displayed body can be inspected on its whole carrier. Data structures contain data, except the explicitly propositional backend laws and derived G1 hypotheses. Missing list entries have the documented zero/default meaning; optimizations must check shapes as described above.

Concrete denotations/checks: `CC.toC`, π rationals, square-root checker, key padding, polynomial eval/filter-coeff, weight checker (depending on unfinished exp bounds), model/matrix enclosure predicates, phase basis/index, recursive Hamiltonian eval, domain, embedding eval (depending on unfinished real-poly expansion), frequency denotation (F1), certificate projections, conjunction of sub-checks, `CertifiedTorus`, upstream finite-model formulas and `soHamExpr`. Placeholder bodies: backend instances, transcendental bounds, polynomial/model algorithms, jets/SLP/majorants/composition, Gram/torsion construction and checks, constants, positivity, all individual checker bodies, lunar data/window endpoints. No claim that those placeholders compute the intended objects is accepted. The proposed raw-backend real-poly semantics fail F2; frequency semantics are exactly the written object but fail the advertised generality F1.

Axiom codes are exact normalized `#print axioms` output: **S** = `[propext, sorryAx, Classical.choice, Quot.sound]`; **s** = `[sorryAx]`; **—** = not an explicitly probed theorem. Locations are draft line numbers, also locating the verbatim Appendix A. Package letters follow Appendix A §§A–I; the design itself is the node authority for these new names.

| Node | Lean declaration (draft line) | Verdict | Classification / note; axioms |
|---|---|---|---|
| SO-A | `KAM.Certificate.CertArith` (54) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-A | `KAM.Certificate.LawfulCertArith` (73) | PASS WITH NOTES | Backend laws (Prop); — |
| SO-A | `KAM.Certificate.CC` (93) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-A | `KAM.Certificate.CC.toC` (98) | PASS WITH NOTES | Concrete body; — |
| SO-A | `KAM.Certificate.instCertArithRat` (101) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-A | `KAM.Certificate.instLawfulCertArithRat` (103) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-A | `KAM.Certificate.CertFixed` (106) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-A | `KAM.Certificate.instCertArithFixed` (109) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-A | `KAM.Certificate.instLawfulCertArithFixed` (111) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-A | `KAM.Certificate.ratExpUp` (117) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-A | `KAM.Certificate.exp_le_ratExpUp` (119) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-A | `KAM.Certificate.piLoQ` (123) | PASS WITH NOTES | Concrete body; — |
| SO-A | `KAM.Certificate.piUpQ` (125) | PASS WITH NOTES | Concrete body; — |
| SO-A | `KAM.Certificate.piLoQ_lt_pi` (127) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-A | `KAM.Certificate.pi_lt_piUpQ` (129) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-A | `KAM.Certificate.PiEnclosure` (133) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-A | `KAM.Certificate.checkPiEnclosure` (139) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-A | `KAM.Certificate.checkPiEnclosure_sound` (141) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-A | `KAM.Certificate.checkSqrtEnclosure` (145) | PASS WITH NOTES | Concrete body; — |
| SO-A | `KAM.Certificate.sqrt_mem_of_checkSqrtEnclosure` (148) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-A | `KAM.Certificate.certCExp` (154) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-A | `KAM.Certificate.certCExp_sound` (156) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-B | `KAM.Certificate.CertKey` (163) | PASS WITH NOTES | Concrete body; — |
| SO-B | `KAM.Certificate.certKeyFun` (166) | PASS WITH NOTES | Concrete body; — |
| SO-B | `KAM.Certificate.CertPoly` (169) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-B | `KAM.Certificate.CertPoly.eval` (173) | PASS WITH NOTES | Concrete body; — |
| SO-B | `KAM.Certificate.CertPoly.coeff` (177) | PASS WITH NOTES | Concrete body; — |
| SO-B | `KAM.Certificate.CertPoly.eval_eq_fourierSum` (181) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-B | `KAM.Certificate.CertPoly.differentiable_eval` (184) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-B | `KAM.Certificate.CertPoly.eval_add_int` (187) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-B | `KAM.Certificate.CertRealPoly` (191) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-B | `KAM.Certificate.CertRealPoly.toPoly` (196) | FAIL | Algorithm / data placeholder; —; F2 |
| SO-B | `KAM.Certificate.CertRealPoly.conjugateSymmetric` (198) | FAIL | Statement reviewed; proof placeholder; S; F2 |
| SO-B | `KAM.Certificate.CertRealPoly.eval_real` (201) | FAIL | Statement reviewed; proof placeholder; S; F2 |
| SO-B | `KAM.Certificate.CertPoly.add` (205) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-B | `KAM.Certificate.CertPoly.derivNo2pi` (209) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-B | `KAM.Certificate.CertPoly.shift` (212) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-B | `KAM.Certificate.CertPoly.conjReflect` (215) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-C | `KAM.Certificate.CertWeight` (220) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-C | `KAM.Certificate.checkWeight` (225) | PASS WITH NOTES | Concrete body; — |
| SO-C | `KAM.Certificate.norm_character_le_weight` (228) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-C | `KAM.Certificate.CertModel` (234) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-C | `KAM.Certificate.CertModel.Encloses` (240) | PASS WITH NOTES | Concrete body; — |
| SO-C | `KAM.Certificate.CertModel.supBound` (246) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-C | `KAM.Certificate.CertModel.norm_le_supBound` (248) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-C | `KAM.Certificate.ModelConfig` (254) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-C | `KAM.Certificate.CertModel.add` (261) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-C | `KAM.Certificate.CertModel.mul` (264) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-C | `KAM.Certificate.CertModel.trim` (268) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-C | `KAM.Certificate.CertModel.toDeg` (273) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-C | `KAM.Certificate.CertModel.Encloses.add` (276) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-C | `KAM.Certificate.CertModel.Encloses.mul` (281) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-C | `KAM.Certificate.CertModel.Encloses.trim` (286) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-C | `KAM.Certificate.CertModel.Encloses.toDeg` (291) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-C | `KAM.Certificate.CertModel.Encloses.average` (297) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-C | `KAM.Certificate.expWitnessRadius` (315) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-C | `KAM.Certificate.expWitness_sound` (318) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-D | `KAM.Certificate.phaseBasis` (328) | PASS WITH NOTES | Concrete body; — |
| SO-D | `KAM.Certificate.HamExpr` (335) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-D | `KAM.Certificate.modePhase` (349) | PASS WITH NOTES | Concrete body; — |
| SO-D | `KAM.Certificate.HamExpr.eval` (353) | PASS WITH NOTES | Concrete body; — |
| SO-D | `KAM.Certificate.HamExpr.contDiff_eval` (366) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-D | `KAM.Certificate.HamExpr.eval_add_int` (368) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-D | `KAM.Certificate.HamExpr.eval_real` (371) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-D | `KAM.Certificate.SlpOp` (376) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-D | `KAM.Certificate.Slp` (384) | PASS WITH NOTES | Data / syntax carrier; —; structural evaluation / table shape must be paid |
| SO-D | `KAM.Certificate.Slp.val` (388) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-D | `KAM.Certificate.HamJet` (393) | PASS WITH NOTES | Data / syntax carrier; —; structural evaluation / table shape must be paid |
| SO-D | `KAM.Certificate.phaseNat` (401) | PASS WITH NOTES | Concrete body; — |
| SO-D | `KAM.Certificate.HamExpr.jet` (405) | PASS WITH NOTES | Algorithm / data placeholder; —; structural evaluation / table shape must be paid |
| SO-D | `KAM.Certificate.HamExpr.jet_v0` (407) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-D | `KAM.Certificate.HamExpr.jet_d1` (410) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-D | `KAM.Certificate.HamExpr.jet_d2` (415) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-D | `KAM.Certificate.HamExpr.jet_d3` (420) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-D | `KAM.Certificate.certDomain` (427) | PASS WITH NOTES | Concrete body; — |
| SO-D | `KAM.Certificate.isOpen_certDomain` (432) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-D | `KAM.Certificate.certDomain_add_int` (435) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-D | `KAM.Certificate.Slp.majorants` (442) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-D | `KAM.Certificate.Slp.norm_val_le_majorant` (445) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-D | `KAM.Certificate.CertEmbedding` (451) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-D | `KAM.Certificate.CertEmbedding.eval` (457) | PASS WITH NOTES | Concrete body; — |
| SO-D | `KAM.Certificate.CertEmbedding.differentiable_eval` (464) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-D | `KAM.Certificate.CertEmbedding.isPrimaryOnStrip` (467) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-D | `KAM.Certificate.CertEmbedding.isRealOnReals` (470) | FAIL | Statement reviewed; proof placeholder; S; F2 |
| SO-D | `KAM.Certificate.Witnesses` (476) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-D | `KAM.Certificate.Slp.compose` (482) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-D | `KAM.Certificate.Slp.compose_sound` (486) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-E | `KAM.Certificate.norm_fderiv_le_sum_partials` (496) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-E | `KAM.Certificate.norm_iteratedFDeriv_two_le_sum_partials` (500) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-E | `KAM.Certificate.hamiltonianVectorFieldℂ_sumVec` (507) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-E | `KAM.Certificate.norm_fderiv_hamiltonianVectorFieldℂ_le` (514) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-E | `KAM.Certificate.norm_iteratedFDeriv_two_hamiltonianVectorFieldℂ_le` (521) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-F | `KAM.Certificate.matrix_inv_of_approx_inverse` (531) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-F | `KAM.Certificate.ModelMatrix` (536) | PASS WITH NOTES | Concrete body; — |
| SO-F | `KAM.Certificate.ModelMatrix.Encloses` (539) | PASS WITH NOTES | Concrete body; — |
| SO-F | `KAM.Certificate.gramModels` (545) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-F | `KAM.Certificate.gramModels_sound` (548) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-F | `KAM.Certificate.gramCheck` (556) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-F | `KAM.Certificate.gramCheck_sound` (560) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-F | `KAM.Certificate.torsionModels` (571) | PASS WITH NOTES | Algorithm / data placeholder; —; F3 |
| SO-F | `KAM.Certificate.torsionAvgCheck` (578) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-F | `KAM.Certificate.torsionAvgCheck_sound` (581) | PASS WITH NOTES | Statement reviewed; proof placeholder; S; F3 |
| SO-F | `KAM.Certificate.cRUpQ` (593) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-F | `KAM.Certificate.cR_le_cRUpQ` (595) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-F | `KAM.Certificate.isoC1Q` (599) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-F | `KAM.Certificate.isoC2Q` (601) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-F | `KAM.Certificate.isoC1_le_isoC1Q` (603) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-F | `KAM.Certificate.isoC2_le_isoC2Q` (609) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-F | `KAM.Certificate.checkRealLowerBound` (616) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-F | `KAM.Certificate.checkRealLowerBound_sound` (619) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-G | `KAM.Certificate.CertParams` (629) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-G | `KAM.Certificate.CertFreq` (649) | FAIL | Data / syntax carrier; —; F1 |
| SO-G | `KAM.Certificate.CertFreq.toReal` (655) | FAIL | Concrete body; —; F1 |
| SO-G | `KAM.Certificate.TorusCertificate` (660) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-G | `KAM.Certificate.TorusCertificate.D` (685) | PASS WITH NOTES | Concrete body; — |
| SO-G | `KAM.Certificate.TorusCertificate.H` (688) | PASS WITH NOTES | Concrete body; — |
| SO-G | `KAM.Certificate.TorusCertificate.K` (690) | PASS WITH NOTES | Concrete body; — |
| SO-G | `KAM.Certificate.TorusCertificate.ωstar` (693) | PASS WITH NOTES | Concrete body; — |
| SO-G | `KAM.Certificate.checkStatic` (701) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-G | `KAM.Certificate.checkHamBounds` (704) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-G | `KAM.Certificate.checkEmbedding` (707) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-G | `KAM.Certificate.checkInvariance` (710) | PASS WITH NOTES | Algorithm / data placeholder; —; F5 |
| SO-G | `KAM.Certificate.checkEnergy` (713) | PASS WITH NOTES | Algorithm / data placeholder; —; F5 |
| SO-G | `KAM.Certificate.checkGram` (716) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-G | `KAM.Certificate.checkTorsion` (719) | PASS WITH NOTES | Algorithm / data placeholder; —; F3 |
| SO-G | `KAM.Certificate.checkSmallness` (722) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-G | `KAM.Certificate.checkTorusCertificate` (726) | PASS WITH NOTES | Concrete body; — |
| SO-G | `KAM.Certificate.G1Hyps` (736) | PASS WITH NOTES | Derived engine hypotheses (Prop); — |
| SO-G | `KAM.Certificate.CertifiedTorus` (789) | PASS WITH NOTES | Concrete body; —; engine shape PASS, generality F1 |
| SO-G | `KAM.Certificate.checkStatic_sound` (804) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-G | `KAM.Certificate.checkHamBounds_sound` (807) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-G | `KAM.Certificate.checkInvariance_sound` (813) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-G | `KAM.Certificate.checkTorusCertificate_hyps` (818) | PASS WITH NOTES | Statement reviewed; proof placeholder; S; F3 |
| SO-G | `KAM.Certificate.checkTorusCertificate_sound` (827) | PASS WITH NOTES | Statement reviewed; proof placeholder; S; engine shape PASS, generality F1 |
| SO-H | `KAM.Certificate.clock_frequency` (838) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-I | `KAM.SpinOrbit.soEcc` (861) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.soEps` (863) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.soCoeffPoly` (865) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.soEccQ` (875) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.soEpsQ` (877) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.soAQ` (879) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.soA` (881) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.soModes` (883) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.soV` (885) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.soVC` (888) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.soField` (891) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.lunarG` (894) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.lunarNuMinus` (896) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.lunarNuPlus` (898) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.lunarNuMinus_half_isDiophantine` (900) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-I | `KAM.SpinOrbit.lunarNuPlus_half_isDiophantine` (903) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-I | `KAM.SpinOrbit.soHamC` (908) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.soHamExpr` (913) | PASS WITH NOTES | Concrete body; — |
| SO-I | `KAM.SpinOrbit.soHamExpr_eval` (919) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-I | `KAM.SpinOrbit.soHamExpr_clock` (921) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-I | `KAM.SpinOrbit.SoBarrier` (927) | PASS WITH NOTES | Conditional barrier semantics with proofs; — |
| SO-I | `KAM.SpinOrbit.SoGraphCert` (938) | PASS WITH NOTES | Data / syntax carrier; — |
| SO-I | `KAM.SpinOrbit.checkSoGraph` (947) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-I | `KAM.SpinOrbit.soBarrier_of_cert` (950) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-I | `KAM.SpinOrbit.so_confinement` (959) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-I | `KAM.SpinOrbit.SoBackend` (968) | PASS WITH NOTES | Concrete body; —; replay-dependent placeholder choice |
| SO-I | `KAM.SpinOrbit.lunarLowerCert` (971) | PASS WITH NOTES | Algorithm / data placeholder; —; F5 |
| SO-I | `KAM.SpinOrbit.lunarUpperCert` (973) | PASS WITH NOTES | Algorithm / data placeholder; —; F5 |
| SO-I | `KAM.SpinOrbit.lunarLowerCert_ham` (975) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-I | `KAM.SpinOrbit.lunarLowerCert_passes` (977) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-I | `KAM.SpinOrbit.lunarLowerGraph_passes` (979) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-I | `KAM.SpinOrbit.lunarLowerCert_ωstar` (981) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-I | `KAM.SpinOrbit.lunarUpperCert_ωstar` (983) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-I | `KAM.SpinOrbit.lunarPLo` (986) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-I | `KAM.SpinOrbit.lunarPHi` (988) | PASS WITH NOTES | Algorithm / data placeholder; — |
| SO-I | `KAM.SpinOrbit.lunarPLo_lt_lunarPHi` (990) | PASS WITH NOTES | Statement reviewed; proof placeholder; s |
| SO-I | `KAM.SpinOrbit.lunar_barriers` (993) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |
| SO-I | `KAM.SpinOrbit.lunar_spin_confinement` (1000) | PASS WITH NOTES | Statement reviewed; proof placeholder; S |

## Source defects, deviations and remaining uncertainty

No new suspected defect in a pinned mathematical source or frozen declaration was established. The pilot already records the unresolved discrepancy between the proposal/book's displayed 3% band and the chosen finite model's numerical ≈3.2% extrema; D30 explicitly adopts 3.3%. This audit does not independently refute that book or certify the numerical extrema.

The defects newly established here are in the proposed design: the quoted “any n≥2” promise versus the single-quadratic-field carrier (F1), and law-free reality versus the intended real Fourier denotation (F2). These should be recorded as design corrections, not source errata. Reported deviations remain: constant-window O1 instead of graph-error transport; Fourier J instead of exact energy lifting (F5); bounded J polydisc instead of the pilot's unrestricted auxiliary action. The last change is harmless for this Hamiltonian's derivative bounds because they are independent of J, provided the candidate and its μ-neighborhood actually fit in the chosen polydisc. Division-free syntax and deferred analytic graphs/conjugacy remain explicit scope questions, not silent replacements of the requested theorem.

Uncertainties: replay cost/depth and sharding, backend choice, actual weighted J budgets, averaged torsion enclosure margins, mixed-degree/exp-pin losses, final literal initial window, and corrected general-frequency interfaces. **The lunar route remains a credible conditional design; the general black box is not ready with the present signatures.** No frozen text, manifest, provider, generated root or README was edited.
