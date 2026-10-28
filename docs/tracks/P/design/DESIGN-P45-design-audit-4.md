# P45 revision 4: independent delta design audit

Overall verdict: **PASS**, for the corrected revision-4 design contract. The P5-EX counterexample is valid; the added closed-cylinder premise repairs its cause without changing the frozen theorem or losing a required consumer. `h0real` is unaffected. Fresh signature elaboration passes. This is a design audit, not a proof of `ext` or approval of completed package proofs.

## Scope, authority and frozen inputs

The orchestrator's clarification supersedes the initial request to reopen audit 3: audit **only** revision 4, answering its five stated questions. Audit 3 was background, not the finding being repaired. Read AGENTS.md, PLAN, DECISIONS, the design-audit brief, revision-4 diff, P5-EX handoff, shared signatures, relevant blueprint/graph contracts, frozen definitions, and downstream signature uses. Tier 2 correspondence audit, with a separate adversarial mathematical pass below. No implementation or source repair is authorized; only this report persists. Temporary validation files live under `.lake/abi-scratch/` and are removed.

Snapshot: HEAD `6cf8652ace2fb8b03966267d8eb72168fb4d94b7`; immediate predecessor `408ea7a6f026a1ecf1d0cf0e988bdc54494497f9` (the prior audited design revision was `e1281e008078f0ce080cfd0d4a167f092ad8d01c`). SHA256:

| Input | SHA256 |
|---|---|
| `docs/tracks/P/design/P45-LEAN-DESIGN.md` | `fe084af07ac93f216e4f98e0ff5284319c5a544ee6df073af2069e9639d47559` |
| `/root/code/KAM-inp/.drafts/design/P45Signatures.lean` | `6f3ac05b5f71bca24343c84aa3df51812acac3f518381c5ae9ef645b2355c402` |
| `.drafts/handoff-DESIGN-P45.md` | `12f1f72cc3b07774be912f3ebd9d786f79295ad41e0a9366bff7d252c6257954` |
| `blueprint-P/parts/p5-pg-assembly.tex` | `f8a5bc1683f30fed2576d0bb1ab6d51a1e6f00c6bf78c180d5a32efb0cef9968` |
| `docs/graph/P/packets/P-p5.nodes.md` | `5cc05f8653bdaba44ae161f09f820e505b7534ae2a5a03c21a41b4d0369556c2` |

`S:L` below means the shared signatures at this hash. The Markdown appendix is byte-identical to that file. Independent comparison with the predecessor's appendix finds **exactly one changed line**, S:556: addition of `w ∈ closure (cylinder d.V d.r0) →` to `PGExtension.agrees`. No other declaration or fixture changes. The design diff also adds the Revision 4 explanation at lines 1986–2002.

## 1. Counterexample against revision 3: valid

Here is a fully specified mathematical instance of the handoff's construction. Take `a=b=1`, `V=(0,1)`, `W=(-1,2)`, `r0=mu0=B=1`, and `H0(I)=I²/2`. Write `J=(p²+q²)/2` and set `Pper=J²/2`, `P0=Omega=0`, `beta=[1]`, independently of mu. All fast-angle periods are `2*pi`.

Let `C=closure (cylinder V 1)` and `t(w)=dist(w,C)` in the specified max norm. With phi the fast angle, put

```text
W0 = {w : t(w) < 1/(1+|phi(w)|)},
P(mu,w) = Pper(w) + indicator_{w outside W0 and t(w)<1/2}(w).
```

`W0` is open and contains all of `C`. Hence `P=Pper` on an open neighbourhood of each constrained point, including coupling endpoints: the joint `AnalyticOnNhd` hypothesis holds. On the cylinder the perturbation is identically zero, so frozen periodicity, the exact secular average and Birkhoff expansion, symmetry and the determinant bound all hold. The fast frequency is the identity on `W`, with smooth inverse. The interval is open, bounded and connected; its two boundary points give the required boundary-layer bound, for example `A=4`. Thus this is actual `PGData`, not merely a periodicity counterexample missing the other hypotheses.

For any proposed positive delta, choose `0<t<min(delta,1/2)`. At `I=1+t`, `p=q=0`, compare phi=0 with phi=`2*pi*m`, where m is sufficiently large that `1/(1+2*pi*m)≤t`. Both points lie in `extensionDomain d delta`, witnessed by the corresponding point at `I=1` with the same angle. Their source values are respectively 0 and 1. Revision-3 `agrees` identifies both values with the extension; `periodic` identifies the extension values with one another. Contradiction. This disproves revision-3 `ext` for every delta, without needing holomorphy or the uniform bound.

Adversarial checks: the discontinuity is outside the constrained closed cylinder; analyticity is local, so the shrinking angle-dependent neighbourhood is allowed. The frozen cylinder uses oscillator discs rather than the max-norm oscillator box, but both selected oscillators are zero, so this distinction does not invalidate the example. The example is independent of mu, so joint parameter analyticity adds no obstruction.

## 2. Amendment and existence: correct, minimal local repair

The revised field is:

```lean
agrees : ∀ mu ∈ Icc 0 d.mu0, ∀ w : Phase (a+b),
  w ∈ closure (cylinder d.V d.r0) →
  KAM.realInclusion₂ (a+b) w ∈ extensionDomain d delta →
    P mu (KAM.realInclusion₂ (a+b) w) = (d.P mu w : ℂ)
```

This is a minimal one-premise edit of the faulty field. It does not add a premise to `PGData` or frozen P-G: `PGExtension` is a produced witness. Open-cylinder agreement alone would serve the consumers, but closure agreement is also justified and retains more of the intended identification. “Minimal” here means the local contract repair, not uniqueness of a logically weakest possible specification.

The amended `ext` is mathematically provable from `PGData` by the intended construction:

1. Restrict to the compact real parameter/angle box: mu in `[0,mu0]`, fast actions in `closure V`, fast angles in `[0,2*pi]^a`, oscillator max norm at most `r0/2`. This lies in the closed frozen cylinder because each oscillator disc satisfies `p_j²+q_j²≤r0²/2<r0²`. Compact real complexification gives a common tube and bound, including joint continuity in mu.
2. Frozen periodicity extends to the closed cylinder by continuity and density. For finitely many neighbouring fundamental cells, translated analytic germs agree near their common constrained real points: the difference vanishes on a nonempty open real subset of the cylinder, then the real-slice identity theorem makes the complex germs agree. Shrink the tube uniformly over the compact box. This is a germ argument; it does **not** assert periodicity of the total source function throughout a uniform tube at all angles.
3. Glue and periodize those germs, then restrict to `extensionDomain` with smaller positive delta. Periodicity and boundedness follow from the compact fundamental construction. At a constrained real point in this domain, reduction by a lattice shift stays in the closed cylinder. Agreement with the original function there follows from the local extension and closed-cylinder periodicity. No source values outside that cylinder are prescribed.
4. Intersect the chosen positive radius with the independent `H0` extension radius and the bound delta<1. Shrinking preserves the required properties and allows uniform derivative bounds by Cauchy estimates.

For the explicit counterexample, the complex polynomial `Pper` itself now supplies the perturbation extension: it agrees on the closed cylinder and is periodic, holomorphic and uniformly bounded on a sufficiently small extension tube. Thus the old counterexample directly ceases to obstruct the repaired statement.

This establishes the existence route, not an elaborated Lean proof body. In particular overlap consistency remains work to prove, using germ equality as in item 2. Merely citing the old unqualified “agreement at real points” sentence would repeat the defect.

## 3. Consumers and signature dispositions

The scope is the changed field, its producing theorem and dependent interfaces, rather than a repeat audit of all 202 declarations. Each relevant signature is classified below; unchanged declarations are checked only for the revision's effect.

| Lean signature (S line) | Blueprint role | Verdict | Revision-4 check |
|---|---|---|---|
| `extensionDomain` (538) | `bpP:p5:ext` | PASS | Same tube and carriers; may contain unconstrained real points. |
| `PGExtension.agrees` (556) | `bpP:p5:ext`, corrected | PASS | Equality only on the constrained closed cylinder. |
| Other `PGExtension` fields (543–566) | `bpP:p5:ext` | PASS | No changes; periodicity, holomorphy, bound and continuity retain the same domain. |
| `ext` (568) | `bpP:p5:ext` | PASS | Produced witness now has the justified agreement field; existence route above. |
| `pgExtension` (570) | `bpP:p5:ext` | PASS | Same choice of a produced witness, with no extra hypothesis. |
| `pgWidth`, `pgOscRadius` (572,574) | `bpP:p5:consts` | PASS | Widths and uniform data-only dependence unchanged. |
| `complexAverage` (576) | `bpP:p5:consts` | PASS | Same integral and normalization. |
| `complexAverage_real` (582) | `bpP:p5:consts`, `bpP:p0:secavg` | PASS | Every integrand point is inside the cylinder; detailed check below. |
| `consts` (606) | `bpP:p5:consts` | PASS | Uses extension holomorphy, bound and periodicity, not global source agreement. |
| `jetP0`, `jetOmega`, `jetBeta`, `jetPolynomial` (588–598) | `bpP:p5:birkhoff-ext` | PASS | Constructed from the same analytic average. |
| `pgRemainder` (602) | `bpP:p5:birkhoff-ext` | PASS | Same average minus its jet polynomial. |
| `birkhoff_ext` (616) | `bpP:p5:birkhoff-ext` | PASS | On-V identifications use the retained real average identity; closure determinant follows by continuity. |
| `birkhoff_ext_parameter_regularity` (632) | `bpP:p5:birkhoff-ext` | PASS | Joint continuity and complex symmetry do not require off-cylinder source values. |
| `uniform_remainder` (649) | `bpP:p5:uniform-remainder` | PASS | Analytic jet vanishing and bounds unchanged. |
| `complexFast`, `bilip` (661,664) | `bpP:p5:bilip` | PASS | Depend on unchanged `H0` extension and its identification on W. |
| `complexFrequency_real` (746) | `bpP:p5:freq-inj` | PASS | Fast action explicitly in V; on-V jet and H0 identities suffice. |
| `pg_osc_hyp`, `pg_osc_bound`, `pg_osc_zero` (1029,1034,1039) | `bpP:p5:avg` | PASS | Bounds/zero mode unchanged; reality on the larger real slice follows by reflection, below. |
| `AveragingSpec`, `avg` (979,1062) | `bpP:p5:avg` | PASS | Hamiltonian identity uses the extension itself, with no off-cylinder equality claim. |
| `kam_hyp`, `pg_kam_hyp` (1101,1131) | `bpP:p5:kam-hyp` | PASS | Reality supplied by analytic continuation; no need to identify arbitrary exterior source values. |
| `location` (1120) | `bpP:p5:location` | PASS | Supplies interior physical-cylinder membership for subsequent attachment. |
| `PGFamilySpec`, `torus_conv` (1150,1172) | `bpP:p5:torus-conv` | PASS | Physical image lies in cylinder V r with r<r0; local equality supplies Hamiltonian derivatives. |
| `main` (1251) | `bpP:p5:main` / frozen P-G | PASS for delta | Telescope and conclusion unchanged; amendment creates no new frozen premise. |

For `complexAverage_real`, `I∈V` and `‖(p,q)‖<pgOscRadius≤r0/2` imply, for every j, `p_j²+q_j²<r0²`. The integrand at **every** fast angle therefore belongs to the open cylinder and hence its closure. It is also in `extensionDomain`, with itself as real witness and distance zero. The new premise is available pointwise, so the normalized integral still equals the literal frozen `secularAverage`.

`birkhoff_ext` identifies coefficients only at `I∈V`, using equality on an oscillator neighbourhood of zero. Jet uniqueness needs no exterior action values. Its determinant lower bound on `closure V` is obtained by continuity of the constructed jet and density of V, not by treating arbitrary total `d.beta` boundary values as analytic. Joint regularity and complex symmetry then use parameter continuity and analytic continuation as before.

**Other possible uses of `agrees`.** Searches of the shared signatures and current inp production Lean find no implemented `.agrees` application to repair; the consumer checks above concern the proposed proofs. Two less direct uses matter:

- `OscHyp.real_f` and KAM reality on real neighbourhoods cannot be justified by equality to `d.P` outside the cylinder. Instead, the complex tube is conjugation-invariant and connected: its real skeleton is a product of connected `closure V`, free fast angles and an oscillator box. For fixed mu compare the extension with `z ↦ conj(P mu (conj z))`. Both are holomorphic and agree on a nonempty open real subset inside the cylinder. Real-slice identity implies equality throughout the tube, giving reality at all its real points. The same argument applies to the average and its jets. Thus the weaker agreement field suffices even for an arbitrary chosen `PGExtension`, without adding a reality field or a new hypothesis.
- Physical Hamiltonian attachment in `torus_conv` uses `location`: the image lies in `cylinder V r`, with `r<r0`. This is an open subset of the original constrained cylinder. Near each physical image point the two Hamiltonians agree on a real neighbourhood, so their derivatives, and hence frozen Hamiltonian vector fields, agree there. Pointwise equality alone would not justify this derivative step; interior membership supplies it.

These checks reject the tempting but unnecessary stronger requirement of original-function agreement on a whole exterior real collar. No carrier, norm, period, numerical constant or measure conclusion changes.

## 4. `h0real`: unaffected

`h0real` (S:563–564) still identifies `H0` with the original `d.H0` at every real point in its complex action neighbourhood. Unlike `d.P`, this source function is analytic on the **fixed open set W**: frozen `HasFastDiffeomorphism` begins with `AnalyticOnNhd ℝ H0 W`. Since `closure V` is compact and contained in W, choose a positive real thickening whose closure lies in W. Complexify on a compact thickening, shrink again for derivative bounds, and choose delta below that radius. Every real point quantified by `h0real` then lies in the controlled analytic region, so actual source equality is legitimate. There is no free angle variable in this construction. The angle-dependent shrinking-neighbourhood counterexample therefore has no analogue here. No amendment to `h0real` is needed.

## Findings, source fidelity and limits

**R4-1 — Major, old design defect; resolved.** Revision-3 `PGExtension.agrees` and consequently `ext` were false. The explicit PGData example in section 1 survives the independent checks of all frozen hypotheses. The revised field resolves this defect.

**R4-S1 — Confirmed blueprint/graph defect; reported, not edited.** At the pinned snapshot, `blueprint-P/parts/p5-pg-assembly.tex:30` says “P~ = P at real points” throughout X_delta. `docs/graph/P/packets/P-p5.nodes.md:36` repeats “P~ = P at real points”. Read literally these assert the disproved revision-3 agreement. The periodicity proof at blueprint line 35 also needs agreement of analytic germs on overlaps, not arbitrary original exterior values. Revision 4 explicitly declares the correction. Correct the source/graph contract in a separately authorized source revision to say “at real points belonging to closure(C(V,r0))”; record the germ argument in the proof. This report approves the **declared corrected contract**, and does not claim literal equivalence to the false source wording. This is a project-blueprint defect, not an independently established erratum in CP10 or another pinned paper.

**No new blocking revision-4 finding.** Frozen-object verdict: PASS; actual cylinder, average, Birkhoff and fast-diffeomorphism definitions were read and used. Definition/structure verdict: PASS; only a produced-witness field changes, with no conclusion-shaped source hypothesis or instance. Package verdict for this delta: PASS; same dependencies and split, with no new import or module. The handoff estimates 900–1100 lines split across focused extension modules, below the 1500-line cap per file. Overlap consistency and reality arguments remain proof obligations; successful stub elaboration does not discharge them.

Not audited: prior F1–F8/N1/N2 repairs afresh, actual implementation proofs, all unrelated P4/P5 declarations, frozen provider sealing, root closure, or paper errata beyond the identified blueprint sentence. No state-changing git operation or source change was made.

## Independent validation

- Required command, run **once** on an exact scratch copy:

  ```text
  /mnt/HC_Volume_106379410/orchestrator-tools/inp_sig_check.sh /root/code/KAM-inp-design-p45 .lake/abi-scratch/P45R4AuditSignatures.lean
  ```

  Exit **0**; **69** declaration-uses-sorry warnings; **0** errors; **0** other warnings. Both existing typed upstream applications elaborate. The gate sets `LEAN_NUM_THREADS=1`, invokes `nice -n 5 lake env lean` against the shared inp build, and acquires its shared lock. Log: `/tmp/p45-r4-audit-signatures.log`.
- `#print axioms KAM.Planetary.main`: `[propext, sorryAx, Classical.choice, Quot.sound]`. This is a draft stub receipt, not a proved-result axiom audit. No new Mathlib API is introduced by this one-premise change; existing names are resolved in the fresh elaboration. No separate production build target is changed or required.
- `PATH=/root/code/KAM-inp-design-p45/.lake/abi-scratch/p45-r4-gated-bin:$PATH LEAN_NUM_THREADS=1 scripts/lint_sources.sh`: exit **0**. Output: `check_lean_modules: PASS (519 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`; `ABI HASHES OK (144 frozen declarations)`. Log: `/tmp/p45-r4-audit-lint.log`. The temporary wrapper routed the ABI subprocess through the required gate and restored the ordinary PATH before entering it. An initial recursive-wrapper attempt was stopped without a validation receipt; this corrected, complete rerun supplies the receipt. The signature check and lint ABI check ran sequentially.
- Final integrity: original input SHA256 values rechecked unchanged; no tracked repository diff; only this report added. `git diff --check` exits **0**, report fences balance, no trailing whitespace, terminal newline present. Audit scratch copy and wrapper removed. No heartbeat/recursion/synthesis override, clean/update/cache retrieval, production build, or concurrent Lean invocation was issued by this audit.

Closeout: all five clarified questions answered; **0 unresolved revision-4 design blockers**. Blueprint/graph wording requires the separately recorded source correction R4-S1. No frozen file, manifest, generated root, README, signature source or handoff was edited. No new deviation beyond revision 4's expressly declared source correction was introduced.
