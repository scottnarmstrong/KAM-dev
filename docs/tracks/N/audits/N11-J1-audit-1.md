# N11-J1 independent package audit 1

Verdict: **PASS WITH NOTES** for `KAM.Nekhoroshev.preimage`.
This is the complete N11-J1 infrastructure slice, not a seal of N-PARTIAL-CONVEX.

## Scope and fixed inputs

Audit date: 2026-10-28. Audited HEAD `961b2c65da8161c230b8490869c7d0360b83f1cb`;
comparison `inp` at `e262c35780384516b9eb2b21264c361a52841ef9`.
Read AGENTS.md, PLAN.md, DECISIONS.md, the external package-audit brief, the handoff,
N11-LEAN-DESIGN.md, both N11 design audits, the live delivered N11Signatures.lean,
Part-11 blueprint contracts, the track statement, relevant frozen definitions and the
partial-convex anchor. The user's exact worktree report path overrides the brief's generic
main-worktree output instruction.

`git diff inp...HEAD` contains four added modules, 1216 lines: Flow (133), Preimage (327),
Symplectic (400), SymplecticLinear (356). Only
`KAM/Nekhoroshev/Partial/Preimage.lean` is audited, as explicitly required by AUDIT FOCUS;
the inherited N11-E1 additions receive no package verdict here. Preimage SHA-256:
`6843b27eb71cdbb74eac25c60ed8cf5aaa38415aff5c5f2761ee43c1efb3c576`.
The handoff's approximately 250-line estimate understates the actual 327 lines; this is cosmetic.

Delivered signature file SHA-256 at verification:
`fe33b7d1689fdfb8ea66242b975d2b44002039fc4aa25378313afc4bd59a8aeb`.

The only new public declaration is the signed `KAM.Nekhoroshev.preimage` at lines 184–323.
There is no provider export or frozen anchor sealed by this package. Provider/frozen-type and
anchor-seal-body tests therefore do not apply to N11-J1. The exact analogous signed-type and
explicit-binder application probes are run for `preimage` itself. The frozen
`partialConvex_nekhoroshev` remains `by sorry`; this report makes no campaign theorem-closure claim.

## Node and declaration ledger

All names below are in `KAM.Nekhoroshev`; all except `preimage` are private implementation details.
The definition classification is included explicitly for every new definition.

| Node / role | Declaration (Preimage line) | Verdict | Reason / classification |
|---|---|---|---|
| `bpN:p11:preimage` | `preimage` (184) | PASS | Exact signed type; literal blueprint preimage and all three displacement bounds. |
| Internal gauge definition | `preGaugeC` (38) | PASS | Literal invertible complex diagonal scaling by σ⁻¹ and ρ⁻¹; positive parameters exclude zero. |
| Internal gauge definition | `preGaugeR` (42) | PASS | Same real diagonal scaling, on the whole real carrier. |
| Gauge norm | `norm_preGaugeC` (46) | PASS | Product/Pi max norm equals the intended scaled norm. |
| Gauge inverse | `preGaugeC_symm` (50) | PASS | Inverse is multiplication by σ and ρ. |
| Real compatibility | `preGaugeC_extCx` (55) | PASS | Gauges commute with actual complex inclusion. |
| Inclusion coordinates | `extCx_eq_pair` (59) | PASS | Literal two-factor real inclusion. |
| Inclusion additivity | `extCx_sub` (63) | PASS | Difference transported exactly. |
| Inclusion norm | `norm_extCx` (66) | PASS | Inclusion is isometric for the max norm. |
| Internal map definition | `preCxCLM` (71) | PASS | Product of real inclusions, continuous real-linear on every input; no fallback. |
| Inclusion map identification | `preCxCLM_apply` (74) | PASS | Equals `extCx`. |
| Internal map definition | `preReCLM` (77) | PASS | Coordinate real part on every complex input, continuous real-linear; no fallback. |
| Real-part identification | `preReCLM_apply` (80) | PASS | Equals `extRe`. |
| Real-part left inverse | `preReCLM_extCx` (82) | PASS | Actual inclusion followed by real part is identity. |
| Real-part norm | `norm_preReCLM_le` (85) | PASS | Norm contraction, with no dimension loss. |
| Transverse block norm | `norm_snd_sub_le` (90) | PASS | Fast/slow projections exhaust the transverse coordinates. |
| Fast real inclusion | `fastAction_extCx` (106) | PASS | Projection commutes with inclusion. |
| Fast displacement | `norm_fastAction_extCx_sub` (110) | PASS | Exact norm transport. |
| Slow displacement | `norm_slowPair_extCx_sub` (114) | PASS | Exact product norm transport. |
| Base membership | `extCx_snd_mem_base` (123) | PASS | Positive block scales give λ≠0; physical slow point λ·slowPair y witnesses membership. |
| Domain / positive margins | `symm_mem_Dom` (141) | PASS | Open radius-half complex ball stays strictly inside Dom, including endpoint widths. |

There are four new definitions, no new abbrev or structure, and no public helper short name.
All four definitions are literal total linear objects with valid positivity guards, not junk-valued
substitutes. The local definitions `W`, `Wr`, `κ`, `G`, `U`, `ψ`, `L`, `X`, `T`, `x`, and `z`
are the actual gauges, displacement, derivative, ball, fixed-point map and recovered points.
In particular `G(w)=W(Ψ(W⁻¹w)−W⁻¹w)` and `T(u)=Wr(y)−Re(G(extCx u))`.
No local object assumes any fixed-point, preimage, derivative estimate or confinement conclusion.

## Fidelity, completeness and proof review

The live signature file lines 477–486 and implementation lines 184–196 are identical after
removing whitespace. This is only formatting normalization: binder names, explicit/implicit
binders, premise order, quantifiers, constants, carriers and conclusion are unchanged.
The theorem is also exactly the blueprint C lines 27–29 under
`EC n k = ℂⁿ × ℂⁿ⁺²ᵏ`, with the transverse max norm grouping fast actions and slow pairs.
The positive `b.rB` and `b.w` assumptions are the standing block typing data, not added
analytic hypotheses. No condition of canonicality, injectivity, nonempty S, periodicity,
nonnegative displacement bounds, or preimage existence is assumed.

The complete design inventory at N11-LEAN-DESIGN.md:233 maps precisely one node to this
module: `bpN:p11:preimage`. No separate positive-margins graph node or signed export exists.
The work-plan wording at line 360, “preimage, positive margins”, is discharged inside the
proof, not left as an assumed helper:

- `ρ>0`, `ρ≤R` imply `R>0`; `σ>0`, `σ≤2s` imply `s>0` (line 197).
- At the given real y, the displacement bounds force `dθ,dI,dx≥0` (lines 201–208).
  Thus κ≥0, and the complete closed real κ-ball is nonempty, including κ=0.
- `dI/ρ,dx/ρ≤κ≤1/4` give `dI,dx≤ρ/4<R`. Real gauge points within 1/4 of Wr(y)
  have transverse displacement at most ρ/4. Adding an open complex half-ball gives
  transverse distance strictly below `3ρ/4<R` (lines 164–181).
- Angles in that complex half-ball have imaginary parts strictly below `σ/2≤s`
  (lines 153–163). This works at the allowed endpoint `σ=2s`.
- Consequently the recovered `x` is in the original open real domain (lines 290–292,
  315), and its displacement bounds are the exact componentwise bounds from `hb`
  (lines 311–323). `realDom R` uses width 1; real angles lie in that strip automatically.

The gauged displacement is bounded by κ (lines 218–227). `general_cauchy` on the open
complex half-ball yields derivative norm ≤2κ (lines 246–260). Real inclusion has norm one,
real part is norm-decreasing, and the convex mean value inequality gives Lipschitz constant
1/2 on X (lines 269–273). Banach is applied to a self-map of the complete closed ball
(lines 267–283), with a witnessed centre and finite distance. Reality is used on the
recovered point inside Dom to turn the fixed-point identity into the exact complex equation
`Ψ(extCx x)=extCx y` (lines 294–311). No complex-domain conjugation symmetry is needed.

The signed statement supplies the literal max-norm preimage required by transfer T2
(C:47) when the transfer action norm is the max norm. The resonant source consumer's
stronger Euclidean initial bound remains the separate T1/normal-form displacement input
(C:118); this package does not claim that a max-norm bound alone implies that Euclidean
bound. There is no deliberately narrowed signed conclusion needing a repair here.
The proof uses A plus general Cauchy and Banach directly; the work-plan E1 dependency is
unnecessary for this lemma and its absence as an import loses no hypothesis or conclusion.

## Independent check receipts

All Lean-related commands below were serialized, with `LEAN_NUM_THREADS=1` and
`nice -n 5`, at default resource budgets. The build was submitted through the prescribed
gate; waiting for its slot was expected.

1. Targeted build:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-n11j1 KAM.Nekhoroshev.Partial.Preimage
   [inp-gate] slot 1 acquired 21:14:40 for KAM.Nekhoroshev.Partial.Preimage
   ⚠ [3219/3223] Replayed KAM.Nekhoroshev.Stability.Gradient
   warning: KAM/Nekhoroshev/Stability/Gradient.lean:168:5: Variable name `hgr` is not explicitly referenced.
   Build completed successfully (3223 jobs).
   exit 0
   ```

   The omitted warning continuation is Lean's routine unused-binder help. The warning is
   inherited, outside Preimage; no heartbeat or other resource-budget override was used.

2. Independent signed-type, explicit-binder-body, margin and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/N11J1Audit.lean
   'KAM.Nekhoroshev.preimage' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

   The scratch theorem `auditExpectedPreimage` used the exact statement extracted from
   the live delivered signatures, with this body:

   ```lean
   exact preimage b hbR hbw hΨ hr hb hρ hρR hσ hσs hsmall
   ```

   Bidirectional checks were:

   ```lean
   example : type_of% @auditExpectedPreimage := @preimage
   example : type_of% @preimage := @auditExpectedPreimage
   ```

   A separate arithmetic example derived `0<R ∧ 0<s ∧ dI<R ∧ dx<R` from precisely
   `hρ`, `hρR`, `hσ`, `hσs`, `hsmall`. All elaborated without warnings or additional
   premises. `preimage` is the sole new public theorem, so this covers every new public
   theorem's axiom obligation.

3. Kernel replay (one invocation for the sole audited module; its private lemmas are in it):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Nekhoroshev.Partial.Preimage
   replaying KAM.Nekhoroshev.Partial.Preimage
   exit 0
   ```

4. Repository lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (952 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The sole failure is the brief's explicitly permitted generated-root exception.
   There are no forbidden-token, line-width, size, module, frozen-anchor or ABI failures.
   KAM.lean was left untouched. This exception accounts for PASS WITH NOTES.

5. `git diff --check` exited 0 with no output. The protected-path comparison
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` exited 0 with no output.
   Final status contains only this new report and the pre-existing untracked handoff;
   no tracked file was changed by the audit.

Static checks: 327 total lines; maximum Unicode line width 97; no forbidden tokens,
resource overrides or `EuclideanSpace` in Preimage. Module header, public imports,
module docstring and exposed public section are present. Only the namespace-qualified
`preimage` is public; its signed name introduces no harmful root shadow.

Recursive local import inspection found 69 KAM modules, including 21 frozen modules;
all 21 are definition anchors with manifest state SEALED. No provider or frozen theorem
module, including any DRAFT_SORRY anchor, is in the production import closure.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty.

## Notes, errata and limitations

1. The known blueprint clarification is retained: C:31 says “the complex ν-ball of radius
   1/2”. At σ=2s this must mean the **open** ball. A closed ball can reach the strip
   boundary. `symm_mem_Dom` and `general_cauchy` explicitly use `ball`, so the implementation
   establishes the valid reading without narrowing the signed endpoint inequality.
   Both earlier design audits already record this; no new mathematical erratum is alleged.
2. The previously reported adjoint proof locator B:69–86 overreaches the proof ending at
   B:73. It belongs to another package and is retained as an upstream graph note, with
   no source/graph edit or verdict on that package.
3. The handoff's “no errata/deviations” omits those carried design notes. No new pinned-source
   defect or implementation deviation was found. This is a blueprint/package proof audit,
   not an independent re-audit of the Nek77 PDF or the eventual frozen provider.

Only this report is a persistent audit edit. Scratch probes are confined to
`.lake/abi-scratch/` and removed after checking. No state-changing git operation,
production-source change, frozen/manifest change or generated-root repair was performed.
