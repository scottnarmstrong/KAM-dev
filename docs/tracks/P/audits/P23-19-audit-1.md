# P23-19 independent package audit 1

Overall verdict: **PASS WITH NOTES** for P23-19's two real-dynamics bridges. No mathematical,
statement-fidelity, hypothesis, or definition defect was found. Notes concern the unchanged unused
`hv` premise, the permitted generated-root lint exception, and the downstream application boundary.
This package has no provider export or frozen theorem anchor to seal; this verdict does not seal P-G
or establish the full two-scale invariant-torus construction.

Audited HEAD: `98b67decddfbdbe4be1c47aede8f21285a07f065`.
Comparison ref `inp`: `cba16d0704fe352828a08b2eff9cb691184b8208`.
`git diff inp...HEAD` contains exactly one added production file:
`KAM/Planetary/TwoScale/RealDynamics.lean` (160 lines).
The pre-existing untracked `P23-19-handoff.md` was read and left untouched.
The report is written in `/root/code/KAM-inp-p2319`, as explicitly required by the user,
overriding the generic brief's main-worktree output instruction.

## Scope and authority

Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, the handoff/AUDIT FOCUS,
revision 2 of `docs/tracks/P/design/P23-LEAN-DESIGN.md`, both design audits in that design
directory, the track-P statement conventions, and blueprint P3b L124–143. Reviewed the frozen
`Phase`, real/complex Hamiltonian fields and symplectic form, and the relevant existing
canonical and real-restriction APIs. Audit scope is exclusively `RealDynamics*`.

The separately named `.drafts/design/P23Signatures.lean` is absent in this worktree.
The verbatim signatures embedded in design Appendix A L1163–1180 supply the comparison target.
Both production signatures equal those signatures after whitespace normalization. Independent
Lean probes also check both directions of full elaborated type compatibility and direct application
with every explicit binder in order. No draft declaration with a `sorry` was imported.

## Declaration-by-declaration results

Public names below are in `KAM.Planetary`; line numbers refer to `RealDynamics.lean`.

| Node / obligation | Declaration | Verdict | Reason / note |
|---|---|---|---|
| `stepP:p3:inv-lim`, design G5 | `real_curve_limit`, L37–47 | PASS WITH NOTES | Exact design signature: differentiable real curves, locally uniform curve and derivative convergence, continuity of the proposed derivative, and `HasDerivAt` at every real time. Direct application of Mathlib's real derivative-limit theorem on `univ`; `hv` is redundant in this proof but retained verbatim. |
| G4, nondegenerate derivative | private `bijective_of_sympl`, L50–59 | PASS | Symplectic preservation implies injectivity by nondegeneracy; finite dimensionality supplies surjectivity. No bijectivity premise is assumed. |
| G4, open image | private `image_mem_nhds_of_sympl`, L63–75 | PASS | Holomorphy on the open source gives a strict derivative; the preceding bijectivity result and the local inverse neighborhood theorem give the image-neighborhood assertion. Requires no global injectivity or inverse as an input. |
| `stepP:p3:inv-conj`, design G4 | `real_symplectic_conjugation`, L79–158 | PASS | Exact design signature and frozen real field. Proves image openness, the real/complex derivative intertwining, and both Hamiltonian-field restriction identities before applying the canonical algebraic conjugation identity. No conjugation premise or extra source hypothesis. |

The two private helpers are fully inventoried above. Their applications occur in the same proof:
`bijective_of_sympl` at L70 and `image_mem_nhds_of_sympl` at L127/L137. They carry no fresh
stage, torus, or limit witnesses.

## Proof and statement review

For conjugation, L94–101 derives `Ψ ∘ ι = ι ∘ Ψr` from the stated reality premise. Openness
of `V` supplies the real neighborhood used at L110–124 to differentiate that equality; this
avoids inferring a derivative equality from equality at one point. The image-neighborhood
helper supplies differentiability of `G` at the image point and openness of `Ψ '' V`.
The two uses of `hamiltonianVectorField_eq_of_real` therefore have the required open domains,
holomorphy, realness, and local agreement. The final chain rule and
`Canonical.map_hamiltonianJ_comp` have the correct sign and direction for frozen phase order
`(angle, action)`. Global injectivity is unnecessary for this pointwise identity, so omitting
the blueprint's stronger diffeomorphism assumption is legitimate.

For the curve limit, `hc` supplies pointwise convergence and `hd` supplies locally uniform
derivative convergence. `hx` gives the differentiability required by
`Mathlib/Analysis/Calculus/UniformLimitsDeriv.lean:502–507`.
That theorem does not need the additional `hv`; retaining it preserves the exact design API.
There are no constants with enlarged dependence, altered norms, changed carriers, or new
conclusion-shaped assumptions in either public theorem. Arbitrary open `V`, including empty
`V`, and dimension zero introduce no exceptional proof branch or fallback.

**Application boundary:** G4/G5 are discharged as the general bridges expressly assigned to
P23-19 by design L232–233 and L283. The remaining construction must supply holomorphy,
symplecticity and reality for the actual finite-stage maps, and locally uniform convergence
of the actual curves and their derivatives to the intended field. In particular the close-pair
field estimate in blueprint L143 is not proved by `real_curve_limit`. There are no production
call sites outside this module at the audited snapshot. Design L303's same-witness applicability
gate remains required for the downstream joint construction; this report does not certify
those absent applications or other P23-17–21 packages.

## Definition classification and import quarantine

There are **no new `def`, `abbrev`, `structure`, or instance declarations**.
The theorem-local `Ψr = Re ∘ Ψ ∘ ι` and `Gr = Re ∘ G ∘ ι` are explicit total restrictions;
their derivative/field assertions are guarded by real-point membership in the open source.
The local `e` at L71 is an actual continuous linear equivalence constructed only after proving
bijectivity. None is a chosen global inverse, default stage, or junk-value construction.

The imported existing `CPhase`, `CHam`, `Phase`, `RealOn`, `symplFormC`, real inclusion and
real projection have the intended product carriers and component formulas. The frozen
Hamiltonian fields are used literally. A recursive local-import traversal visits 41 KAM modules,
including 12 frozen definition modules, and finds **no provider or frozen theorem module**.
Thus there is no DRAFT_SORRY theorem dependency or imported theorem seal state to justify.

## Independent validation

All Lean/Lake checks below ran sequentially with `LEAN_NUM_THREADS=1` and `nice -n 5`.
The targeted build used the prescribed compile gate. No resource override, clean, update,
cache fetch, generated-root edit, or production source edit was used.

### Targeted build

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p2319 KAM.Planetary.TwoScale.RealDynamics
```

Exit **0**. The gate runs `nice -n 5 lake build` internally. Output:

```text
[inp-gate] slot 1 acquired 07:37:41 for KAM.Planetary.TwoScale.RealDynamics
⚠ [9087/9087] Replayed KAM.Planetary.TwoScale.RealDynamics
warning: KAM/Planetary/TwoScale/RealDynamics.lean:41:5: Variable name `hv` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hv

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (9087 jobs).
```

This is Lake's cached replay receipt, not a claim of a fresh proof rebuild. Independent probe
elaboration and kernel replay below are separate checks.

### Signature probes and axioms

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/P2319Audit.lean
```

Exit **0**. The temporary probe imports only the audited module, copies each Appendix A
signature under `P2319Audit.design_<name>`, and proves it with the production theorem:

```lean
-- Bodies of the fresh copies, with the design's explicit binders in order:
exact KAM.Planetary.real_symplectic_conjugation hV hΨ hG hsym hrealΨ hrealG
exact KAM.Planetary.real_curve_limit hx hc hd hv
-- For each name, checks both full elaborated types:
example : type_of% @design_real_curve_limit := @KAM.Planetary.real_curve_limit
example : type_of% @KAM.Planetary.real_curve_limit := @design_real_curve_limit
-- Identical two-direction checks for real_symplectic_conjugation.
```

Exact axiom output (both new public theorems):

```text
'KAM.Planetary.real_symplectic_conjugation' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.real_curve_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Frozen-provider ABI and frozen seal-body probes are **not applicable**: the diff contains
neither a provider nor a frozen theorem implementation. The design-type probes above check
the corresponding exact-type and explicit-application obligations for this infrastructure package.

### Kernel replay and source lint

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.TwoScale.RealDynamics
```

Exit **0**. Exact output:

```text
replaying KAM.Planetary.TwoScale.RealDynamics
```

This single invocation covers the package's only module, including its private helpers.

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

Exit **1**, solely the brief's explicitly permitted stale generated-root exception. Exact output:

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (459 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (144 frozen declarations)
```

The root was not regenerated. Frozen textual and elaborated ABI checks both passed.

Independent scoped static inspection also returned:

```text
forbidden proof escapes: []
option overrides: []
forbidden carrier: []
line cap: 160 <= 1500
100-character check: []
module header: True
```

Maximum Unicode line length is **98**. Copyright, `module`, public imports, module docstring,
and `public section` are present. There are no definitions needing an `@[expose]` annotation.

Final integrity commands:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
git diff --check
git status --short
```

The first three exit **0** with no output. Final status contains only:

```text
?? docs/tracks/P/audits/P23-19-audit-1.md
?? docs/tracks/P/audits/P23-19-handoff.md
```

The report's trailing-whitespace check passed. The audit-owned scratch probe was deleted;
the handoff was already untracked on entry. No state-changing git operation was performed.

## Errata, deviations, and residual uncertainty

No suspected new pinned-source or blueprint defect was found within this scope. The blueprint
uses source order `(action, angle)` and the Lean API uses the documented frozen order
`(angle, action)`; the field and conjugation formulas agree after that explicit coordinate swap.
The historical global-Lipschitz concern P3-08 is already repaired by the close-pair argument in
blueprint P3b L143; this package makes no global Lipschitz assertion.

No mathematical deviation was introduced. No fresh pinned-PDF verification is claimed: this is
the requested design/blueprint-to-proof audit. The absent separate draft file, harmless unused
premise, expected root-generation exception, and outstanding downstream applicability checks
are disclosed above. Only this report is an enduring audit edit; scratch probes are removed.
