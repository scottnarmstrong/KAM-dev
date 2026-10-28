# Independent S9 package audit 1

Audit date: 2026-10-28. Scope: only `KAM/Planetary/SecularBox/GlobalFlow.lean`.

## Verdict and scope

**PASS WITH NOTES** for the S9 infrastructure slice: `KAM.Planetary.angle_quadrature` and
`KAM.Planetary.sb_global`. No mathematical, signed-interface, or assigned-node coverage defect found.
The note is the explicitly allowed stale generated root, subject to the exact checks below.

No frozen anchor is seal-ready on this package alone. The manifest entries
`planetary.d25.secularBoxSafety.v1` and `planetary.d25.secularBoxAtCitedMasses.v1` remain
`DRAFT_SORRY` / **FROZEN_UNPROVED**. S9 supplies the global-flow ingredient, not uniqueness,
all-phase safety geometry, the final provider, or either complete frozen conclusion. There is no S9
provider export to compare directly with a frozen theorem; the analogous exact-type and explicit-binder
checks are performed against the two signed library declarations.

HEAD: `4597d414463d894bb2aedc277e69344ae9ace2c5`. Initial `inp`:
`eedc66febf1e2749337a502351ab1515c1779c15`; merge base:
`676267256853edb2ecde14b4a15d5f571fa29198`. `inp` advanced during the audit to
`b5e58ec5e766134ead4e306f3ed3c4dc0da81acd`; both three-dot diffs were byte-identical:
32,616 bytes, SHA-256 `40bb6dc95a5eb33c431bdd900353fc8efb3201cd9f0cbf9ca095ed4347809232`.
The full `git diff inp...HEAD` was inspected: Field (244), SlowFlow (204), GlobalFlow (171)
are the three additions. Field and SlowFlow are inherited S7/S8 inputs, outside this report's verdict.
The existing untracked `S9-handoff.md` was preserved.

Read AGENTS.md, PLAN.md, DECISIONS.md, the controlling package-audit brief, S9 handoff and its
AUDIT FOCUS, the P14 design and both design audits, the track P secular-box statement, relevant
frozen theorem/definition files, blueprint `p14b-secular-box.tex`, and the corresponding graph records.
Applied the lean-statement-audit skill's statement, binder, definition, and consumption checks.
No agents were delegated. The user's exact report destination overrides the brief's generic main-worktree
output sentence. Only this report is a persistent auditor edit; temporary probes use `.lake/abi-scratch/`.

Pinned inputs:

- GlobalFlow SHA-256: `6da303677648a5df2ba08f1c3ba737720387698459927322537f8d8bda54c913`.
- Original signatures: `/root/code/KAM-inp/.drafts/design/P14Signatures.lean`, SHA-256
  `24916d5937451954a71ba5349789bcbda5b06b70f40fe3a6ba24eec9bd533f88`.
- Design SHA-256: `04c358878699851e0e45adcccbfd06048e2474b6cffe015821df5e072f36fca3`.
- Blueprint b SHA-256: `f14536c948f27bc9ccb330b5df0b482846696aa7ea10283d42ee2569be2d0ae7`.

## Declaration and node ledger

Names below are in `KAM.Planetary`; private names denote source declarations, not public exports.
Design lines 253–256 assign exactly the parent and three internal steps to GlobalFlow; row S9 at
line 395 also assigns the FTC wrapper. The graph packet has the same literal step conclusions.

| Node / role | Declaration or proof location | Verdict | Reason |
|---|---|---|---|
| `sb-x-int` supplier / `sb-gl-1` | `angle_quadrature`, 29–33 | PASS | Exact signature lines 98–100; continuous Fin 2-valued integrand, two-sided derivative at every real t, including zero and negative t. No time or period rescaling. |
| `bpP:p14:sb-global` | `sb_global`, 94–167 | PASS | Exact signature lines 504–510; one curve simultaneously supplies initial equality, the literal frozen Hamiltonian predicate, S membership, and constant fast actions/AMD for all real time. |
| `stepP:p14:sb-gl-1` | `sb_global`, 102–120 | PASS | Derives continuity of y from its derivative, continuity of the slice, and continuity of omega on S. Constructs lambda by the actual integral and proves its derivative. |
| `stepP:p14:sb-gl-2` | `sb_global`, 122–135, 164–167 | PASS | Assembles the full curve, proves initial equality, membership and fast-action identity; transfers the conserved AMD from S8. |
| `stepP:p14:sb-gl-3` | `sb_global`, 136–163 | PASS | Proves differentiability of H at the reconstructed curve and every fast/slow coordinate derivative, using zero fast-action field, the reduced field components, and angle-independence of omega. |
| Reconstruction identity | private `sbGlobal_eta`, 35–39 | PASS | Exact Fin block eta identity for arbitrary block sizes. |
| S transfer | private `sbGlobal_mem_congr`, 42–46 | PASS | S depends only on fast actions and both slow coordinate blocks; direct unfolding. |
| AMD transfer | private `sbGlobal_amd_congr`, 48–51 | PASS | Direct unfolding of the sum of oscillator actions. |
| Fast translation | private `sbGlobalShift`, 54 | PASS | Literal vector `(append c 0, 0)` on the whole carrier. |
| Translation identity | private `sbGlobal_add_shift`, 56–62 | PASS | Componentwise equality for arbitrary phase point and translation. |
| Assembly translation | private `sbGlobal_assemble_shift`, 64–70 | PASS | Splits angle lambda into zero-angle slice plus literal translation. |
| Fast-angle independence | private `sbGlobal_omega_lam`, 73–84 | PASS | Differentiates an actual global translation identity for H via `fderiv_comp_add_right`; no independence premise assumed. |
| Frequency continuity | private `sbGlobal_omega_cont`, 86–92 | PASS | C-infinity H on open S implies continuous derivative; evaluation at each fast-action basis vector gives continuous omega. |

Every assigned node is established inside the proof or by the signed export. There is no unsigned
public graph-named export with a narrowed conclusion. Private duplication of newer S7 continuity and
angle-independence exports is explicitly permitted by the AUDIT FOCUS and is not a finding.

## Exact statements and expanded binders

A Python comparison of each declaration header against the original signatures, removing whitespace
only, returned `IDENTICAL` for both. Binder names, order, implicitness, rational constants, carriers,
and the complete conclusion match; no extra positivity or smallness assumption on mu appears.
The same headers in design Appendix A agree. These are ordinary library helpers, not frozen anchors.

The following table expands project-owned assumption aliases. SOURCE means the blueprint premise;
TYPING means carrier/parameter data. There are no instance binders, EXCESS premises, or concealed
proof obligations. Source references are `blueprint-P/parts/p14b-secular-box.tex` (b).

| Theorem | Binder / expanded logical input | Bin | Evidence |
|---|---|---|---|
| `angle_quadrature` | implicit `omega : ℝ → (Fin 2 → ℝ)` | TYPING | Signed FTC wrapper; b38, b263. |
| same | `h : Continuous omega` | SOURCE | Design F5, lines 41–43 and Appendix A; b263's continuous omega-star. |
| same | `t : ℝ` | TYPING | Two-sided FTC at every real time. |
| `sb_global` | `saturn : ℝ` | TYPING | Fixed mass-ratio data of b, signature 504. |
| same | `mu : ℝ` | TYPING | Fixed Hamiltonian parameter, signature 504. |
| same | `hs`: `29/100 ≤ saturn` | SOURCE | Fixed mass range; b standing data. |
| same | `hs`: `saturn ≤ 31/100` | SOURCE | Same. |
| same | implicit `w0 : Phase (2+2)` | TYPING | b259, as in slow lemma b247. |
| same | `hw`: for every i, `0 < fast w0.2 i` | SOURCE | S membership b259/b247; literal `sb_sdef` Region.lean:31–36. |
| same | `hw`: for every i, `50 * secularGamma w0 i < fast w0.2 i` | SOURCE | Same S premise. |
| same | `hw`: `51/10 < secularAxis ... w0 0` | SOURCE | Same S premise. |
| same | `hw`: `secularAxis ... w0 0 < 53/10` | SOURCE | Same S premise. |
| same | `hw`: `47/5 < secularAxis ... w0 1` | SOURCE | Same S premise. |
| same | `hw`: `secularAxis ... w0 1 < 97/10` | SOURCE | Same S premise. |
| same | `hA`: `secularAMD w0 < 16373/2500000` | SOURCE | b247, inherited literally by b259. |
| same | `hI`: for every i, `87/100 < fast w0.2 i` | SOURCE | b247, inherited literally by b259. |

Expanded counts: angle_quadrature SOURCE=1, TYPING=2; sb_global SOURCE=10, TYPING=3;
STANDING=RULED=EXCESS=0 in both. Before conjunction expansion sb_global has four premise binders
`hs, hw, hA, hI`. Scalar expressions use the literal frozen bodies: Phase is a product of Pi spaces,
fast/slow select the two Fin blocks, assemble is `(append phi q, append I p)`, Gamma is
`(p_i²+q_i²)/2`, AMD their sum, axes are `(Lambda_i/m_i)²`, weights are `![1,saturn]`.

The frozen `IsHamiltonianSolutionOn H univ univ w` expands to all-real-time action membership in
univ, `DifferentiableAt ℝ H (w t)`, and `HasDerivAt w (hamiltonianVectorField H (w t)) t`.
Both substantive clauses are proved at GlobalFlow:136–163, not replaced by a predicate alias or
assumed field equation. H is exactly the frozen normalized double secular average, not a selected
model Hamiltonian. Its `(2*pi)^(-2)` normalization is inherited unchanged.

## Definitions, proof route and consumers

The only new def/abbrev/structure is the private literal `sbGlobalShift`. Its body matches fast-angle
translation at every point, with no fallback or choice. BODY_MATCH=OK; PUBLIC_CARRIER=OK
(private auxiliary); WELL_DEFINEDNESS=N/A_LITERAL; CHARACTERIZATION=N/A_LITERAL;
CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS. Local `I`, `H`, `lam`, and `w` are exact
abbreviations/constructions; lambda is a genuine interval integral, and the complete witness properties
are proved. No choice of a source-defined unique object or unproved result bundle is introduced.

The central logical supplier is the actual theorem `sb_slow saturn mu hs hw hA hI` (line 102).
Its derivative supplies continuity, domain membership and the reduced dynamics, rather than adding
those as premises. Smoothness and openness produce omega continuity and differentiability of H;
translation invariance produces omega independence even at arbitrary fast angles. The four coordinate
cases have the canonical signs and order `(lambda,xi;Lambda,eta)`: omega, reduced position field,
zero, reduced momentum field. The interval FTC is valid on both time directions. No compactness of
unrestricted lifted angles is asserted or needed.

The signed interface is not narrower than the parent blueprint conclusion. The S10 uniqueness
signature consumes precisely the global solution predicate and all-time S membership. Design's
assembly row at line 440 consumes the same witness, initial equality, conserved actions and AMD;
regularity comes separately from S7 smoothness. Thus S9 pays its consumer obligations without
claiming the rest of S10/S11/S12. This audits S9's use of the existing S7/S8 interfaces and its
transitive axiom closure, not a fresh independent verdict on their internal proof slices.

The project import closure contains 73 KAM modules, no provider imports, and 53 frozen modules,
all manifest-state SEALED. No DRAFT_SORRY anchor is imported, directly or transitively.

## Independent validation

All audit Lean/Lake invocations were serialized. The compile gate runs `nice -n 5 lake build`; direct probes and kernel replay use `nice -n 5`, with `LEAN_NUM_THREADS=1`. An initial partial lint run was stopped before its Lean ABI phase and rerun with these explicit settings after kernel replay. No Lean/Lake overlap was introduced.


1. Targeted build (exit **0**):

   ```text
   env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p14-s9 KAM.Planetary.SecularBox.GlobalFlow
   [inp-gate] slot 2 acquired 21:01:47 for KAM.Planetary.SecularBox.GlobalFlow
   Build completed successfully (9119 jobs).
   ```

   This used the existing overlay and targeted module; no clean or library rebuild was requested.
   No warning or heartbeat failure was emitted.

2. Signed header comparison: whitespace-normalized exact text **IDENTICAL** for both exports.
   Probe (exit **0**):

   ```text
   env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/S9Audit1.lean
   'KAM.Planetary.angle_quadrature' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.sb_global' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   The probe imports only GlobalFlow, opens Set/KAM.Kepler/KAM.Planetary and scoped ContDiff,
   and copies the two exact signature headers into namespace S9Audit. Fresh theorem bodies are:

   ```lean
   by exact KAM.Planetary.angle_quadrature h t
   by exact KAM.Planetary.sb_global saturn mu hs hw hA hI
   ```

   Thus every explicit binder is passed in exact source order; implicit omega/w0 are inferred.
   For each name N the probe also checks both directions:

   ```lean
   example : type_of% @KAM.Planetary.N := @S9Audit.N
   example : type_of% @S9Audit.N := @KAM.Planetary.N
   ```

   These are instantiated at both actual names, not merely textual checks of pretty-printed types.
   All new public theorems are accounted for; private helpers are covered by export axiom closure
   and module kernel replay. No `sorryAx` or project-specific axiom occurs.

3. Kernel replay, one invocation (exit **0**):

   ```text
   env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.SecularBox.GlobalFlow
   replaying KAM.Planetary.SecularBox.GlobalFlow
   ```

4. Static hygiene: target 171 physical lines, maximum line width 98 characters. No forbidden
   sorry/admit/axiom/unsafe/opaque/EuclideanSpace token or resource-setting command; module header,
   copyright, public imports, module docstring and public section present. No additional declaration
   of either public short name anywhere else in KAM, and neither export lives in the root namespace.
   `sbGlobalShift` is private and under the expose section. No protected import or source edit.

5. Protected-path and whitespace checks (exit **0**, empty output):

   ```text
   git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
   git diff --check inp...HEAD
   git diff --check
   ```


6. Full source lint (exit **1**, solely the permitted stale-root exception):

   ```text
   env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (951 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No other output or substantive lint failure. The generated root was not regenerated.
   The ABI subprocess inherited `LEAN_NUM_THREADS=1` and niceness 5 and ran after kernel replay.

## Notes, errata and closeout

- The stale generated root is the brief's explicit exception. All source, frozen-anchor and ABI
  checks otherwise pass; this does not authorize editing the root in an audit.
- Design audit 1's F5 API correction is implemented literally using
  `intervalIntegral.integral_hasDerivAt_right`; design revision 2's two-sided FTC contract is paid.
  The older design node-table supplier spelling at line 194 still reads
  `intervalIntegral.integral_hasDerivAt`; the executable correction at lines 37–43 and the S9
  implementation use the correct `_right` name. This is inherited documentation residue, not a
  mathematical gap or an implementation defect. The blueprint's actual FTC sentence at b38 is valid.
- No suspected pinned-paper mathematical erratum or introduced mathematical deviation was found.
  This is a bounded implementation/source-contract audit, not a new audit of every cited paper.
- S7/S8 remain separately audited packages; this verdict does not certify their entire graph slices,
  any later S10/S11/S12 proof, or either frozen headline. No missing S9 graph cut was found.
- The final observed live `inp` was `e262c35780384516b9eb2b21264c361a52841ef9`. Its three-dot
  diff remained the same 32,616 bytes and SHA-256 recorded above. HEAD, target bytes and controlling
  signature bytes were unchanged at recheck.
- The auditor's `S9Audit1.lean` probe was removed. No production, frozen, manifest, generated file,
  or git state mutation was performed. Final persistent auditor output is exactly
  `/root/code/KAM-inp-p14-s9/docs/tracks/P/audits/S9-audit-1.md`.

Final disposition: **PASS WITH NOTES** for S9; both signed exports and all assigned internal steps
are accepted within this scope. Frozen headline proof status remains **FROZEN_UNPROVED**.
