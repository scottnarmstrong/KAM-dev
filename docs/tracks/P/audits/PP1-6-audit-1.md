# PP1-6 independent package audit 1

**Overall: PASS WITH NOTES.** All 14 public declarations in
`KAM/Planetary/Hamiltonian/Transport.lean` pass statement and definition fidelity.
The 11 public theorem proofs pass inspection. Notes concern only the expected generated-root
lint failure, an unused binder, and the comparison-base ambiguity documented below.
There is no frozen theorem anchor in PP1-6, so “seal-ready” means ready to integrate this helper
package; this report does not seal P-G, P-PLANAR, P-FIXED, or any I/N/P headline.

## Scope and frozen inputs

Date: 2026-10-28. Worktree: `/root/code/KAM-inp-pp16`.
Audited HEAD: `850e2c3cb660a2c2ec21e616702d0e455e21943d`.
Observed `inp`: `00cf49c93cbcea2fd371edf0865258fadd64a43d`.
The requested `git diff inp...HEAD` warns:

```text
warning: inp...HEAD: multiple merge bases, using d030f8799fbc9a4c5e23582162b9bd844fa49574
 KAM/Planetary/Hamiltonian/Chart.lean     | 248 ++++++++++++++++++++
 KAM/Planetary/Hamiltonian/Transport.lean | 373 +++++++++++++++++++++++++++++++
 2 files changed, 621 insertions(+)
```

Only Transport is audited, as required by the handoff's AUDIT FOCUS. Chart is inspected at
its consumed interfaces, not given a new package verdict. The initial working tree also has
an untracked `docs/tracks/P/audits/PP1-6-handoff.md`; it is evidence, not an implementation edit.
The explicit user destination overrides the generic brief's instruction to write in the main
inp worktree. No source, frozen file, manifest, generated file, or git state is edited.
Only this report is delivered; temporary Lean probes are confined to `.lake/abi-scratch/`.
No delegation, network lookup, or upstream source modification was needed. The verdict uses the current files and rerun checks.

Frozen-v1 SHA-256 values:

| Input | SHA-256 |
|---|---|
| Transport.lean | `1fe2cee53837cb969582fee25e17d4dba9157b28855255e15414e275dcc842f3` |
| blueprint-P/parts/p1-hamiltonian-tools.tex | `71125916b1c5316e440916dd15e22d267a891c2d2b97188a7afb46ba2ff6af33` |
| docs/tracks/P/design/PART1-LEAN-DESIGN.md | `f88dab2f934cdbb1f2d398da3c8a3413f6ebdfe502a9c763cfa14b74c4fa8be4` |
| docs/tracks/P/design/DESIGN-P1-design-audit-1.md | `4f722da6ba8a6805a63b403f1df4a6a86c3bf29511821b47778479ab7d8a31e6` |
| docs/tracks/P/design/KEPLER-LEAN-DESIGN.md | `b23265f9c90c8fdf3bebd66fb7eac1cf965e3b1b22080d85ff9c2becf2fe4a15` |
| /root/code/KAM-inp/.drafts/design/PPart1Signatures.lean | `78f21690c9e2623e9d9a9b6087bf32d1477434618c3089d98d0d0b99d5d098f7` |

Read AGENTS.md, PLAN.md, DECISIONS.md, the package audit brief, handoff, Part-1 design and
its audit, Kepler design dependency item 8 and P7-6 row, the relevant blueprint statements,
track-P statement conventions, and the frozen definitions actually consumed. No theorem anchor
is imported or proved here; provider=frozen-type and proposed seal-body tests are inapplicable.
This is a tier-2 correspondence/proof audit with a separate adversarial second pass. Acceptance
requires exact design surfaces, all source clauses, no excess premises, faithful definitions,
serial build/probe/replay, permitted axioms, and hygiene with only the brief's root-file exception.

## Declaration ledger

Names are in `KAM.Planetary`. Line numbers refer to frozen-v1 Transport. The blueprint source
is `blueprint-P/parts/p1-hamiltonian-tools.tex` at this HEAD. A mechanical whitespace-normalized
comparison of every public declaration header with signature section D found **14/14 exact
matches**; the three definition bodies also match. The type probes copy all 11 design theorem
headers and apply the corresponding implementation with every implicit and explicit argument
in order. This checks applicability, including binder order, without importing draft signatures.

| Node | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| p1:lattice-torus | `IsLatticeTorus` (44) | PASS | All L1–L6, blueprint 81–90; explicit lattice parameter specializes to angleShift. |
| p1:torus-transport | `fderiv_chart_comp_torus` (55) | PASS WITH NOTES | Exact chain rule, blueprint 105; unused hc retained from design. |
| p1:torus-transport(a) | `torus_transport_cyl` (86) | PASS | Exact frozen cylinder predicate, full fastShift quotient injectivity, unchanged w. |
| p1:torus-transport(b) | `torus_transport_phys` (113) | PASS | Exact frozen physical predicate; positive gamma and strict tau threshold supplied. |
| p1:period-convert(c) | `periodOne` (132) | PASS | Literal parameter scaling by 2*pi. |
| p1:period-convert(c), phys-pipeline | `IsTwoPiLatticeTorus` (136) | PASS | All six radian-convention clauses; no hidden Diophantine or output predicate. |
| p1:period-convert(c) | `analyticOnNhd_periodOne_iff` (174) | PASS | Both directions on the entire parameter carrier. |
| p1:period-convert(c) | `fderiv_periodOne` (188) | PASS | Unconditional equality; both nondifferentiable sides are zero. |
| p1:period-convert(c) | `periodOne_lattice_iff` (212) | PASS | Arbitrary target lattice T; both directions. |
| p1:period-convert(c) | `periodOne_injMod_iff` (224) | PASS | Exact integer/radian parameter-lattice equivalence. |
| p1:period-convert(c) | `periodOne_hasDerivAt_iff` (239) | PASS | Identical curves, derivative v, and time t. |
| p1:period-convert(c) | `isLatticeTorus_periodOne_iff` (252) | PASS | All six clauses transported, including immersion and Lagrangianity. |
| p1:cyl-pipeline | `cyl_pipeline` (316) | PASS | One angleScale, exact inverse-factor Hamiltonian, same frequency w. |
| p1:phys-pipeline | `phys_pipeline` (346) | PASS | Frequency omega/(2*pi), positive gamma/(2*pi), and complete range equality. |

## Definitions and premises

All three new definitions are **literal**, with no choice, junk branch, fallback value,
non-unique witness, or deferred characterization:

| Definition | BODY_MATCH | PUBLIC_CARRIER | WELL_DEFINEDNESS | CHARACTERIZATION | CHOICE_INDEPENDENCE | DEFINITION_VERDICT |
|---|---|---|---|---|---|---|
| IsLatticeTorus | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| periodOne | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |
| IsTwoPiLatticeTorus | OK | OK | N/A_LITERAL | N/A_LITERAL | N/A | PASS |

The Prop definitions describe the actual source input tori, not an assumed transport result.
`IsLatticeTorus angleShift` is exactly blueprint LT. General L is the explicit design
generalization; no additive law for L is needed. Dropping IsOpen O strengthens the theorem:
AnalyticOnNhd supplies analyticity on a neighborhood at each point used, and the consumed
chart differentiability equivalence works pointwise. The explicit positivity assumption hc
is source data even where the derivative formula itself does not need it.

The binder census below lists every outer binder; no instance binder is added. SOURCE means
an explicit source premise, TYPING a source object/carrier or universally quantified datum.
STANDING=0, RULED=0, EXCESS=0. Source locations use the blueprint lines cited above.
The SOURCE packages expand as follows (each clause is independently a SOURCE premise):

| Package | Expanded clause | Source |
|---|---|---|
| hPsi / hPhi | AnalyticOnNhd of the chart | chart definition; transport 95; pipelines 143,150 |
| hPsi / hPhi | conformal symplectic derivative on the chart domain | same |
| hK / hκ | parameter analyticity | L1 at 84; radian version 150 |
| hK / hκ | range in O | L1 at 84; radian version 150 |
| hK / hκ | Hamiltonian differentiability on the range | L1 at 84; radian version 150 |
| hK / hκ | lattice equivariance | L2 at 85; radian version 150 |
| hK / hκ | injectivity modulo parameter lattice | L3 at 86; radian version 150 |
| hK / hκ | injectivity of derivative | L4 at 87; radian version 150 |
| hK / hκ | zero symplectic pullback | L5 at 88; radian version 150 |
| hK / hκ | HasDerivAt along every linear orbit, same time | L6 at 89; radian version 150 |
| hQ1 | shifted point remains in O | Q1 at 97; pipelines 143,150 |
| hQ1 | chart shift/periodicity identity | Q1 at 97; pipelines 143,150 |
| hQ2 | chart injectivity modulo lattice | Q2 at 98; pipelines 143,150 |
| hU | entire transported range contained in U | 102; cylinder pipeline 143 |
| hgamma | positive Diophantine constant | 103; physical pipeline 150 |
| htau | strict dimension/exponent threshold | 103; physical pipeline 150 |
| hw / homega | frozen IsDiophantine inequality for all nonzero integer vectors | 103,150; frozen IsDiophantine body |

IsChart's symplectic clause uses the delivered IsSymplecticOn, precisely the quantified
bilinear identity, not an invertibility premise. The latter is proved upstream. Neither
frozen output torus predicate occurs as an assumed premise. All existential parameter-lattice
witnesses occur inside the source injectivity clauses; no output witness is preselected.

## Proof and adversarial checks

Inspected every proof line, including private helpers. `transport_core` derives analyticity,
Hamiltonian differentiability, derivative injectivity, Lagrangianity and flow from the input
clauses and Chart. The cylinder proof extends an arbitrary fast k by `Fin.append k 0` before
Q2, so it proves the frozen quotient-injectivity clause for **every** fast lattice shift.
In both transport proofs Q2 gives m, L2 identifies K(theta+m), and L3 gives the extra integer
l, hence theta'=theta+(m+l). This does not assume L(m+l)=L(m)+L(l).

A separate refutation pass tested the likely failure modes: arbitrary L without a group law;
orientation of the physical Q2 equality; zero fast/slow dimensions; differentiability failure
in the unconditional derivative identity; immersion and Lagrangianity in both directions of
the period equivalence; domain restrictions in chart composition; and a double frequency/time
rescaling. None survives inspection. Nonzero 2*pi supplies inverse scaling; the proof explicitly
shows nondifferentiability transfers through that invertible scaling before using total fderiv=0.
The Lagrangian factor is (2*pi)^2. `periodOne_flow` is equality of curves, so time is unchanged.
`cyl_pipeline` composes chart factors 2*pi and 1 and retains w; `phys_pipeline` only scales the
parameter and uses Diophantine conversion at gamma/(2*pi). Positivity is explicit, avoiding
the zero-gamma counterexample recorded in the earlier blueprint review. There are no accepted
mathematical defects or unrefuted tentative blockers.

## P7-6 consumption and dependencies

Kepler design row P7-6 (446) and dependency item 8 (624–625) require Part 1's angleScale and
fullShift. Their owners are Chart, imported publicly by Transport, with the exact bodies
`(c • z.1,z.2)` and `(fun i => 2*pi*(k i : ℝ),0)`. Both specialize unchanged to Phase(n+n).
The probe checks those defining equations by rfl and applies angleScale_add_angleShift at
that dimension. P7-6 should import Chart directly and omit its draft duplicate definitions,
as already required by the Part-1 design. Transport has no dependency on Poincare/Lattice,
so no cycle is introduced. A homogeneous P7 chart with Q1/Q2 feeds torus_transport_phys
or phys_pipeline directly; the exact-signature probes check every required premise.
The P7-6 implementation is absent in this snapshot, so this establishes the designed
interface's applicability, not completion of P7-6 or a proof of its polar lattice facts.

The project-import closure has 13 modules, no provider and no DRAFT_SORRY anchor.
All frozen imports are definitions. The explicit Diophantine import at Transport:19
resolves design-audit N1; phys_pipeline consumes isDiophantine_smul_iff at line 361.
Other project dependencies are Kepler.Basic, ODE.Basic, Chart and Algebra; their proof
bodies are not independently reaudited as packages here. Public axiom closure is checked below.

## Verification evidence

All Lean/Lake commands ran serially with LEAN_NUM_THREADS=1 and niceness 5. No heartbeat,
recursion-depth, or synthesis-budget override, package update, cache fetch, cleanup or broad
rebuild was used.

1. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-pp16 KAM.Planetary.Hamiltonian.Transport`
   exited 0. Output: `[inp-gate] slot 1 acquired 06:29:32 for KAM.Planetary.Hamiltonian.Transport`
   and `Build completed successfully (9059 jobs).` This was cached/replayed; it is not a fresh-source
   proof-elaboration timing. The target warning is `Transport.lean:55:41: Variable name hc is not
   explicitly referenced.` The same already-recorded kind of warning was replayed in Algebra,
   Chart and Diophantine, outside this audit scope.
2. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.Hamiltonian.Transport`
   exited **0**. Complete substantive output: `replaying KAM.Planetary.Hamiltonian.Transport`.
3. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/PP1-6-probe.lean`
   exited **0**. All 11 design-header copies elaborated with explicit implementation applications;
   the three P7-dimension defining-equation/lattice probes also passed. Every public theorem's
   `#print axioms` output was exactly `[propext, Classical.choice, Quot.sound]`:

   ```text
   fderiv_chart_comp_torus
   torus_transport_cyl
   torus_transport_phys
   analyticOnNhd_periodOne_iff
   fderiv_periodOne
   periodOne_lattice_iff
   periodOne_injMod_iff
   periodOne_hasDerivAt_iff
   isLatticeTorus_periodOne_iff
   cyl_pipeline
   phys_pipeline
   ```

   Each name above is prefixed by `KAM.Planetary` in the actual output. There is no sorryAx,
   project axiom, or other trust extension.
4. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean KAM/Planetary/Hamiltonian/Transport.lean`
   exited **0**, freshly elaborating the current source at default heartbeats. Its sole warning
   was the unused hc at 55:41. No resource failure occurred.
5. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh` exited **1**, solely for
   the explicitly permitted generated-root exception. Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (419 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No over-100-character warning or other forbidden-pattern/module/manifest/ABI issue occurred.
   The lint script runs its ABI Lean subprocess serially after all other Lean commands finish.
6. Removed `.lake/abi-scratch/PP1-6-probe.lean` after successful elaboration. Probe SHA-256
   before deletion: `5ae8f1cac1816de070c29ebba328218af5edb1e05dcb79627eac785bf3039977`.
   The target source SHA-256 was unchanged at final verification. Repository sources were
   never edited; the two local check logs remain under `.lake/abi-scratch/` only.

Mechanical source scan: 373 physical lines, zero lines over 100 Unicode characters, no forbidden
proof escapes or overrides, required copyright/module/public imports/docstring/exposed public
section present. All 14 signature headers and all 3 definition bodies match design section D.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` is empty (apart from the same
multiple-merge-base warning). `git diff --check` exited 0.

## Notes, errata, and closeout

- N1 (nonblocking): root-import regeneration belongs to the orchestrator; apply only the brief's
  explicit “KAM.lean is out of date” lint exception. No generated file was changed here.
- N2 (cosmetic): `fderiv_chart_comp_torus` retains unused hc from the exact design signature.
  No signature change is needed for this package.
- N3 (provenance): the requested comparison includes Chart and has multiple merge bases.
  This report pins the actual selected base and target hash; it makes no claim about auditing
  that prerequisite's complete diff.

Suspected blueprint/pinned-source errata: **none found in the audited slice**. The blueprint
calls this transport result “Ours as a statement for the frozen predicates; no source page”
(lines 107), so no uninspected external theorem is being certified as a verbatim source result.
The prior positivity issue is already repaired in the current blueprint and implementation.
Deviations introduced by this audit: none. No proof or source repair was performed.

Closeout: all 14 public declarations classified; all three literal definitions faithful;
all 11 theorem signatures checked against the independent design, proofs inspected, and
kernel replay successful. Final hygiene status and axiom output are recorded in the evidence
above. No frozen anchor is promoted by this helper-package verdict.

## Binder annex

| Declaration | Binder | Bin | Blueprint locator |
|---|---|---|---|
| `fderiv_chart_comp_torus` | `d` | TYPING | 132 |
| `fderiv_chart_comp_torus` | `c` | TYPING | 132 |
| `fderiv_chart_comp_torus` | `hc` | SOURCE | 132 |
| `fderiv_chart_comp_torus` | `O` | TYPING | 132 |
| `fderiv_chart_comp_torus` | `Ψ` | TYPING | 132 |
| `fderiv_chart_comp_torus` | `hΨ` | SOURCE | 132 |
| `fderiv_chart_comp_torus` | `K` | TYPING | 132 |
| `fderiv_chart_comp_torus` | `hKan` | SOURCE | 132 |
| `fderiv_chart_comp_torus` | `hKO` | SOURCE | 132 |
| `fderiv_chart_comp_torus` | `θ` | TYPING | 132 |
| `torus_transport_cyl` | `a` | TYPING | 95–105 |
| `torus_transport_cyl` | `b` | TYPING | 95–105 |
| `torus_transport_cyl` | `c` | TYPING | 95–105 |
| `torus_transport_cyl` | `hc` | SOURCE | 95–105 |
| `torus_transport_cyl` | `O` | TYPING | 95–105 |
| `torus_transport_cyl` | `Ψ` | TYPING | 95–105 |
| `torus_transport_cyl` | `hΨ` | SOURCE | 95–105 |
| `torus_transport_cyl` | `H` | TYPING | 95–105 |
| `torus_transport_cyl` | `w` | TYPING | 95–105 |
| `torus_transport_cyl` | `K` | TYPING | 95–105 |
| `torus_transport_cyl` | `L` | TYPING | 95–105 |
| `torus_transport_cyl` | `hK` | SOURCE | 95–105 |
| `torus_transport_cyl` | `hQ1` | SOURCE | 95–105 |
| `torus_transport_cyl` | `hQ2` | SOURCE | 95–105 |
| `torus_transport_cyl` | `U` | TYPING | 95–105 |
| `torus_transport_cyl` | `hU` | SOURCE | 95–105 |
| `torus_transport_phys` | `d` | TYPING | 95–105 |
| `torus_transport_phys` | `c` | TYPING | 95–105 |
| `torus_transport_phys` | `hc` | SOURCE | 95–105 |
| `torus_transport_phys` | `O` | TYPING | 95–105 |
| `torus_transport_phys` | `Ψ` | TYPING | 95–105 |
| `torus_transport_phys` | `hΨ` | SOURCE | 95–105 |
| `torus_transport_phys` | `H` | TYPING | 95–105 |
| `torus_transport_phys` | `w` | TYPING | 95–105 |
| `torus_transport_phys` | `K` | TYPING | 95–105 |
| `torus_transport_phys` | `L` | TYPING | 95–105 |
| `torus_transport_phys` | `hK` | SOURCE | 95–105 |
| `torus_transport_phys` | `hQ1` | SOURCE | 95–105 |
| `torus_transport_phys` | `hQ2` | SOURCE | 95–105 |
| `torus_transport_phys` | `γ` | TYPING | 95–105 |
| `torus_transport_phys` | `τ` | TYPING | 95–105 |
| `torus_transport_phys` | `hγ` | SOURCE | 95–105 |
| `torus_transport_phys` | `hτ` | SOURCE | 95–105 |
| `torus_transport_phys` | `hw` | SOURCE | 95–105 |
| `analyticOnNhd_periodOne_iff` | `d` | TYPING | 132 |
| `analyticOnNhd_periodOne_iff` | `κ` | TYPING | 132 |
| `fderiv_periodOne` | `d` | TYPING | 132 |
| `fderiv_periodOne` | `κ` | TYPING | 132 |
| `fderiv_periodOne` | `θ` | TYPING | 132 |
| `periodOne_lattice_iff` | `d` | TYPING | 132 |
| `periodOne_lattice_iff` | `κ` | TYPING | 132 |
| `periodOne_lattice_iff` | `T` | TYPING | 132 |
| `periodOne_injMod_iff` | `d` | TYPING | 132 |
| `periodOne_injMod_iff` | `κ` | TYPING | 132 |
| `periodOne_hasDerivAt_iff` | `d` | TYPING | 132 |
| `periodOne_hasDerivAt_iff` | `κ` | TYPING | 132 |
| `periodOne_hasDerivAt_iff` | `ω` | TYPING | 132 |
| `periodOne_hasDerivAt_iff` | `θ` | TYPING | 132 |
| `periodOne_hasDerivAt_iff` | `v` | TYPING | 132 |
| `periodOne_hasDerivAt_iff` | `t` | TYPING | 132 |
| `isLatticeTorus_periodOne_iff` | `d` | TYPING | 132 |
| `isLatticeTorus_periodOne_iff` | `G` | TYPING | 132 |
| `isLatticeTorus_periodOne_iff` | `O` | TYPING | 132 |
| `isLatticeTorus_periodOne_iff` | `ω` | TYPING | 132 |
| `isLatticeTorus_periodOne_iff` | `κ` | TYPING | 132 |
| `cyl_pipeline` | `a` | TYPING | 143 |
| `cyl_pipeline` | `b` | TYPING | 143 |
| `cyl_pipeline` | `H` | TYPING | 143 |
| `cyl_pipeline` | `Φ` | TYPING | 143 |
| `cyl_pipeline` | `O₀` | TYPING | 143 |
| `cyl_pipeline` | `hΦ` | SOURCE | 143 |
| `cyl_pipeline` | `hQ1` | SOURCE | 143 |
| `cyl_pipeline` | `hQ2` | SOURCE | 143 |
| `cyl_pipeline` | `w` | TYPING | 143 |
| `cyl_pipeline` | `K₃` | TYPING | 143 |
| `cyl_pipeline` | `hK` | SOURCE | 143 |
| `cyl_pipeline` | `U` | TYPING | 143 |
| `cyl_pipeline` | `hU` | SOURCE | 143 |
| `phys_pipeline` | `d` | TYPING | 150 |
| `phys_pipeline` | `H` | TYPING | 150 |
| `phys_pipeline` | `Φ` | TYPING | 150 |
| `phys_pipeline` | `O₀` | TYPING | 150 |
| `phys_pipeline` | `hΦ` | SOURCE | 150 |
| `phys_pipeline` | `hQ1` | SOURCE | 150 |
| `phys_pipeline` | `hQ2` | SOURCE | 150 |
| `phys_pipeline` | `κ` | TYPING | 150 |
| `phys_pipeline` | `ω` | TYPING | 150 |
| `phys_pipeline` | `hκ` | SOURCE | 150 |
| `phys_pipeline` | `γ` | TYPING | 150 |
| `phys_pipeline` | `τ` | TYPING | 150 |
| `phys_pipeline` | `hγ` | SOURCE | 150 |
| `phys_pipeline` | `hτ` | SOURCE | 150 |
| `phys_pipeline` | `hω` | SOURCE | 150 |

Outer-binder counts: SOURCE=30, TYPING=63, STANDING=0, RULED=0, EXCESS=0. Bundled SOURCE clauses are expanded in the preceding premise table.
