# GAP-C independent audit 1

Verdict: **PASS WITH NOTES for the requested A7 gap fill**. The new export proves the literal
A7 equality and bound at the adapted radius. Together with the existing `free_radius`, it
establishes A1–A7. **These two exports alone do not state every clause of the parent
`bpP:p11a:free-radius` node**: its iteration, parameter-selection and exported-sum transfers
belong to the existing B10/B12/B13 exports, as the design explicitly rules. Do not credit
this 47-line module alone with those transfers or a frozen theorem seal.

## Scope and authority

- Worktree: `/root/code/KAM-inp-gapc`; report written here as explicitly requested, overriding
  the generic brief's main-worktree output instruction.
- Audited HEAD: `b73169581597d6b46096a4a373e027a1431eda60`.
- Compared with `inp` at `ce5bc0c09a78b36777a59cdb8b93c5e544d380e6`, merge base
  `33f3bb0952de8f918a015b374f231ef9b4860120`, using the complete `git diff inp...HEAD`.
  That diff contains exactly one file, 47 added lines:
  `KAM/Planetary/WeakKAM/AdmissibleAdapted.lean`.
- Read AGENTS, PLAN, DECISIONS, the package-audit brief, GAP-C handoff and its overnight
  append-only ruling, the two requested graph nodes and cited blueprint text, the track-P
  statement, and relevant P11B design/signature and dependency definitions/proofs.
- No new provider, frozen anchor, signed declaration, definition or structure is in scope.
  Frozen/provider type-equality and seal-body probes are therefore inapplicable. The
  handoff explicitly marks this export unsigned; it is absent from P11BSignatures.
  Existing `free_radius` is unchanged and has the design's deliberately scalar signature.

## Node and declaration findings

| Node / declaration | Lean declaration | Verdict | Reason |
|---|---|---|---|
| New public export; A7 | `KAM.Planetary.adm_choice_initial_adapted` | PASS | Lines 27–33 state exactly A7 of `p11a3-iteration-selection.tex:215`, including its equality, on the full initial domain at `selectionAdapted d ε`. |
| `stepP:p11a:fr-list` | `free_radius` plus `adm_choice_initial_adapted` | PASS WITH NOTES | Graph `DEPGRAPH.md:26649–26674` literally asks for A1–A7, not A7 alone. `free_radius` returns A1–A6 in `SelectionAdmissibility`; the new export supplies A7. A fresh probe elaborated their conjunction. The new theorem alone is the A7 companion, not a standalone full-list export. |
| `stepP:p11a:fr-small` | Existing `free_radius`, `selectionAdapted` | PASS, contextual | `Admissible.lean:316–365` gives positive radius, radius ≤ fixed radius, the ε₀ identity, λ₀ formula and λ₀ bound; the adapted definition at :64–66 gives ε₀ = 2ε and the square-root radius. No change here. |
| `bpP:p11a:free-radius`, scalar and initial clauses | The preceding exports and schedule definitions | PASS | `p11a4-limit-family.tex:36–38`: radius and λ bounds, A1–A7, unchanged fixed constants, and Q₀ formula are accounted for as detailed below. |
| `bpP:p11a:free-radius`, consequence / `fr-other` | Existing `inductive_lemma_adapted`, `parameter_selection_adapted`, `wbud_exported` | PASS WITH NOTES, contextual only | These are separate existing transfer results, not conclusions of either audited A7 export or scalar `free_radius`. Their bodies/applicability were inspected; this audit does not independently rerun or re-audit those packages. |

### Literal statement, premises and proof

The added conclusion uses `selectionInitial d f x` minus the linear action term
`∑ i, fderiv ℂ d.h x.2 (Pi.single i 1) * x.1.2 i`. By `Initial.lean:26–29`, this is
`h(b+η)+f(θ,b+η)-h(b)-Dh(b)η`, the intended R₀. The carrier is exactly
`selectionDomain d.strip s₀ (actionNbhd d.K t₀)` with both radii from the adapted
schedule; `Data.lean:50–51` and the frozen `ComplexStrip`/`ActionNbhd` definitions
give the stipulated complex strip, max-norm action ball and parameter collar. The
bound is pointwise everywhere on that domain, with no smaller subset or altered norm.

The scalar hypotheses match `free_radius`: `d`, `0 < ε`, and `ε ≤ selectionAdmissible d`.
There is additionally `f` and `hf : SelectionPerturbation d f ε`. This is a legitimate
source premise, not a conclusion-shaped addition: `Data.lean:105–114` bundles only
holomorphy, periodicity, reality and the original perturbation bound. The standing
situation explicitly supplies it (`p11a4-limit-family.tex:31`); scalar `free_radius`
does not need it because it proves no analytic claim. Thus “only free_radius's
hypotheses” must include the standing perturbation input when asking for A7.

At lines 34–43 the proof obtains scalar admissibility and s₀ > 0, proves √n ≥ 1
from `d.n_pos`, derives t₀ ≤ ϑ and s₀ ≤ t₀/(8n) ≤ t₀ ≤ ϑ, and applies `initial`
with exactly its source hypotheses. Its second conjunct gives the Taylor bound;
the returned ε₀ identity converts that bound to ε₀ at line 45. No claimed bound
is assumed. All constants and their dependence are inherited unchanged. The
ε₀ identity is required by A7, not an added weakening or auxiliary output.

For A1–A6, the fields `t_pos`, `t_le`, `collar`, `increment`, `radius`, `quadratic`,
`weighted`, `closeness`, `cutoff_ge`, and `cutoff_loss` in `SelectionAdmissibility`
match `p11a3-iteration-selection.tex:209–214`. The remaining explanatory
inequalities in A1–A3 follow using √n ≥ 1, ϑ ≤ 1, and these fields. The new
proof explicitly derives the two domain inequalities needed by A7.

The parent node also specifies Q₀ and unchanged constants. `Schedule.lean:186–188`
defines exactly `C_Q * 2^n * T₀^τ * (ε₀/s₀) / (π * γ * (strip/24)^(n+1))`.
`selectionAdapted` retains μ, τ, γ, strip, T₀ and t₀ definitionally;
`selectionAdmissible d` has no ε argument. These clauses need no new premise.

For the parent's final “consequently” clause, `Iteration.lean:78–86` and
`Selection.lean:335–351` construct the iteration and selection at the adapted
schedule from the same raw inputs. For scalar exported sums,
`Budgets.lean:464–478` is general in `WeakBudgetCtx d a`; its constructor at
:69–74 applies to the adapted schedule using `free_radius`, reflexive parameter
equalities, positive s₀ and positive ε₀ = 2ε. This is the designated transfer
route, not an assumed iteration or a new premise. The design coverage ruling
at `P11B-LEAN-DESIGN.md:255–259` explicitly assigns these clauses to B10/B12/B13.

## Definitions and imports

No new `def`, `abbrev` or `structure`: classification is **none**. Referenced
objects are the actual initial Hamiltonian, domain and adapted square-root schedule;
no junk-value or fallback branch is used. Positive ε, n ≥ 1 and C₁ ≥ 1 guard the
square root and denominators in the relied-on scalar construction.

The only direct import is `KAM.Planetary.WeakKAM.Admissible`. A recursive local
import scan found 64 KAM modules, no provider imports and no frozen theorem
imports, hence no DRAFT_SORRY theorem dependency. The export's axiom probe also
excludes `sorryAx`. All declarations introduced here remain in `KAM.Planetary`;
a repository declaration search found exactly one `adm_choice_initial_adapted`.
There is no reused public helper name or root shadow.

## Independent checks

All Lean/Lake commands were sequential, with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No source, frozen file, manifest, generated file or git state was edited.

1. Targeted compile gate:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-gapc KAM.Planetary.WeakKAM.AdmissibleAdapted
   [inp-gate] slot 1 acquired 23:31:41 for KAM.Planetary.WeakKAM.AdmissibleAdapted
   Build completed successfully (9110 jobs).
   exit 0
   ```

   Replayed dependency warnings were unused-variable/style/deprecation warnings
   in Schedule, CutoffTensor, CutoffScale, Cutoff, FourierCutoffTail, StripBudget
   and Admissible. No new-module warning or default-heartbeat design signal.

2. Fresh scratch probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/GAPCAudit.lean
   'KAM.Planetary.adm_choice_initial_adapted' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

   The probe copied the new theorem's complete explicit statement and applied
   the export to `d f ε hf he hsmall`; a second example combined it with
   `(free_radius d ε he hsmall).1` to establish scalar admissibility ∧ A7.
   `#check @...` confirmed the implicit n and explicit binders. An initial
   probe attempt exited 1 because the auditor omitted `open KAM` for
   `actionNbhd`; this scratch-only namespace mistake was corrected before
   the successful run. No production edit was needed.

3. Kernel replay:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.AdmissibleAdapted
   replaying KAM.Planetary.WeakKAM.AdmissibleAdapted
   exit 0
   ```

   This is the only new lemma module; there is no provider module to add.

4. Repository lint:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1107 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1
   ```

   The sole failure is the explicitly permitted generated-root exception.
   The generated root was not regenerated. The ABI subprocess ran after
   all other Lean commands had finished.

5. Static checks: 47 lines, maximum Unicode line width 92; required copyright,
   `module`, `public import`, docstring and public section present. No forbidden
   proof token, resource override or `EuclideanSpace`. `git diff --check`: exit 0.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: empty, exit 0.
   Scratch probe removed after validation. Final status contains only this new
   report and the handoff that was already untracked at the start.

## Errata, deviations and limits

No suspected mathematical source defect or introduced deviation was found in
this slice. The full-list versus A7 distinction and the separate transfer
exports are coverage qualifications, not a silent change to the graph contract.
The graph's `fr-list` NOT_STARTED note at `DEPGRAPH.md:26677–26679` describes the
previous missing A7 and can now be updated by the orchestrator. No graph edit
was made. No frozen anchor is proved or made seal-ready by this infrastructure
package; anchor verdict is **not applicable**.
