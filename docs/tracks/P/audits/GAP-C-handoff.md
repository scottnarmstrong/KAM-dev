# GAP-C prover handoff (branch inp-gapc, b7316958; off inp with B12; offloaded gap-fill package run by the main orchestrator)


**Files:** new `KAM/Planetary/WeakKAM/AdmissibleAdapted.lean` (imports `Admissible` only; ~55 lines).
KAM.lean not edited (lint reports "KAM.lean is out of date; run scripts/gen_root_imports.py" — expected,
the orchestrator regenerates it).

**Declaration:** `KAM.Planetary.adm_choice_initial_adapted` (unsigned, docstring cites stepP:p11a:fr-list):
hyps `hf : SelectionPerturbation d f ε`, `0 < ε`, `ε ≤ selectionAdmissible d` (those of `free_radius`);
concl: `(selectionAdapted d ε).ε₀ = ε + n/2*C₁*s₀^2 ∧ ∀ x ∈ selectionDomain d.strip s₀ (actionNbhd d.K t₀),
‖selectionInitial d f x - ∑ i, fderiv ℂ d.h x.2 (Pi.single i 1) * x.1.2 i‖ ≤ (selectionAdapted d ε).ε₀`
(the A7 clause in the form of `adm_choice_initial`, plus the ε₀ identity, which `adm_choice_initial` also carries).

**Approach:** as `iterPre_base`: `free_radius` gives A1-A6 and `ε₀ = ε + n/2 C₁ s₀²`; `t₀ ≤ ϑ`
from `hA.t_le` and `√n ≥ 1`; `s₀ ≤ ϑ` from `hA.radius`; then `initial` (second component) and
`ε + n/2 C₁ s₀² ≤ ε₀`.

**Checks:** gate build `KAM.Planetary.WeakKAM.AdmissibleAdapted`: success (only pre-existing warnings
in Admissible.lean). `#print axioms`: propext, Classical.choice, Quot.sound. `scripts/lint_sources.sh`:
check_lean_modules PASS, frozen-anchor guard OK, ABI hashes OK (only the KAM.lean-stale note). No lines > 100.

**Coverage of bpP:p11a:free-radius:** `free_radius` (A1-A6, s₀ ≤ adm s₀, ε₀ identity, ε₀/s₀ = √(2nC₁ε),
≤ λmax) together with this lemma (A7) states every clause I could identify from the node's
SOURCE_CONCLUSION, as far as read from the brief's description; I did not re-audit the blueprint lines
line by line — the orchestrator should confirm against DEPGRAPH.md.

**Uncertainties / errata / deviations:** none. No design signals.

ORCHESTRATOR RULING (OVERNIGHT 23:30): append-only gap fill requested by the sub-orchestrator: stepP:p11a:fr-list (A7 at the adapted radius) was used inside B10's iterPre_base but never stated.

AUDIT FOCUS: read NODE: stepP:p11a:fr-list and NODE: bpP:p11a:free-radius in docs/graph/P/DEPGRAPH.md and the cited blueprint lines. Verdict: does adm_choice_initial_adapted state the literal fr-list conclusion (A7 at selectionAdapted d eps, in the form of adm_choice_initial) under only free_radius's hypotheses, and does free_radius together with it establish every clause of bpP:p11a:free-radius? Audit ONLY KAM/Planetary/WeakKAM/AdmissibleAdapted.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
