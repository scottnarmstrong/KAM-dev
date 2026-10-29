# GAP-ISM prover handoff (branch inp-gism, 15868249; off inp; track I graph-gap programme package run by the main orchestrator)


**Files:** new `KAM/Iso/LeftoverNodes.lean` (append-only; no landed file edited).

## Nodes -> declarations
| node | declaration |
|---|---|
| stepI:p6:k-pos | `KAM.Iso.k_pos_node` : `0 < κ → Ω ≠ 0 → ∀ L : {L // 0 < L}, 0 < 3κΩ²/L⁴ ∧ 0 < (keplerBorder κ Ω L).det` (uses landed `keplerBorder_det`; no `0 < Ω`) |
| stepI:p3:tori-patch | `KAM.Iso.Charts.tori_patch_node`: finite patch family `P` (`IsPatch` each = bpI:p3:patch), `closure B' ⊆ ⋃ ball c (ρc c)` (bpI:p3:cover), `ε₁ ≤ δE c/2` on `P` (bpI:p3:uniform), `ε < ε₁`, `I₀ ∈ closure B'`, `|E - h(I₀)| ≤ ε` ⊢ `∃ c ∈ P, ‖I₀-c‖<ρc ∧ |h(I₀)-h(c)|<δE/2 ∧ |E-h(c)| ≤ ε+δE/2 ∧ ε+δE/2 ≤ δE`. Patches/uniform constants are fixed before `f, ε, E, I₀` (they are variables independent of them). `0 ≤ ε` is not needed, so omitted (stronger). The content was inline in `tori` (Tori.lean ~L336-358), which is untouched. |
| bpI:p7:sec-ham#data | `KAM.Iso.sec_ham_data μ`: (1) `{z \| CollisionFree μ z} = {0<radius(q-a₁) ∧ 0<radius(q-a₂)}` (rfl); (2) `= {q ≠ a₁ μ ∧ q ≠ a₂ μ}`; (3) `IsOpen` (via landed `isOpen_collisionFree`); (4) `restrictedHamiltonian μ ⟨z,hz⟩ =` the explicit formula (rfl); (5) `restrictedVectorField μ ⟨z,hz⟩ =` the explicit formula (rfl). |

## sec-ham#data source objects -> Lean
- W_μ: `{z : (Fin 2 → ℝ) × (Fin 2 → ℝ) | KAM.Iso.CollisionFree μ z}`, `KAM/Frozen/Iso/Defs/CollisionFree.lean` (def at `CollisionFree`, L~35).
- a₁(μ), a₂(μ): `KAM.Iso.primary₁` (`KAM/Frozen/Iso/Defs/Primary1.lean`:37), `primary₂` (`Primary2.lean`:36).
- rad: `KAM.Iso.radius` (`Radius.lean`:37) = `√(radiusSq q)`; `radiusSq` (`RadiusSq.lean`:36).
- r_j = rad(q - a_j(μ)): a notation, not a definition; written out as `radius (z.1 - primary_j μ)` in (1),(4),(5).
- H^R3_μ: `KAM.Iso.restrictedHamiltonian` (`RestrictedHamiltonian.lean`); V_μ: `KAM.Iso.restrictedVectorField` (`RestrictedVectorField.lean`); both defined on the subtype of `CollisionFree` points.
- Openness: landed `KAM.Iso.isOpen_collisionFree` (`KAM/Iso/RestrictedHam.lean`:57).
- Note: `r_j` is not a separate Lean object; the node's "defines" is covered by the frozen definitions plus these identities.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-gism KAM.Iso.LeftoverNodes`: Build completed successfully; no warning in my file (only pre-existing warnings in KAM/ODE/Exit, KAM/Kepler/Energy).
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK. It prints "KAM.lean is out of date; run scripts/gen_root_imports.py": expected, KAM.lean is generated and I did not touch it (orchestrator to regenerate).
- `#print axioms` of all three nodes: `[propext, Classical.choice, Quot.sound]`.
- File is 96 lines, lines ≤ 100 cols, no set_option.

## Uncertainties / errata / deviations
- tori-patch: the hypotheses use `IsPatch` and the cover/uniform facts as typing data (bpI:p3:cover/patch/uniform premises), not any proved output of `tori`. `hε : ε < ε₁` with `ε₁ ≤ δE c/2` stated per patch of `P`.
- No source errata found. No deviations beyond the omitted `0 ≤ ε`.

ORCHESTRATOR RULING (OVERNIGHT 05:25): three track I nodes left open by the sub-orchestrator's sync: stepI:p6:k-pos (source assumes Omega != 0; the landed lemma covered only 0 < Omega), stepI:p3:tori-patch (content inside Tori.lean, no audited export), bpI:p7:sec-ham#data (definition node that also asserts a property). Definition-node policy (02:30, owner to review): a definition node closes by naming its Lean definitions plus a definitions-audit row; its asserted properties need an export.

AUDIT FOCUS: (1) for stepI:p6:k-pos and stepI:p3:tori-patch, read the NODE records in docs/graph/I/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint-I lines; does k_pos_node / tori_patch_node state the literal conclusion under only the source's hypotheses, quantifiers in source order (no proved dependency's output as a premise)? (2) bpI:p7:sec-ham#data: a DEFINITIONS-AUDIT ROW for every source object listed in the handoff (W_mu, a_1, a_2, rad, r_j, H^R3_mu, V_mu): Lean definition (file:line) | FAITHFUL / FAITHFUL-WITH-NOTE / NOT FAITHFUL / MISSING | reason (body equals the source formula on the whole public carrier; no fallback branch); then whether sec_ham_data states the node's asserted properties (set identity, openness, the defining equations on W_mu) literally, and a per-node verdict CLOSABLE or not. Audit ONLY KAM/Iso/LeftoverNodes.lean (and read the frozen definitions it names). Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
