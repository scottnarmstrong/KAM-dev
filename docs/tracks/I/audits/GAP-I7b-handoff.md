# GAP-I7b prover handoff (branch inp-gi7b, a2e38a9c; off inp; track I graph-gap programme package run by the main orchestrator)


**Files:** new `KAM/Iso/TransferStepNodes.lean` (~270 lines). No landed file edited. KAM.lean not regenerated
(`lint_sources.sh` reports "KAM.lean is out of date": the orchestrator runs `scripts/gen_root_imports.py`).

## Node -> declaration (all in `KAM.Iso`)
| node | declaration | content |
|---|---|---|
| `stepI:p7:he-smooth` | `he_smooth μ` | for a ∈ {primary₁ μ, primary₂ μ}: radiusSq(z.1 - a) = explicit quadratic; analytic on univ; > 0 on W_μ; radius and its inverse `AnalyticOnNhd` on W_μ; remaining terms analytic on univ; `ContDiffOn ℝ ∞ (restrictedHamTotal μ)` on W_μ |
| `bpI:p7:orbit-maps-e` (k clause) | `orbitMapC_k_holomorphic` | on `orbitDomC e₁` (0<e₁<1): Re(1-e²)>0; k=(1-e²)^(1/2) holomorphic; k²=1-e²; real sqrt at real e, e²<1; `orbitMapC e₁` with 5th coordinate replaced by k is holomorphic |
| `stepI:p7:tr-cf` | `tr_cf` | under `transfer`'s hypotheses, ∀ t∈J: (L,G)∈K, S z̃(t) ∈ deDom, phaseToC ∈ UDelta K (exactDelta K), CollisionFree μ (delaunay (S z̃(t))) |
| `stepI:p7:tr-chain` | `tr_chain` | ∀ t∈J: HasDerivAt zt X; X = X_{(R∘Q)∘S}; HasDerivAt (Q∘S∘zt) (DQ(S z̃)(S X)); that vector = X_{restrictedHamTotal μ}(z t) = restrictedVectorField μ ⟨z t, hcf⟩; radius/elements/energy clauses of `transfer_identities` |

All take only the source premises (`SafeAction`, kRhoMax<1, B⊆2πK, |μ|<exactMu2, `IsHamiltonianSolutionOn`); proved dependencies are rebuilt inside the proofs (reusing `PeriodOneAux.periodOne_real` etc., not as hypotheses).

Notes: tr-cf's "S z̃(t) real" is encoded as membership in `deDom`/`UDelta` of the real image `phaseToC (S z̃(t))` (real by construction). δ₂ = `exactDelta K`.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-gi7b KAM.Iso.TransferStepNodes`: "Build completed successfully", no warnings in my file.
- `sh scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; only "KAM.lean is out of date" (generated).
- `#print axioms` of he_smooth, orbitMapC_k_holomorphic, tr_cf, tr_chain: [propext, Classical.choice, Quot.sound].
- No heartbeat overrides; lines ≤ 100.

## Uncertainties / errata / deviations
None found. he-smooth: radiusSq's private `radiusSq_def` was re-proved locally (`hsq`, inside the proof). Short names he_smooth, tr_cf, tr_chain, orbitMapC_k_holomorphic were grepped: unused in KAM.

ORCHESTRATOR RULING: track I graph-gap programme (/root/code/KAM-inp/.drafts/briefs/offload-main/GAP-PLAN-I.md, section GAP-I7b). Ruling 05:10: also supplies the missing 'k = sqrt(1-e^2) holomorphic' clause of the PROVED parent bpI:p7:orbit-maps-e (over-claim note); check that orbitMapC_k_holomorphic states it on the source's domain. KAM.lean regeneration is the sub-orchestrator's job at merge, not a finding.

AUDIT FOCUS: for EVERY node in the handoff's node table, read its NODE record in docs/graph/I/DEPGRAPH.md (SOURCE_HYPOTHESES, SOURCE_QUANTIFIERS, SOURCE_CONCLUSION) and the blueprint-I lines it cites; per-node verdict: does the named declaration state the literal conclusion under only the source's hypotheses, quantifiers in source order? An export taking a proved dependency's OUTPUT as a premise is a FAIL. Audit ONLY KAM/Iso/TransferStepNodes.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE: every graph node the design's node table maps to these modules is established (in the proof or as an export); an UNSIGNED export named after a graph node must state that node's literal conclusion, while a SIGNED declaration follows the signature file (where the design deliberately narrows it, check that every consumer's needs are met); (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100.
