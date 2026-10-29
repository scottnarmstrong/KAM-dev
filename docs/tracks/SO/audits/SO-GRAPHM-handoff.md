# SO-GRAPHM prover handoff (branch inp-sographm, 032b279f; track SO package run by the main orchestrator)


## Files
- new: `KAM/SpinOrbit/Graph/Inverse.lean` (446 lines, module, no heartbeat overrides). Nothing else touched.
  `KAM.lean` is out of date (new module); the orchestrator regenerates it (rule 10).

## Statements (no signed SO-GRAPHM statement exists: SOSignatures §I only signs `soBarrier_of_cert`
## which needs `checkSoGraph`/`SoGraphCert`, owned by post-gate SO-GRAPH; I proved the exact-torus core)
- `KAM.SpinOrbit.soBarrier_of_torus`: real-variable core. Data: `Q Pp dQ : ℝ → ℝ → ℝ` (angle q, momentum p
  as functions of torus angles (x,y); φ = y + c; frequency (ν,1)); continuity, `Q(x+1,y)=Q+1`, `Q(x,y+1)=Q`,
  `Pp` periodic, `∂ₓQ = dQ ≥ m > 0`, flow equations `d/dt Q(x+tν,y+t)|₀ = Pp`,
  `d/dt Pp(..)|₀ = -soVq (Q x y) (y+c)`, `lo ≤ Pp ≤ hi`. Conclusion `Nonempty (SoBarrier lo hi)`.
- `KAM.SpinOrbit.soBarrier_of_exact_torus`: from the complex exact torus `Kinf` (holomorphic on strip,
  `IsPrimaryOnStrip`, `IsRealOnReals`, `invarianceError soHC Kinf (sinf • ωstar) = 0`, Diophantine) with
  `m ≤ Re (D Kinf (x,y) (1,0)).1 0` and `lo ≤ Re (Kinf (x,y)).2 0 ≤ hi` on reals. It calls
  `KAM.Certificate.clock_frequency` (j = 1, D = univ; `∂_J soHC = 1` proved from `fderiv_soHC_apply`).
  SO-GRAPH must supply `mono > disp/ρ∞` ⇒ the `m` bound (Cauchy transfer) and the p-range.
- Helpers in `KAM.SpinOrbit.SoGraph`: `Torus` (hypothesis bundle), `Torus.inv` (graph inversion),
  `continuous_inv`, `inv_add_one`, `inv_φ_add_one`, `graph`, `invariant`, `realPt/realQ/realP`, etc.

## Approach
Strict monotonicity + `Q(x+k)=Q x + k` ⇒ unique inverse `G(q,φ)` (IVT). Joint continuity by the estimate
`m|G(q,φ)-G(q₀,φ₀)| ≤ |q-q₀| + |Q(x₀,φ₀-c)-Q(x₀,φ-c)|`. `P = Pp(G(q,φ), φ-c)`; periodicity from the shift
laws of `G`. Invariance: a solution through a graph point equals the torus orbit (explicit solution of
`soField`, `gen_uniqueness`). Complex bridge: real parts, `HasDerivAt` along real lines of the holomorphic
`Kinf`, invariance error ⇒ `soExtFieldC`.

## Checks
- `LEAN_NUM_THREADS=1 inp_lake_build.sh /root/code/KAM-inp-sographm KAM.SpinOrbit.Graph.Inverse`: success, no warnings in my file.
- `sh scripts/lint_sources.sh`: only complaint `KAM.lean is out of date`; modules check PASS (1292 files),
  frozen guard OK, ABI hashes OK.
- `#print axioms soBarrier_of_torus` and `soBarrier_of_exact_torus`: `[propext, Classical.choice, Quot.sound]`.
- No lines > 100 columns; no `sorry`.

## Uncertainties / errata
- Interface choice: the mono hypothesis is stated on `Re ∂_{θ₀}q` at real points (`realPt 1 0` direction);
  the `mono > disp/ρ∞` Cauchy transfer is left to SO-GRAPH. `ω* ≠ 0`/irrationality of ν is not needed.
- No errata in pinned sources found. No deviations from signed statements (none signed for this package).

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, Revision 4); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean. Signature file section I 'KAM/SpinOrbit/Graph.lean: graph inversion of an exact torus' (Revision 2: mono > disp/rho_inf). Owner ruling O4: continuous graphs (analyticity of the graph is a later corollary). Check that the exact torus hypotheses are exactly what the isoenergetic theorem (KAM.Iso.Apost.g1_explicit) plus the landed clock lemma deliver, that the inversion is proved at every clock phase, and that the resulting graph is an invariant barrier in the exact sense of SO-CONF's SoBarrier (KAM/SpinOrbit/Barrier.lean, landed). Orchestrator renames: hasDerivAt_line(_K) -> graphHasDerivAt_line(K); SoGraph.abs_sub_le -> graphAbs_sub_le (root shadow).

AUDIT FOCUS: the package's signed declarations match the draft signatures verbatim; every proof is sound with no added premise; the slice the design assigns to these modules is complete. Audit ONLY KAM/SpinOrbit/Graph/Inverse.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY (including fully qualified names); (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100, no native_decide or axiom.

## Round 2 (orchestrator hygiene repair, commit 6bb3bcd2)

Audit 1: mathematics PASS WITH NOTES, FAIL on hygiene only. Mechanical repair by the orchestrator, no proof change:
SoGraph.strictMono -> soStrictMono; Torus.exists_inv/inv_unique/inv_spec/inv_apply/continuous_inv/inv/inv_add_one/
inv_φ_add_one -> Torus.soGraphInv_exists/soGraphInv_unique/soGraphInv_spec/soGraphInv_apply/continuous_soGraphInv/
soGraphInv/soGraphInv_add_one/soGraphInv_periodic_φ (the names the module docstring advertised; docstring updated);
three lines over 100 columns wrapped. Rebuilt through the compile gate: success; short-name check OK.
ROUND 2 FOCUS: are all audit-1 hygiene findings closed (no public short name reused from Mathlib or KAM, no root
shadow, lines <= 100, docstring accurate)? Did the renames change any statement (they must not)? Verdict.

## Round 3 (orchestrator naming repair, commit 0fecbb3f)

Audit 2: mathematics PASS WITH NOTES, FAIL on three reused short names. Renamed (no proof or statement change):
Torus.graph -> Torus.soGraphFun (with continuous_graph -> continuous_soGraphFun, graph_apply -> soGraphFun_apply),
Torus.orbit -> Torus.soOrbit (hasDerivAt_orbit -> hasDerivAt_soOrbit, orbit_mem -> soOrbit_mem),
Torus.invariant -> Torus.soGraph_invariant. The orchestrator then scanned ALL 36 public short names of the module
against every declaration header in Mathlib and in KAM (theorem/lemma/def/abbrev/structure/class/instance, any
namespace): no match. Rebuilt through the compile gate: success.
ROUND 3 FOCUS: naming closed? Any statement changed by the renames (must not)? Verdict.
