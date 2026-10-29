# E11 prover handoff (branch inp-p14-e11, df9039a2; track P P14, run by the main orchestrator)


Branch `inp-p14-e11`, head df9039a2. Already contained inp at/after 677cbecf (merge-base check: yes), so no new merge was needed.

## Files
- NEW `KAM/Planetary/Exponential/Stopped.lean` (377 lines, all ≤100 columns). No other file changed.
  `KAM.lean` NOT regenerated (rule 10): the only module missing from it is `KAM.Planetary.Exponential.Stopped`.

## Declarations (all in `KAM.Planetary`)
| Graph node | Lean declaration |
|---|---|
| bpP:p14:stopped | `stopped` — signature byte-identical to P14Signatures.lean (diff of the telescope: IDENTICAL) |
| st-thr | inside `stopped`: two applications of `KAM.Nekhoroshev.partialConvex_nekhoroshev` (h, -h); `nu0 = min 1 (min μ₊ (min μ₋ (min (κ^b⁻¹) (ε_D^b⁻¹))))`, `ε_D = (√(2A) - √(2·outerAMD))/√(2n)` |
| st-core (fast) | `stopped_fast_erosion` |
| st-core (slow) | `stopped_slow_erosion` (Cauchy–Schwarz over `Fin n ⊕ Fin n`; hypothesis `√(2A₁) + √(2n) ε < √(2A)`) |
| st-sol | `stopped_isSolutionOn_forward` (H⁺ on [0,r]), `stopped_isSolutionOn_reverse` (H⁻ for (-h,-P) on [0,-l], curve s ↦ y(-s)), `stopped_hamiltonian_neg` (H⁻ = -H⁺) |
| st-seg, st-fwd, st-bwd, st-phys | inside `stopped` (lift E9 → working cylinder; forward with C=r; backward with C=-l; coordinate ≤ max-norm) |
Support: `fastBox_eq_pi`, `isOpen_fastBox`, `convex_fastBox`, `isOpen_slowBall`, `isOpen_workingCylinder`,
`planetaryTimeExponent_eq_partial`, `planetaryDriftExponent_eq_partial`, `planetaryDriftExponent_pos`.
Short names grep-checked: none used elsewhere in KAM.

## Approach (as in the design ~l.443)
N root with n fast actions, k=n, G=`fastBox B κ`, G'=`fastBox B (2κ)` (open, convex via a product of open intervals),
D=`slowBall n A` (open), ρ, g, v, M and the collar/holomorphic/C²/reality/Hessian/definite clauses from `h_data`
(and `keplerDataNeg_*` + the `-h` HasDefiniteFastPart clause for the second call), done before fixing P, C or the curve.
κ,e,A from `enlarge`; ρ,B0,P from `perturbation` (B0 is the witness). Segment lifted by `lift`; fields identified by
`differentiableAt_hnu_field` with U = the (open) working cylinder. Exponents rewritten via the proved equalities
planetary* = partial*. No whole-window slow confinement assumed: slow erosion is checked pointwise on the tested segment
from `physicalAMD < outerAMD`.

## Checks (exact)
- `inp_lake_build.sh /root/code/KAM-inp-p14-e11 KAM.Planetary.Exponential.Stopped`: EXIT 0,
  "Build completed successfully (9310 jobs)"; zero warnings/errors in Stopped.lean (warnings only in upstream N files).
- `sh scripts/lint_sources.sh`: exit 1, solely because
  "KAM.lean is out of date; run scripts/gen_root_imports.py" (new module; orchestrator regenerates). Other output:
  `check_lean_modules: PASS (1337 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`,
  `ABI HASHES OK (144 frozen declarations)`.
- No maxHeartbeats/heartbeat overrides, no sorry/axiom/native_decide, no EuclideanSpace (grep empty).

## #print axioms (lake env lean on a scratch file importing the module)
```
'KAM.Planetary.stopped' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_slow_erosion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_fast_erosion' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_isSolutionOn_forward' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Planetary.stopped_isSolutionOn_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Quarantine
Imports the SEALED frozen anchor `KAM.Frozen.Nekhoroshev.Theorems.PartialConvexNekhoroshev` (as released in the brief update);
no `KAM.Provider.*` import, no DRAFT_SORRY anchor. Frozen Defs only otherwise.

## Uncertainties / design signals / errata
- None blocking. No heartbeat problems (whole module elaborates in ~12 s).
- Deviation (minor, internal): ν₀ uses `κ^(b⁻¹)`, `ε_D^(b⁻¹)` (= design's 1/b). `stopped_slow_erosion` takes the
  sufficient condition `√(2A₁)+√(2n)ε<√(2A)` instead of ε<ε_D; `stopped` derives it from ν^b<ε_D.
- No suspected errata in pinned sources.

CONTEXT: E11 proves the signed theorem stopped (P14Signatures.lean line 363), the critical path to the last frozen theorem of the original project, planetaryExponentialSafety (E12 expsafe and the provider are proved parametrically in stopped on inp-p14-e12, in audit). It applies the frozen anchor KAM.Nekhoroshev.partialConvex_nekhoroshev, SEALED by Zohar's team (a88de4b6; independent seal-key audit NSEAL-PARTIAL: proof PASS). Design docs/tracks/P/design/P14-LEAN-DESIGN.md (row E11, gate N2, the N-root application near line 443, the stopped row of the binder table) and its audits.

AUDIT FOCUS: (1) stopped's type is byte-identical to the signed statement; (2) the N root is applied with EXACTLY the design's data (G = fastBox B kappa, G' = fastBox B (2 kappa), D = slowBall n A, open/convex proofs, the collar/holomorphic/C2/reality/Hessian/definite clauses) and every hypothesis of the frozen N statement is DISCHARGED, for both h and -h; (3) the quantifier order of stopped (B0, nu0 chosen before mu, T, delta, z0) and the time window T <= (B0 mu)^-1 exp((B0 mu)^-a) are honoured; slow erosion is checked pointwise on the tested segment, never assumed for the whole window; (4) no import of a provider or a DRAFT_SORRY anchor; no conclusion-shaped premise in any helper used; (5) hygiene: names (KAM and Mathlib), lines <= 100, no native_decide or axiom. Audit ONLY KAM/Planetary/Exponential/Stopped.lean.
