# SO-AIF prover handoff (branch inp-soaif, 1d59185c; off inp; track SO package run by the main orchestrator)


## Files (new)
KAM/Certificate/Arith/{Interface,PiEnclosure,Transcendental,Roots}.lean (89/63/71/363 lines).

## Approach
- Interface: classes `CertArith`, `LawfulCertArith`, `CC`, `CC.toC`, `CC.conj`, `toC_conj`, `toC_zero` verbatim.
- PiEnclosure: `PiEnclosure`, `checkPiEnclosure`, `checkPiEnclosure_sound` verbatim statement. Check handles
  rounding: `upAdd (add c (neg r)) (addErr c (neg r)) ≤ ofRatDown lo` and
  `upAdd (ofRatUp hi) (addErr c r) ≤ add c r` (imports landed PiHigh).
- Transcendental: `ratExpUp` (halve s times, Taylor N + Real.exp_bound remainder, s squarings via
  iterate; fallback `3^⌈q⌉` when `q/2^s > 1` or `N = 0`, so the signed theorem has no extra hypothesis),
  `exp_le_ratExpUp` verbatim.
- Roots: `checkRootEnclosure`, `rpow_mem_of_checkRootEnclosure`, `sqrt_mem_of_checkRootEnclosure` verbatim.
  `CertBall` complex ball arithmetic (`ofRat`, `one`, `plus`, `times`, soundness lemmas), `expAux`
  Taylor ball recursion, `certCExp` (Taylor sum of N+1 terms in ball arithmetic + `eRem (N+1)` remainder).

## DEVIATION / signed statement false: `certCExp_sound`
The signed `certCExp_sound` (no hypothesis on size of `z`, `zRad`) cannot hold for any definition
over the interface operations: for N = 0 the output is a bounded-depth computation, which cannot
dominate `exp (val zRad)` as `val zRad → ∞` (α = ℚ). Also `Complex.exp_bound` needs `‖w‖ ≤ 1`.
Provided instead: `certCExp_sound_of_small` with hypothesis `‖z.toC‖ + val zRad ≤ 1`
(domain restriction, not conclusion-shaped) and the backend test `certCExpSmall` with
`certCExpSmall_sound : certCExpSmall z zRad = true → ‖z.toC‖ + val zRad ≤ 1`. `certCExp` itself has the
signed type. Owner/design decision needed (guard hypothesis, or argument reduction in client).
Note the Taylor order is N+1 terms (so N = 0 needs no positivity hypothesis).

## Checks
- `inp_lake_build.sh` on the four modules: Build completed successfully (2844 jobs); only warning is the
  pre-existing PiHigh unused simp arg (not mine).
- `scripts/lint_sources.sh`: check_lean_modules PASS; FROZEN-ANCHOR GUARD OK; ABI HASHES OK; no over-100-col
  lines in my files; "KAM.lean is out of date" is the expected generated-file notice (not touched).
- `#print axioms` of CC.toC_conj, CC.toC_zero, checkPiEnclosure_sound, exp_le_ratExpUp,
  rpow_mem_of_checkRootEnclosure, sqrt_mem_of_checkRootEnclosure, certCExp_sound_of_small,
  certCExpSmall_sound: all `[propext, Classical.choice, Quot.sound]`.
- No set_option, no native_decide, no sorry.

## Uncertainties
- No concrete backend instances (SO-ABK) so nothing exercised on ℚ/fixed point.
- Signed `instCertArithRat` etc. intentionally not provided.
- Radius of `certCExp` is crude (naive ball Horner-free expansion); fine for small balls only.
No errata in pinned sources.

CONTEXT: track SO (plan /root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md; design /root/code/KAM-inp-design-so/docs/tracks/SO/design/SO-LEAN-DESIGN.md, now Revision 3); draft signatures /root/code/KAM-inp/.drafts/design/SOSignatures.lean. ORCHESTRATOR RULING (12:10): the signed certCExp_sound (no size hypothesis) is false as the prover shows; the accepted replacement is certCExp_sound_of_small with the domain hypothesis norm(z) + val zRad <= 1 plus the checkable test certCExpSmall with certCExpSmall_sound; judge that this hypothesis is a legitimate domain restriction (not conclusion-shaped) and that the replacement is sound. The concrete exact-Q instance (instCertArithRat) moved to SO-AIF in design Revision 3 after this package started; its absence is not a finding (follow-up). Orchestrator rename: CertBall.one -> CertBall.oneBall (short-name clash).

AUDIT FOCUS: the package's signed declarations match the draft signatures verbatim (except the ruled deviation above); every proof is sound with no added premise; the slice the design assigns to these modules is complete. Audit ONLY KAM/Certificate/Arith/{Interface,PiEnclosure,Roots,Transcendental}.lean. Common to all: (a) every SIGNED declaration = signature file EXACTLY; (b) the slice COMPLETE; (c) proof soundness, no added premises; (d) hygiene: no EuclideanSpace, no reused public HELPER short name, no harmful root shadow, lines <= 100, no native_decide or axiom.
