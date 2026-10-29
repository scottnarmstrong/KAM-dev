# Seal-key audit request: P-EXP-SAFE `KAM.Planetary.planetaryExponentialSafety` (the last frozen theorem of the original project)

Branch inp-p14-seal (4c9d3335) = inp-p14-e11 (E11 `stopped`, in audit) + inp-p14-e12 (E12Q
`expsafe_of_stopped` and the provider helper `planetaryExponentialSafety_of_expsafe`, in audit) + two orchestrator
one-liners (commit 4c9d3335):
- KAM/Planetary/Exponential/Safety.lean: `theorem expsafe` (signed type copied verbatim from
  .drafts/design/P14Signatures.lean lines 546-572) := `expsafe_of_stopped hn (stopped hn) B hB`;
- KAM/Provider/Planetary/PlanetaryExponentialSafety.lean: `theorem planetaryExponentialSafety` (the provider; exact
  frozen telescope, signature lines 665-691) := `planetaryExponentialSafety_of_expsafe hn (KAM.Planetary.expsafe hn) B hB`.
The provider module builds (9324 jobs).

The frozen anchor KAM/Frozen/Planetary/Theorems/PlanetaryExponentialSafety.lean (manifest
planetary.d25.planetaryExponentialSafety.v1, DRAFT_SORRY, body `by sorry` at line 80) will be sealed by the
sub-orchestrator with the binder-applied body (D26, continuation indented 6 spaces past `exact` if wrapped):
  by exact KAM.Provider.Planetary.planetaryExponentialSafety hn B hB

AUDIT (refute-first; do not edit the real frozen file):
1. Exact-type probe: `example : type_of% @KAM.Planetary.planetaryExponentialSafety :=
   @KAM.Provider.Planetary.planetaryExponentialSafety` elaborates (import the frozen file's module and the provider in a
   scratch file).
2. Prospective seal: in a SCRATCH COPY of the frozen file (outside KAM/Frozen or under .drafts/scratch), replace `by sorry`
   with the body above and compile it; report the exact body that compiles.
3. `#print axioms` of the provider and of the prospective seal: only propext, Classical.choice, Quot.sound.
4. Kernel replay of the provider module and its new dependencies (Stopped, Safety) with the toolchain's leanchecker
   (/root/.elan/toolchains/leanprover--lean4---v4.35.0/bin/leanchecker; find its usage).
5. The two one-liners: types byte-identical to the signed ones; hstop/hexpsafe instantiated by the actual theorems.
6. Quarantine: only the frozen anchor (and the generated root KAM.lean, per the orchestrator ruling of 15:35) imports the
   provider; no non-provider module imports a DRAFT_SORRY anchor.
7. Quantifier order of the frozen statement (design P14 line 439): n, hn, B, hB fixed before muStar, c, C.
Write docs/tracks/P/audits/P14-SEAL-audit-1.md with a verdict and the exact seal body.
