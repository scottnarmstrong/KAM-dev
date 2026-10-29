# SO-CLOCK independent audit 1

Verdict: **PASS WITH NOTES** for the SO-CLOCK helper package. Both signed declarations
pass exact-text and elaborated-type checks; the clock proof is sound and the assigned
slice is complete. There is no frozen theorem anchor or provider in this package, so
this verdict does not seal an I/N/P anchor, certify numerical data, or close the lunar
barrier theorem. The notes concern the permitted generated-root lint exception and
the integration ownership of `phaseBasis`.

## Scope and authority

- Worktree: `/root/code/KAM-inp-soclock`; report written here as explicitly requested,
  overriding the generic brief's main-worktree destination.
- Audited HEAD: `0ba16e09657a1a04bf5fd273361368b392e1edbc`.
- Observed `inp`: `2dcaff9daa985bb46795fcefbf19a4c8cc773143`;
  merge base: `836e8efe03c1f2e23422a12dd35058c9bc7101a6`.
- Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the supplied
  `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and
  `docs/tracks/SO/audits/SO-CLOCK-handoff.md`, including its AUDIT FOCUS.
- Statement authority: `/root/code/KAM-inp/.drafts/design/SOSignatures.lean`,
  §D lines 327–329 and §H lines 836–849. SHA-256 of the inspected file:
  `49571edd6903210ca1414da3691e02da72404f4c1ec25533677ce04665c922f2`.
- Consumer authority: `/root/code/KAM/docs/explorations/lunar-spin-orbit-certificate-proposal.md`
  §7.1–7.2, and `/root/code/KAM/docs/campaign/design/SPIN-ORBIT-PLAN.md`, including O1.
  The referenced `SO-LEAN-DESIGN.md` and a track-SO statement/blueprint were not present
  in the inspected worktrees; the explicitly supplied draft signatures and proposal
  control this audit. No unrelated I/N/P theorem is claimed as implemented here.
- Read the frozen definitions of the strip, primary winding, reality, Diophantine
  condition, complex Hamiltonian field, and invariance error, and the averaging,
  Fourier-derivative, Fourier-uniqueness and `sumVec` interfaces used by the proof.

The full `git diff inp...HEAD` contains exactly two additions: `Clock.lean` (204 lines)
and `PhaseBasis.lean` (39 lines). No implementation changes were made by this audit.

## Declaration results

| Node / role | Lean declaration and location | Verdict | Reason |
|---|---|---|---|
| §D signed definition | `KAM.Certificate.phaseBasis`, PhaseBasis:28 | PASS | Entire declaration and body byte-identical to §D; correct angle/action basis on the whole carrier. |
| New public helper | `KAM.Certificate.phaseBasis_inr`, PhaseBasis:31 | PASS | Exactly the action basis `(0, Pi.single j 1)`; no premises beyond typing. |
| §H signed clock theorem | `KAM.Certificate.clock_frequency`, Clock:70 | PASS | Entire statement byte-identical to §H; copied statement elaborates with the audited theorem as its proof. |
| Private averaging helper | `torusAverage_const_complex`, Clock:33 | PASS | Unit-cube volume is one, including dimension zero. |
| Private Fourier helper | `torusCoeff_const_complex`, Clock:38 | PASS | Constant has only its zeroth Fourier coefficient. |
| Private derivative helper | `coord_hasFDerivAt`, Clock:47 | PASS | Chain rule for the first projection and coordinate projection; differentiability is a source premise. |
| Private winding helper | `periodic_clock`, Clock:55 | PASS | Subtracting the coordinate from a primary lift cancels the unit winding. |

No public helper short name is reused elsewhere in `KAM/`; declarations stay within
`KAM.Certificate`. The four proof helpers are private. No harmful root shadow was found.

## Definition classification and proof scrutiny

`phaseBasis` is the only new definition; there are no new abbreviations, structures,
classes or bundled proof premises. `sumVec` sends `(a,b)` to `Sum.elim a b`, so its inverse
on a singleton is the intended coordinate vector for either summand. The `.inr` identity
is proved in the module; an independent probe also proved the `.inl` identity.
There are no fallback values, truncated carriers or junk branches. The definition is
exposed through `@[expose] public section`.

At Clock:83–96 the proof projects `invarianceError = 0` onto angle coordinate `j`.
The frozen sign convention is `X_H(K) - DK ω`; the frozen field's angle component is
`fderiv H (0, single j 1)`. Thus `hH1`, applied at `Kinf θ` using `hKD`, gives
`D_ω Kinf,j = 1` with the correct sign and action basis.

At Clock:98–125, `w = Kinf,j - θ_j` is holomorphic on the open positive-width strip
and periodic by primary winding. Its directional derivative is `1 - ω_j` throughout
the strip. `torusAverage_complex_direction_eq_zero` integrates the derivative on the
real unit torus, justified by holomorphy on a surrounding strip and periodicity; it
does not assert integration over a complex domain. Averaging the constant derivative
and taking real parts gives `sinf * ωstar j = 1`. There is no missing integrability,
boundary term, domain containment or frequency normalization premise.

At Clock:127–185 the directional derivative vanishes. The Fourier derivative identity
gives `0 = (2π i Σ k_j ω_j) ŵ_k`. For nonzero integer `k`, its l1 size is positive;
`γ > 0` and the Diophantine inequality make the real dot product nonzero, even for
arbitrary real `τ`. The complex multiplier is therefore nonzero and every nonzero
Fourier coefficient vanishes. Continuity and periodicity of the real restriction
justify Fourier uniqueness on `v - torusAverage v`; its zeroth coefficient vanishes
by construction. This proves pointwise constancy on every real angle, not merely
almost everywhere. At Clock:187–202 reality at zero supplies the single real constant.

All premises are geometric/analytic source assumptions or typing data. In particular,
neither the forced frequency nor constancy of the correction is assumed. No positivity
of `sinf`, extra Hessian bound, normalization of the phase, or conclusion-shaped premise
was silently introduced. Dimension zero cannot supply `j : Fin 0`, as intended.

## Consumer applicability and limits

For `n = 2`, `j = 1`, `ωstar = ![ν/2, 1/2]`, the first conclusion gives `sinf = 2`
and hence `sinf • ωstar = ![ν,1]`. This exact algebraic specialization was elaborated
independently. The second conclusion gives one real `c` with clock lift `x₁ + c`
for all real `x`, exactly the phase shift required by proposal §7.1.

The consumer's Diophantine premise is on `ωstar`, while this theorem asks for the
output frequency. This is discharged without circularly assuming `sinf = 2`:
draft `CertifiedTorus` (lines 789–799) supplies `1 < sinf`, and the existing
`KAM.Iso.Linear.isDiophantine_smul` (KAM/Iso/Linear/Tools.lean:38) preserves the same
`γ,τ` for scalars at least one. Its proof factors the dot product and uses `1 ≤ sinf`.
Positive width and domain containment must likewise be extracted from the certificate's
positive strip and positive clearance. They are not conclusions supplied by SO-CLOCK.

This statement is sufficient for the assigned clock slice. Graph inversion, global
flow invariance, certificate soundness, and quantitative transport of a phase shift
remain separate consumer obligations. The clock theorem does not bound `|c|` or
the effect of reparametrization on closeness. Proposal §7.2 explicitly retains that
obligation; plan O1 defers graph-error transport for the first constant-window client.
No application of this theorem to an implemented lunar barrier was available here.

Integration note: SO-EXPR must import `KAM.Certificate.PhaseBasis` and omit its own
copy of the draft §D definition. The namespace and body already agree; declaring it
again would fail on merge. No duplicate exists in this checkout.

## Independent checks

Every Lean/Lake invocation was serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`;
the build used the prescribed gate, whose script supplies `nice -n 5`. Lint also ran
under these settings, including its internal ABI Lean probe.

1. `git diff inp...HEAD` inspected in full; `git diff --stat inp...HEAD`:
   two files, 243 insertions. `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`
   produced no output. `git diff --check inp...HEAD` exited 0 with no output.
2. Exact-text extraction from the supplied draft and production files printed:
   `clock signature byte equality: True` and
   `phaseBasis declaration/body byte equality: True`.
3. `LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-soclock KAM.Certificate.Clock`
   exited 0: `[inp-gate] slot 1 acquired 11:24:24 for KAM.Certificate.Clock`;
   `Build completed successfully (3163 jobs).` This target includes PhaseBasis.
4. `LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOClockAudit.lean`
   elaborated the copied signed statement with body
   `by exact KAM.Certificate.clock_frequency j hρ hH1 hKD hholo hprim hreal hinv hγ hdio`,
   both directions of `type_of%` equality, the signed basis body by `rfl`, the angle
   basis identity, and the lunar frequency specialization. Axioms output:

   ```text
   'KAM.Certificate.phaseBasis_inr' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Certificate.clock_frequency' depends on axioms: [propext, Classical.choice, Quot.sound]
   'SOClockAudit.clock_frequency_signed' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

   `#print KAM.Certificate.phaseBasis` showed exactly
   `fun {n} a => (sumVec n).symm (Pi.single a 1)`.
   Final probe exit: 0, without warnings. The initial successful probe emitted two
   unused-tactic warnings in its own arithmetic specialization; simplifying that
   scratch tactic briefly left `2 * (ν / 2) = ν` unsolved (exit 1). Adding the explicit
   ring step resolved it. Neither iteration changed a package source or its proof.
5. `LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Certificate.Clock KAM.Certificate.PhaseBasis`
   exited 0, output:

   ```text
   replaying KAM.Certificate.PhaseBasis
   replaying KAM.Certificate.Clock
   ```

6. `LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh` exited 1, with
   exactly the permitted generated-root exception and otherwise successful gates:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1284 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   The generic audit brief expressly allows this exception. The root was not regenerated.
7. Direct forbidden-token scan of both additions found no `sorry`, `admit`, `axiom`,
   `unsafe`, `opaque`, `set_option`, `native_decide` or `EuclideanSpace` (rg exit 1,
   meaning no matches). Both files have the copyright, `module`, public imports,
   module docstring and public section. Counts: Clock 204 lines / maximum width 98;
   PhaseBasis 39 lines / maximum width 97.
8. Recursive local import inspection found 35 KAM modules and no provider or frozen
   theorem imports. All 12 imported frozen definitions are manifest `SEALED`:
   complexStrip, IsDiophantine, IsRealOnReals, IsPrimaryOnStrip, invarianceError,
   hamiltonianVectorFieldℂ, omegaZero, torsionAverage, torsion, dotℂ, normalFrame,
   gramMatrix. No DRAFT_SORRY dependency was found.

## Errata, deviations and handoff

No suspected defect in the inspected source statements, frozen definitions or blueprint
interfaces was found. The package moves the signed phase-basis definition into a small
independent module; this is an organizational deviation only, already disclosed in the
handoff, with unchanged namespace, carrier and body.

Only this report and temporary probes in `.lake/abi-scratch/` were written. No generated
root, frozen file, manifest, source module or git state was edited.

Final cleanup: deleted `.lake/abi-scratch/SOClockAudit.lean`. The report is the only
audit-created repository file; the untracked prover handoff was present at entry and
was left unchanged. Final `git diff --check` and protected-path comparison were clean.
