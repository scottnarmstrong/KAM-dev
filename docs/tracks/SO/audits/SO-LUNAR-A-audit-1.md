# SO-LUNAR-A independent audit 1

Date: 2026-10-30 UTC. Worktree: `/root/code/KAM-inp-solunara`.
Audited HEAD: `4b407a958925cacd03806e49577b5597092344ec`.
Observed `inp`: `0319427f9030707d7d39672fb464a2954dfc1afa`.

## Verdict and scope

**PASS WITH NOTES** for `KAM.SpinOrbit.lunar_barriers_of` and
`KAM.SpinOrbit.lunar_spin_confinement_of`: the parametric assembly is sound and matches
its signed interface. No mathematical or proof-integrity blocker was found in this package.
These are conditional infrastructure results, not proofs that production lunar certificates
exist or pass. No frozen SO anchor is supplied or sealed by this package; the eventual
unconditional `lunar_barriers` and `lunar_spin_confinement` still require SO-DATA.

Read AGENTS.md, PLAN.md, DECISIONS.md, the requested package-audit brief, the handoff's
AUDIT FOCUS, the original SO-LUNAR-A implementation brief, the SO design §6, and the
absolute signed file `/root/code/KAM-inp/.drafts/design/SOSignaturesLunar.lean` §I.6.
There is no `docs/tracks/SO/statement.md`; the SO signed design governs this package,
rather than unrelated I/N/P blueprint nodes. The inherited I-G1 conventions and the
consumed frozen Diophantine, strip, reality, periodicity and invariance definitions
were checked against their actual use.

The requested `git diff inp...HEAD` has **two merge bases**:
`38e678b81bcf76876f21f2d1304421d15daa7426` and
`b54c8c61ac30dc01421424799cb95e6dadb58cbc`.
Git warns that it uses the first. That literal comparison contains 808 changed files
and 33,293 diff lines, including inherited cleanup, tests, generated documentation,
namespace moves and integration changes. It was inspected to establish attribution;
this report does not certify all inherited packages as freshly audited.

The package itself is isolated by `git diff 8b2e8376..HEAD`: precisely the new
123-line `KAM/SpinOrbit/LunarAssembly.lean` and the handoff, in commits `de0ba3ba`
and `4b407a95`. The implementation commit also had a transient .drafts handoff.
No package-local frozen, manifest, generated-root or README change exists.

## Declaration / node audit

All names below are in `KAM.SpinOrbit`, unless stated otherwise.

| Node / contract | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| Signed §I.6, line 481 | `soPrecision`, LunarAssembly:33 | PASS | Literal `320`, exactly the signed definition; checked by `rfl`. |
| Signed §I.6, line 484 | `SoBackend`, :36 | PASS | Exact abbreviation `CertFixed soPrecision`; checked against `CertFixed 320` by `rfl`. |
| Band widening, SO design §6 | `SoBarrier.widen`, :39–47 | PASS | Preserves the identical graph, continuity, both periods and physical-flow invariance; only weakens endpoint bounds by transitivity. |
| R1 positivity (private) | `lunarR1Kappa_pos`, :49 | PASS | Closed rational fact proved with `decide +kernel`; no added public premise. |
| Time-scale positivity (private) | `lunarR1TimeScale_pos`, :51 | PASS | Closed rational fact proved with `decide +kernel`. |
| R1 certificate-to-barrier (private) | `lunar_barrier_of_cert`, :54–62 | PASS | Applies landed `soRotBarrier_of_cert`, rewrites parameters, and transports exactly the required Diophantine input. |
| Signed Theorem A, §I.6:527–530 | `lunar_barriers_of`, :65–100 | PASS WITH NOTES | Ten signed certificate facts plus five rational inequalities; conclusion verbatim after endpoint substitution. Certificate data remain an external obligation. |
| Signed Theorem B, §I.6:534–540 | `lunar_spin_confinement_of`, :103–121 | PASS WITH NOTES | Exact signed conclusion, conditional on A's conclusion; global existence, both time directions, bound and equality with every global solution are preserved. |

There are exactly two new public theorems and three public definitions/abbreviations.
No constants have widened dependence. No type carrier or norm was substituted.
The helper B explicitly receives the preceding A result as authorized by the implementation
brief; it does not assume its own confinement conclusion. The certificate checks in A
are signed source premises, not a replacement for the analytic soundness proof.

## Parametric fidelity and one-line applications

The hypotheses at LunarAssembly:66–72 correspond one for one to the signed data theorems:

| Hypotheses | Signed declarations, SOSignaturesLunar.lean |
|---|---|
| `hhamL`, `hhamU` | `lunarLowerCert_ham`, `lunarUpperCert_ham`, lines 491–495 |
| `hparL`, `hparU` | `lunarLowerCert_params`, `lunarUpperCert_params`, lines 497–501 |
| `hcL`, `hcU` | `lunarLowerCert_passes`, `lunarUpperCert_passes`, lines 503–505 |
| `hgL`, `hgU` | `lunarLowerGraph_passes`, `lunarUpperGraph_passes`, lines 507–509 |
| `hωL`, `hωU` | `lunarLowerCert_freq`, `lunarUpperCert_freq`, lines 512–516 |

The correspondence is literal with certificate, error and displacement constants replaced
by variables. Errors occur only in the parameter equalities; no separate positivity,
smallness, graph-existence or analytic hypothesis is imposed. A passing checker supplies
its own required restrictions through existing soundness.

An independent scratch probe mechanically extracted all ten signed data propositions,
substituted variables, and extracted both signed final statements. It proved the first by:

```lean
exact lunar_barriers_of gL gU errL dispL errU dispU pLo pHi
  h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 hbL hbelow hlt habove hbU
```

The second copied the signed initial-state binders and full conclusion and used:

```lean
exact lunar_spin_confinement_of pLo pHi hB q₀ p₀ φ₀ hp
```

Both elaborated at default resource settings. A separate text comparison confirmed
that A's conclusion and B's `hB` are identical modulo whitespace. The probe used neither
`axiom` nor `sorry`, and both probe theorems' axiom lists were clean. Its first run
failed because the auditor omitted `include` for section hypotheses not mentioned in
the conclusion; adding `include` to the scratch probe fixed that test-harness issue.
No production source was changed. No frozen-provider equality/seal-body test applies:
this package introduces no provider and no frozen theorem target. The signed-statement
probes are the applicable interface tests.

## Diophantine and band checks

`RotFreq.lean:67–79` supplies the minus and plus results at precisely
`IsDiophantine ((lunarR1Kappa : ℝ) / 42) 1 (lunarRotFreq ν± lunarR1Kappa)`.
`LunarParams.lean` defines the parameter gamma as the rational `lunarR1Kappa / 42`
and tau as `1`. Rewriting by `hpar`, then `simpa [lunarR1]`, matches the casts and
exponent expected by `soRotBarrier_of_cert` and `checkTorusCertificate_sound`
(`Soundness.lean:62–65`). This conversion was independently elaborated in the probe.
The time scale is the actual R1 value `237/125`, positive by kernel computation.
There is no outgoing frequency assumption or weakened Diophantine constant.

SO-DATA must supply these five rational inequalities, with `dL = lunarLowerDisp`
and `dU = lunarUpperDisp` (the parameter equalities identify the corresponding fields):

1. `967/1000 ≤ lunarLowerCert.pLo - dL`.
2. `lunarLowerCert.pHi + dL < lunarPLo`.
3. `lunarPLo < lunarPHi` (the signed window-order theorem).
4. `lunarPHi < lunarUpperCert.pLo - dU`.
5. `lunarUpperCert.pHi + dU ≤ 1033/1000`.

All five are propositions over rationals, decidable once the finite data are present.
This audit does not assert that any proposed data satisfy them.

For minimality, put `aL = gL.pLo - dL`, `bL = gL.pHi + dL`, and likewise for U.
The actual obtained barriers give `aL ≤ BL.P 0 0 ≤ bL` and
`aU ≤ BU.P 0 0 ≤ bU`, hence `aL ≤ bL` and `aU ≤ bU`.
Consequently `bL < pLo < pHi < aU ≤ bU ≤ 1033/1000`, and
`967/1000 ≤ aL ≤ bL < pLo < pHi < aU`.
Thus the two omitted band facts follow, even strictly. This uses barrier consistency,
as the handoff explicitly says; the five rational inequalities alone without that
consistency would not suffice. An independent Lean probe established both omitted
rational facts from the actual barrier bounds with `exact_mod_cast` and `linarith`.
No extra public premise is needed.

The widening function's graph projection reduces definitionally to `B.P` (`rfl`
probe). Its other fields are copied, except for bound transitivity. It cannot invent
a barrier for an empty original band. B then applies `so_confinement` to initial
strict separation and derives `|p-1| ≤ 33/1000` from the real band endpoints.

## Definition classification and imports

- `soPrecision`: intended closed natural number on its entire carrier, not a fallback.
- `SoBackend`: transparent alias of the existing fixed-point backend at that precision.
- `SoBarrier.widen`: genuine graph-preserving band inclusion for every supplied barrier
  and endpoint proof. No choice, default branch, junk value or restricted-domain claim.

The source import closure contains 172 KAM modules and no provider module. Its 20 frozen
modules are all definition anchors marked `SEALED` in the current manifest; no
`DRAFT_SORRY` theorem is imported. The consumed implementation is
`KAM.Iso.Apost.g1_explicit`, not an assumed frozen theorem. The axiom probes below
also exclude any transitive `sorryAx` dependency of the audited results.

## Independent validation receipts

All Lean/Lake invocations initiated by this auditor were sequential, inherited
`LEAN_NUM_THREADS=1`, and ran at niceness 5. No resource override, clean, cache fetch,
package update or frozen edit was used.

1. Targeted compile gate:

   ```text
   LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-solunara KAM.SpinOrbit.LunarAssembly
   [inp-gate] slot 1 acquired 00:54:01 for KAM.SpinOrbit.LunarAssembly
   Build completed successfully (3333 jobs).
   exit 0
   ```

   The gate itself runs `nice -n 5 lake build`. Replayed dependency warnings occurred
   in ODE/Exit:36, Certificate/Expr/Basic:85, Arith/PiHigh:218,
   Sound/Static:99,152, and Sound/Ham:68 (unused variables or simp argument).
   No LunarAssembly warning or heartbeat failure occurred.

2. Kernel replay, one invocation for the only new Lean module:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.SpinOrbit.LunarAssembly
   replaying KAM.SpinOrbit.LunarAssembly
   exit 0
   ```

3. Signed-interface, cast, minimality and axiom probe:

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SO_LUNAR_A_audit_1.lean
   'KAM.SpinOrbit.lunar_barriers_of' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.SpinOrbit.lunar_spin_confinement_of' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.SpinOrbit.SoBarrier.widen' depends on axioms: [propext, Classical.choice, Quot.sound]
   'AuditSoLunarA.signedA' depends on axioms: [propext, Classical.choice, Quot.sound]
   'AuditSoLunarA.signedB' depends on axioms: [propext, Classical.choice, Quot.sound]
   exit 0
   ```

4. Full lint (including the single sequential ABI Lean process):

   ```text
   LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (1384 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   exit 1 (only the explicitly permitted stale generated root)
   ```

5. Names:

   ```text
   python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py . KAM.SpinOrbit.LunarAssembly
   short-name check OK (no reused public short name)
   exit 0
   ```

6. Static source checks: 123 lines, maximum 99 columns; copyright, `module`, public
   imports, module docstring and exposed public section present. No forbidden escape,
   resource override or banned ambient carrier. The handoff's initial “129 lines” is
   a harmless stale count; the actual file is 123 lines.

7. Protected paths and whitespace:

   ```text
   git diff inp...HEAD -- KAM/Frozen manifest
   [empty; only the multiple-merge-base warning]
   git diff inp...HEAD --numstat -- KAM.lean README.md
   15  0   KAM.lean
   141 135 README.md
   git diff 8b2e8376..HEAD -- KAM/Frozen manifest KAM.lean README.md
   [empty]
   git diff --check inp...HEAD -- KAM/SpinOrbit/LunarAssembly.lean docs/tracks/SO/audits/SO-LUNAR-A-handoff.md
   [no whitespace errors; exit 0]
   ```

   The literal whole-branch protected-path emptiness requirement is **not met** for
   the two generated files. These changes predate both package commits; this is a
   baseline/integration note, not an undisclosed package-local edit. In a direct
   `git diff inp HEAD`, README is identical and KAM.lean lacks eight newer test imports.
   The stale-root lint exception is explicitly permitted by the audit brief; no generated
   file was repaired. Frozen and manifest integrity remain independently checked.

## Errata, deviations, limitations and handoff

No suspected pinned-source or blueprint mathematical defect was found in the audited
assembly. The slight handoff line-count discrepancy is documented above. The explicit
conditional form is the requested scope, not a substitute for the final data theorem.
The source remains unmodified. The only repository output is this report, at the exact
absolute path requested by the user, overriding the generic brief's main-worktree default.
Scratch probes were removed after validation. No commit, checkout, reset or other
state-changing git operation was performed.

SO-DATA should import the already defined backend names rather than redeclare them.
Final statement freezing, production data generation and all passing-data proofs remain
outside this audit. The successful checks establish readiness of this parametric assembly
for that subsequent integration, not unconditional lunar confinement.
