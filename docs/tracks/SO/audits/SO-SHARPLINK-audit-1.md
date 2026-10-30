# SO-SHARPLINK independent package audit 1

Date: 2026-10-30. Worktree: `/root/code/KAM-inp-sosharplink`.
Audited HEAD: `00f0acabbfb81496b10d983a9067fc6143d94bb5`.
Comparison ref `inp`: `de3f2d6e14a88d8f61f8215196da88bfe5c3dc82`;
merge base: `680e9f21546488841aa8db69d2d6c9060c5d63a9`.
Reviewed the full `git diff inp...HEAD`, including the handoff, rather than only the last commit.
The working tree was initially clean.

## Verdict and scope

**PASS WITH NOTES** for SO-SHARPLINK. Kernel replay passed for all three audited modules.
No frozen theorem anchor is supplied or sealed by this package: provider/frozen seal probes are
not applicable. The new public results are an abstract sharp-checker barrier bridge and a
parametric lunar assembly. They do not prove that any particular production data pass the checks.

The only source-lint failure is the explicitly permitted stale generated `KAM.lean`.
The auditor did not regenerate it. There is no substantive statement, proof, hypothesis,
definition, or protected-path finding. Regenerate the root on integration under orchestrator
ownership. D38 and the SO-DION additions postdate this worktree's base; the task-specific brief
supplies the authority for the parametric extension.

Read: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`, the package audit brief at
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, the SO-SHARPLINK prover brief and common
prover rules, `docs/tracks/SO/audits/SO-SHARPLINK-handoff.md` (including AUDIT FOCUS),
`docs/tracks/SO/design/SO-LEAN-DESIGN.md` §6 and §I.5–I.6, and
`docs/campaign/design/SHARP-CERTIFIER-FOR-SO.md`. There is no SO `statement.md` or SO blueprint
part in this checkout; the SO design, task brief, and landed interfaces supply the statements.
The generic I/N/P audit template does not create I/N/P anchor obligations for this SO package.
The relevant frozen strip, primary, real, invariance-error and Diophantine definitions, the
certificate outputs/checks, and the landed barrier/confinement interfaces were inspected.

## Declaration results

All names in this table are in `KAM.SpinOrbit`. PASS means fidelity and proof checks pass;
the package-level note concerns root generation only.

| Node / role | Declaration and locator | Verdict | Reason |
|---|---|---|---|
| Shared graph transfer | `soGraph_exactTorus_of_certified`, `Graph/Cert.lean:163` | PASS | Takes the exact black-box output, static/graph checks and reference Diophantine fact; preserves strip, monotonicity and displacement conclusions. |
| Old static extraction | `checkStatic_of_checkTorusCertificate`, `Graph/Cert.lean:212` | PASS | Projects the first conjunct; no lawful-arithmetic instance needed. |
| Landed graph export | `soGraph_exactTorus`, `Graph/Cert.lean:220` | PASS | Statement bytes equal `inp`; only proof refactored. Copied landed signature elaborates with a direct forwarding body. |
| Original-frame barrier | `soBarrier_of_cert`, `Graph/Cert.lean:240` | PASS | Entire declaration, including proof, byte-identical to `inp`. |
| Shared rotated barrier | `soRotBarrier_of_certified`, `Graph/Cert.lean:260` | PASS | Static facts and CertifiedTorus feed graph transfer and the rotated exact-torus barrier; no old-checker hypothesis or call. |
| Landed rotated export | `soRotBarrier_of_cert`, `Graph/Cert.lean:276` | PASS | Statement bytes equal `inp`; old soundness theorem supplies the shared output. |
| Sharp static extraction | `checkStatic_of_checkTorusCertificateSharp`, `Graph/CertSharp.lean:30` | PASS | Projects the actual sharp check's first conjunct. |
| Sharp rotated barrier | `soRotBarrier_of_certSharp`, `Graph/CertSharp.lean:38` | PASS | Uses `checkTorusCertificateSharp_sound` and sharp static extraction, then the shared bridge. |
| Gamma monotonicity | `isDiophantine_of_le_gamma`, `LunarAssemblySharp.lean:38` | PASS | Correct for all real exponents and constants: the denominator is nonnegative. No unnecessary positivity premise. |
| Certificate Diophantine form | `lunarRotFreq_isDiophantine_params`, `LunarAssemblySharp.lean:45` | PASS | Rewrites tau to 1 and casts the rational gamma comparison; no extra analytic premise. |
| Real band algebra | `soBarriers_of_band`, `LunarAssemblySharp.lean:54` | PASS | Widens both barriers into the common band and proves strict separation through the window. |
| Rational band adapter | `soBarriers_of_band_rat`, `LunarAssemblySharp.lean:76` | PASS | Exact rational-to-real casts of all five inequalities; same conclusion. |
| Sharp lunar assembly | `lunar_barriers_of_sharp`, `LunarAssemblySharp.lean:89` | PASS | All parameters exposed, checks and frequency facts retain their data shapes, and rational inequalities suffice for band assembly. |
| Old-checker parametric twin | `lunar_barriers_of_band`, `LunarAssemblySharp.lean:116` | PASS | Same interface except the old checker; independently calls the old certified-barrier export. |
| General confinement | `lunar_spin_confinement_of_band`, `LunarAssemblySharp.lean:142` | PASS | Global unique physical flow from the landed confinement theorem; band inclusions imply the requested absolute-value bound. |
| Sanity A | `lunar_barriers_of_viaBand`, `LunarAssemblySharp.lean:187` | PASS | Same statement tokens as landed `lunar_barriers_of`; derived through the new old-checker parametric twin. |
| Sanity B | `lunar_spin_confinement_of_viaBand`, `LunarAssemblySharp.lean:212` | PASS | Same statement tokens as landed `lunar_spin_confinement_of`; derived through general band confinement. |

The unchanged public helpers in `Graph/Cert.lean` (`norm_fst_apply_sub_le`,
`norm_snd_apply_sub_le`, `realPt_one_zero`, `soGraph_deriv_transfer`, `checkSoGraph_sound`)
were included in the axiom probe and kernel replay. Six private sanity helpers in
`LunarAssemblySharp.lean:166–183` only establish positive fixed rational constants, casts,
the R1 gamma equality, and the old-frequency Diophantine cast bridge.

## Definitions and statement preservation

There are **no new or modified definitions, abbreviations, structures, instances or macros**.
`SoGraphCert` (`Graph/Cert.lean:42`), `soGraphMonoModel` (:58), `soGraphActionModel` (:63),
and `checkSoGraph` (:69) are byte-identical as complete declarations to `inp`.
They remain respectively the certificate data bundle, derivative model, action model and
Boolean graph check. This change introduces no fallback, junk carrier or changed interpretation.
The inherited `SoBarrier.widen` retains the same graph and invariant-set evidence and only
weakens its numerical bounds; it is the intended operation on its entire carrier.

Python extraction compared each landed graph statement through its declaration's `:=`:
`soGraph_exactTorus`, `soRotBarrier_of_cert`, `soBarrier_of_cert`, `SoGraphCert`, `checkSoGraph`,
`soGraphMonoModel`, `soGraphActionModel`: statement bytes identical to `inp`.
Complete-declaration equality also passed for the four definitions and original-frame barrier.
`LunarAssembly.lean`, `LunarParams.lean`, and `RotFreq.lean` are byte-identical to `inp`.
The sanity statements are token-identical modulo the new theorem names and whitespace
(the wrapping of `lunar_barriers_of` differs); elaborated type equality passes both ways.

The shared bridge gets `rhoInf > 0`, `gamma > 0`, weight and pi-enclosure facts from
`checkStatic_sound`. `CertifiedTorus` supplies `sinf > 1`, holomorphic primary real embedding,
exact invariance and uniform displacement on the same strip. Cauchy transfer gives the
monotonicity loss `disp/rhoInf`, the graph check pays its strict margin, and the action range
loses at most `disp`. Positive scaling of the reference Diophantine vector gives the scaled
frequency's Diophantine condition. Hamiltonian equality then feeds the landed rotated barrier
without an old-checker assumption. Thus `hT` is an explicitly authorized intermediate output,
not a replacement assumption for checker soundness.

## Parametric fidelity and SO-DION compatibility

For `lunar_barriers_of_sharp`, `hhamL/U`, `hparL/U`, `hcL/U`, `hgL/U` and `hωL/U` are the
signed data conclusions in precisely the shapes listed in the handoff. `c`, `κ`, `γdL/U`,
all band/window endpoints, and the two parameter packages are arbitrary. `νL/U` are arbitrary
reals. The only numerical side conditions are rational positivity, tau equality, gamma
inequalities, and the five rational band inequalities. No positivity of κ or γd is silently
assumed; any positivity needed by certificate soundness comes from the passing static check.
No parameter dependence of a hidden constant is enlarged.

The two `hdL/U` assumptions are the authorized external number-theoretic results.
The current landed source `/root/code/KAM-inp/KAM/SpinOrbit/RotFreqN.lean:68–81` states
`lunarRotFreq{Minus,Plus}N_isDiophantine` for `8 ≤ N`, `0 < κ` at constant `κ/(N+2)`.
Choose `γd = 1 / ((N : ℚ) + 2)` and `ν = lunarNu{Minus,Plus}N N`.
A scratch Lean proof verified, for every N and κ,

```lean
example (N : ℕ) (κ : ℚ) :
    (κ : ℝ) * ((1 / ((N : ℚ) + 2) : ℚ) : ℝ) =
      (κ : ℝ) / ((N : ℝ) + 2) := by
  push_cast
  simp only [div_eq_mul_inv, one_mul]
```

This removes the handoff's uncertainty about the constant's carrier. For N=65 the rational
factor is `1/67`. SO-DION is not imported by this branch: this is a source-interface comparison
plus a compiled cast bridge, not a claimed integrated build of the newer inp modules.

The band proof explicitly uses the nonemptiness witnessed by each existing barrier at `(0,0)`
to order its endpoints, then widens the lower/upper bands into `[lo,hi]`.
At each point, `BL.P ≤ bL < pLo < pHi < aU ≤ BU.P`; strict separation is correct.
For confinement, `hB` is the declared intermediate barrier-existence input already produced
by assembly; it does not assume the requested ODE or confinement result. The initial-window
hypothesis starts the solution strictly between the graphs. The landed `so_confinement` gives
a global solution, uniqueness and strict graph bounds for all real time. Together with the
barrier range and `1-δ ≤ lo`, `hi ≤ 1+δ`, these imply `-δ ≤ p(t)-1 ≤ δ`.
No separate δ-positivity premise is needed.

## Independent checks

All Lean operations were serialized with `LEAN_NUM_THREADS=1` and `nice -n 5`.
No resource override, build reset, package change or state-changing git command was used.

1. Targeted gate build (exit 0):

```sh
LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh \
  /root/code/KAM-inp-sosharplink KAM.SpinOrbit.Graph.Cert \
  KAM.SpinOrbit.Graph.CertSharp KAM.SpinOrbit.LunarAssemblySharp
```

The gate invoked `nice -n 5 lake build` and reported slot 1 acquired at 12:37:34 UTC;
`Build completed successfully (3398 jobs).` Only inherited dependency warnings were replayed
(unused variables/arguments and deprecated `if_pos`/`if_neg`); no audited-module warning or sorry.

2. Scratch signature/body/cast/axiom probe (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/SOSharplinkAudit.lean
```

The probe imported `KAM.SpinOrbit.LunarAssemblySharp`, opened `KAM`, `KAM.Certificate`,
`KAM.CertificateSharp`, `SoGraph`, and copied the exact landed signatures under fresh names.
Direct bodies passed all explicit binders in order for the graph, rotated barrier and
original-frame barrier. Both sanity signatures elaborated with the new sanity proofs.
It additionally elaborated both directions of:

```lean
example : type_of% @lunar_barriers_of := @lunar_barriers_of_viaBand
example : type_of% @lunar_barriers_of_viaBand := @lunar_barriers_of
example : type_of% @lunar_spin_confinement_of := @lunar_spin_confinement_of_viaBand
example : type_of% @lunar_spin_confinement_of_viaBand := @lunar_spin_confinement_of
```

Initial scratch-only setup errors (missing `open SoGraph` and a redundant rewrite after
`push_cast`) were corrected; the final complete probe exited 0 without diagnostics other
than the requested axiom output. No production source was changed.

Axiom output for every public theorem in all three audited modules follows.

```text
'KAM.SpinOrbit.norm_fst_apply_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.norm_snd_apply_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.realPt_one_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soGraph_deriv_transfer' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.checkSoGraph_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soGraph_exactTorus_of_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.checkStatic_of_checkTorusCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soGraph_exactTorus' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soBarrier_of_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotBarrier_of_certified' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotBarrier_of_cert' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.checkStatic_of_checkTorusCertificateSharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soRotBarrier_of_certSharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.isDiophantine_of_le_gamma' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunarRotFreq_isDiophantine_params' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soBarriers_of_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.soBarriers_of_band_rat' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunar_barriers_of_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunar_barriers_of_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunar_spin_confinement_of_band' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunar_barriers_of_viaBand' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.SpinOrbit.lunar_spin_confinement_of_viaBand' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All 22 exports report exactly `[propext, Classical.choice, Quot.sound]`; no `sorryAx` or
additional axiom. This includes every new public theorem, both refactored exports and all
unchanged public theorems in `Graph/Cert.lean`.

3. Kernel replay, one invocation (exit 0):

```sh
LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose \
  KAM.SpinOrbit.Graph.Cert KAM.SpinOrbit.Graph.CertSharp KAM.SpinOrbit.LunarAssemblySharp
```

```text
replaying KAM.SpinOrbit.LunarAssemblySharp
replaying KAM.SpinOrbit.Graph.CertSharp
replaying KAM.SpinOrbit.Graph.Cert
```

4. Full source lint (exit 1, solely the allowed generated-root exception):

```sh
LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
```

```text
KAM.lean is out of date; run scripts/gen_root_imports.py
check_lean_modules: PASS (1460 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (146 frozen declarations)
```

This includes the forbidden-token/resource/escape checks, module-system and size checks,
frozen byte guard and elaborated ABI checks. The forbidden code patterns were absent.
The three files contain 285, 46 and 226 lines; their maximum line lengths are 100, 97 and 97.
All have copyright, `module`, public imports, module docstrings and public sections.
The root was never edited, even temporarily.

5. Public short-name check (exit 0):

```sh
python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py \
  /root/code/KAM-inp-sosharplink KAM.SpinOrbit.Graph.Cert \
  KAM.SpinOrbit.Graph.CertSharp KAM.SpinOrbit.LunarAssemblySharp
```

Output: `short-name check OK (no reused public short name)`.

6. Integrity (exit 0 for each):

```sh
git diff --check inp...HEAD
git diff --exit-code inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
```

Both produced no output. An independent source import-closure scan found 231 KAM modules,
24 frozen definition modules (all SEALED in the manifest), no frozen theorem module and no
provider module. In particular there is no DRAFT_SORRY import or hidden provider dependency.
The new files' direct imports are exactly the public imports shown in the handoff.

## Errata, deviations and limits

No suspected pinned-source erratum or blueprint contradiction was found. The SO design's
historical 3.3% literal-band statements are preserved by the landed exports and exact sanity
types; the new parametric declarations are the explicit extension authorized by SO-SHARPLINK.
No mathematical source lookup outside the repository was needed for these composition and
algebra checks. No frozen theorem was changed or newly sealed.

The two old-checker proofs were factored as the task prefers; no landed statement changed.
The sharp checker is not claimed equivalent to the old one, so the separate old-checker
parametric twin is the correct vehicle for the sanity theorem. The final production band,
parameter packages, positive scaling and numerical certificate success remain data obligations.
There was no default-heartbeat design signal. No deviation was introduced by the auditor.

Only this report was written outside `.lake/abi-scratch/`. Audit-created scratch probes,
scripts and logs were removed after incorporating their results here; no production files,
frozen files, manifests or generated files were edited. Final `git diff --check` passed.
