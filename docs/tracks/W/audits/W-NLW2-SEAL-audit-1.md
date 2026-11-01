# W-NLW2-SEAL independent audit 1

Audit date: 2026-11-01. Auditor: maud-wpq-1.

Verdict: **SEAL-READY — PASS for `wave.nlw2.v1` (`KAM.Wave.nlw2`).**
All five seal-focus gates passed. There is no remaining seal blocker in the audited scope.

## Authority and scope

Read `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md`,
`/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and
`docs/tracks/W/audits/W-NLW2-SEAL-handoff.md`. The handoff's five SEAL AUDIT FOCUS
items control this review, replacing generic package focus. D61 approval is supplied
explicitly by the owner prompt and handoff; the checked-in decisions file ends at D51.
This is a seal audit, not a fresh independent re-audit of all previously audited W3–W8 packages.

Worktree: `/root/code/KAM-inp-wpq` (physical path
`/mnt/HC_Volume_106379410/kam-w/KAM-inp-wpq`). Compared `git diff inp...HEAD`:
HEAD `c7dd873bc770a7c8f9493b5150ddb56ca58e490d`, inp
`a43ea7e7964851a8d1e1e983a1b053af6320134a`.
The integration delta has 45 files, including 38 Lean files and the inherited generated
`KAM/Root/Wave.lean` additions. The auditor has not edited generated files.

## Findings by seal item and declaration

| Item / node | Declaration or check | Verdict | Evidence |
|---|---|---|---|
| 1: provider | `KAM.Provider.Wave.nlw2` | PASS | Only source premise is `{m : ℝ} (hm : 0 < m)`; statement identical to anchor; body exactly `KAM.Wave.nlw2_proof hm`; no frozen theorem import. |
| 2 / `bpW:w8:nlw2-proof` | `KAM.Wave.nlw2_proof` | PASS | Frozen type preserved, including all six clauses, witness order and dependence. Only the three standard axioms. |
| `stepW:w8:p-close` | `KAM.Wave.w8_tn_le_two_sum` | PASS | Proves shell bound from shell membership and positive actions, rather than assuming the final closeness estimate. |
| `stepW:w8:p-close` | `KAM.Wave.w8_close_arith` | PASS | Correct exponents 33/64 and 1/32; general nonnegative E, positive t and s, and t ≤ 2s. |
| `stepW:w8:p-size` | `KAM.Wave.w8_size_arith` | PASS | General arithmetic helper with r2 ≤ t ≤ 2s, yielding the required C3 bound; weaker ancillary sign assumptions than needed by the caller. |
| `stepW:w8:p-close`, `p-size` | `KAM.Wave.w8_patchClose` | PASS | Obtains the concrete shell estimates and proves both frozen bounds on Γ. |
| 3: temporary seal | `KAM.Wave.nlw2` | PASS | Unrenamed copy of anchor, exact mandated body; elaborates, with only the three standard axioms. Real anchor remains `by sorry`. |
| 4: quarantine | Import closure | PASS | 447 local KAM modules; no provider or frozen theorem in proof closure, no forbidden construct or option override; only anchor imports provider. |
| 5: frozen surface | Diff, guard, ABI | PASS | Empty protected diff; frozen guard and all 177 core ABI hashes pass; original hashes unchanged. |

The type text of the provider and proof equals the frozen statement after removing comments
and normalizing whitespace (both comparisons true). Lean probes separately check assignment
to `type_of% @KAM.Wave.nlw2` and equality of the full types by `rfl`, including implicit mass.
The only explicit binder supplied by the exact seal body is `hm`.

The assembly agrees with `blueprint-W/parts/w-headline.tex` (`bpW:wh:nlw2`) and
`blueprint-W/parts/w8-assembly.tex:547` onward. It uses r0, C, tau, eta, Γ, ν, K before
I and θ; tau is 24; eta is `2^(33/64) E7 r^(1/32)`. Density, frequency limit,
embedding, exact coefficient dynamics, classical PDE solutions with the shared C, and
family injectivity are retained. No conclusion-shaped premise is added to either export.

## Definition classification and fallback checks

Neither the provider nor `Nlw2Proof` introduces a def, abbrev, structure, or instance.
The eleven frozen wave definitions were read without modification: physical frequencies
and sine modes; positive exponential weights; weighted lp phase space and coefficient
projection; reconstruction sums; cubic force integral; linear torus; analytic embedding;
and classical PDE predicate. Their intended carriers and normalizers are preserved.
The additional frozen definitions in the local closure are `IsDiophantine`, `ComplexStrip`,
and `OmegaZero`; no frozen theorem occurs there.

The assembly's witness definitions are concrete constructions from m and proved upstream
constants, not assumed theorem conclusions. `W8UpstreamConsts` stores numbers and positivity
proofs; `w8Upstream` supplies these from W6 results. Shell constants, radii and eta are explicit
real formulas; Γ is the countable shell union. The selection index uses Nat.find, with a
zero default outside the shell union. `w8ShellIdx_eq` and the patch agreement lemmas prove
it selects the unique appropriate shell on Γ. Patched ν and K are zero off Γ; the frozen
claims concern their restrictions to Γ, so those extensions are harmless.
`w8KOfBirk` has a zero extension outside the Birkhoff chart; `w8Psi_ball` in
`KAM/Wave/Assembly/ShellTorus.lean:324` proves the actual shell torus is inside the chart,
and `w8KOfBirk_of_mem` removes that branch. No on-carrier assertion is paid by a fallback.
The reconstruction sums have absolute-summability suppliers, e.g.
`Recon2/Functionals.lean:254`–270; no divergent-sum default is used for the physical functions.

## Checks and exact commands

All Lean/Lake/checker invocations in this audit ran serially under the owner's exact
scope prefix:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1
```

The specified lint wrapper was itself placed in that scope, so its child ABI Lean invocation
inherits the memory/swap cap, niceness and single-thread environment. No heartbeat,
recursion-depth or synthesis-budget override was used.

For scratch probes and replay, the command following that prefix was:

```sh
lake env sh -c 'LEAN_PATH="$PWD/.lake/build/lib/lean:/root/code/KAM-inp/.lake/build/lib/lean:$LEAN_PATH" exec lean .lake/abi-scratch/SealAudit.lean'
lake env sh -c 'LEAN_PATH="$PWD/.lake/build/lib/lean:/root/code/KAM-inp/.lake/build/lib/lean:$LEAN_PATH" exec leanchecker --verbose KAM.Provider.Wave.Nlw2 KAM.Wave.Assembly.Nlw2Proof'
```

Temporary seal probe: exit 0. Output:

```text
'KAM.Wave.nlw2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Provider.Wave.nlw2' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.nlw2_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The seal copy retained the original namespace and theorem name, replacing only the body
between the proof markers. A scratch-only direct import of `Nlw2Proof` was added to expose
its name to the axiom and equality commands. An initial probe lacked that direct import:
the seal and provider axiom checks succeeded, but the two proof-name queries failed with
`Unknown constant` / `Unknown identifier KAM.Wave.nlw2_proof` because the provider's import
is private. Adding the explicit import fixed those probe queries; the corrected full probe
exited 0. This required no production-code change.

Kernel replay: exit 0, output:

```text
replaying KAM.Wave.Assembly.Nlw2Proof
replaying KAM.Provider.Wave.Nlw2
```

This freshly replays the provider that the launcher omitted because of its short-name
collision. Launcher receipts were not visible and are not claimed as independent evidence.

Actual-anchor identity and helper axiom probe (same scope prefix):

```sh
lake env sh -c 'LEAN_PATH="$PWD/.lake/build/lib/lean:/root/code/KAM-inp/.lake/build/lib/lean:$LEAN_PATH" exec lean .lake/abi-scratch/IdentityAudit.lean'
```

Exit 0. Both assignments and both `rfl` full-type equalities against the imported,
unaltered frozen theorem succeed. Output:

```text
'KAM.Wave.w8_tn_le_two_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w8_close_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w8_size_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.w8_patchClose' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Lint command (the full scope prefix above immediately precedes this command):

```sh
/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpq
```

Exit 0. Complete output:

```text
check_lean_modules: PASS (4053 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

The opt-in lunar anchors are outside this seal audit; the wave anchor is included in the
177 core ABI checks. No expected-root exception was needed.

Targeted build command:

```sh
/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpq KAM.Provider.Wave.Nlw2
```

This driver acquires an inp compile-gate slot and executes exactly:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake build KAM.Provider.Wave.Nlw2
```

Exit 0. Gate output: `[w_build] slot 1: KAM.Provider.Wave.Nlw2 (10:07:51)`.
Final output: `Build completed successfully (3796 jobs).`
The intervening output replays existing upstream deprecation and linter warnings
(e.g. `if_pos` and `ContinuousLinearMap.add_apply`); no error or resource-limit failure.
This was a targeted cached build, not a clean rebuild or an application build.


Static inspection used the repository's comment/string-aware `code_mask`, followed local
imports transitively, and checked every local closure file for sorry/sorryAx, axiom, admit,
unsafe, opaque and budget overrides. Findings: empty. All `set_option` commands in the
local closure: empty. Global local-module scan: provider importers exactly
`KAM/Frozen/Wave/Theorems/Nlw2.lean`; DRAFT_SORRY importers empty.
Maximum local closure file length: 824 lines (`KamStep/StepTheoremSrc.lean`).
Maximum changed Lean file length: 468 lines (`KAM/Root/Wave.lean`).
`git diff --check inp...HEAD`: exit 0, no output.
`git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md`: exit 0, empty.

## Byte scope, limitations, errata and deviations

SHA256 of audited provider:
`e1c75dde39e75e218a35293c60cfc7f78e303098c0ce61bb5ebd76d0c9a1b123`.
SHA256 of audited proof:
`79e0ee1e500dd02455cb9300a641b2531f705a2c064887132638fc9711a0c53f`.
Original anchor SHA256:
`9ce65519e3108c55e50565b268e7138d5a47ed68fbfade07166d0641b2e2dde6`.
Original manifest SHA256:
`8859fe7f8bae7ca904585d0b72a6c23601d848c66febefdc7e5c74adb2300555`.
Both original protected-file hashes were rechecked before handoff.

No suspected mathematical source or blueprint defect found within the seal focus.
No introduced production deviation. Historical status text in `W-STATEMENTS.md` still says
nothing is frozen; the actual frozen files and manifest, plus the explicit D61 owner ruling,
control this audit. The staged seal document's older owner-approval wait is superseded by
that ruling. This report does not itself seal the theorem or update the manifest: those
remain the lander's operation. Scratch probes and audit logs were removed after recording
results; only this report was added to the repository.
