# B08 independent package audit 2 — delta

Overall verdict: **PASS WITH NOTES** for B08. Round-1 F1 and F2 are resolved.
`finite_divisor` remains PASS against its pinned signature. No frozen anchor is assigned;
this is infrastructure approval, not sealing or closure of a planetary headline.

Date: 2026-10-28. Audited HEAD / fix: `617beb7ab041f93a1f3a96e12b38d82825fd80a3`.
Compared live `inp`: `ea47150c9881c2fda67e782c455eafeb2f6c0d95`.
Round-1 source: `b3f65914fb00cb86e3c1297fbb81a12b1297b3e8`.
Scope: only `KAM/Planetary/WeakKAM/FiniteDivisor.lean`; the requested report is written
in this worktree, overriding the generic brief's main-worktree destination.

## Authority and comparison

Read AGENTS.md, PLAN, DECISIONS, the package audit brief, B08 handoffs (including
“Round 2 fix”), audit 1, P11B design and its design audits, Track P statement conventions,
the pinned P11B signature, blueprint p11a3 L233–252, and the live authoritative graph
`/root/code/KAM-inp/docs/graph/P/DEPGRAPH.md` L25348–25463. Checked imported chain,
frequency, shell, tail and cutoff definitions and the frozen carriers/collar.

`git diff inp...HEAD` warns:

```text
warning: inp...HEAD: multiple merge bases, using c802e7aa6b770c0ceeb9a0e1f0511e938a53fc23
```

The resulting comparison includes 81 inherited files and 35 added generated-root imports.
Those unrelated packages are outside this audit. The fix's parent comparison changes only
FiniteDivisor.lean (91 insertions, 7 deletions). `git diff b3f65914 HEAD -- KAM/Frozen
manifest KAM.lean README.md` is empty. The generated-root difference in the live
three-dot comparison is inherited: the latest root commit here is `d9183ada`
(“Regenerate KAM.lean (P11C-T2)”), preceding B08. Consequently the brief's literal
empty-root-diff check is **not met by the aggregate branch comparison**; this is recorded
as an inherited hygiene note, not concealed or repaired. Frozen files, manifest and README
have empty three-dot diffs. No new B08 root change occurred.

## Findings and declaration coverage

**F1 resolved.** `fd_tel` L127–186 returns the identity and all four adjacent inequalities:
frequency difference = finite increment sum; norm ≤ finite ell sum ≤ `selectionTail a m`
≤ γ T_m^(-τ-1) ≤ γ |k|₁^(-τ-1), with m literally `selectionModeStage a k`.
This matches graph fd-tel L25387–25389 and blueprint L247. Its `hS` is the explicit source
SC2 premise, not a newly assumed conclusion of telescoping. Summability is the existing
pinned htail input. Chain data, positive radii/amplitudes, T₀≥1, τ≥0, γ>0, nonzero mode,
and m≤ν are standing/source premises. The point assumption b∈K_ν is weaker than the
source b∈K_(ν+1); it suffices for increment bounds and is supplied by retained membership.
The original helper survives as `fd_tel_tail`.

**F2 resolved.** `fd_concl` L244–255 returns both γ/|k|₁^τ ≤ |k·x| and
`selectionD a ν ≤ γ/|k|₁^τ`. With `selectionD = γ T_ν^(-τ)`, this is the literal graph
fd-concl L25443–25445 / blueprint L251 endpoint. The displayed subtraction
2γ/|k|₁^τ − γ/|k|₁^τ equals γ/|k|₁^τ by arithmetic, so the returned endpoint has the
same strength. The vectors x,y are arbitrary complex vectors: specializing to ω_ν(b),
ω_m(b) gives the source conclusion. The tail and 2γ shell-test assumptions are exactly
preceding source-step outputs, not the final divisor inequality. The mode cutoff is
T_ν, while the frequency error correctly uses T_m. The original helper is `fd_concl_gen`.

All names below have prefix `KAM.Planetary.`; all are public theorems.

| Node / role | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| Shell membership | `selectionModeStage_mem_shell` (29) | PASS | Unchanged; ceil-log shell endpoint and strict preceding endpoint. |
| Shell stage bound | `selectionModeStage_le` (57) | PASS | Unchanged; |k|₁≤T_ν implies m≤ν. |
| Nested prefixes | `selection_chain_antitone` (70) | PASS | Unchanged; analytic-chain nesting. |
| Conditional tail helper | `fd_tel_tail` (79) | PASS | Round-1 helper retained with distinct name; arbitrary m≤ν. |
| stepP:p11a:fd-tel | `fd_tel` (127) | PASS | Full identity and inequality chain; F1 closed. |
| stepP:p11a:fd-test | `fd_test` (190) | PASS | Unchanged; literal tested 2γ margin. |
| Conditional subtraction helper | `fd_concl_gen` (204) | PASS | Round-1 generic helper retained under distinct name. |
| stepP:p11a:fd-concl | `fd_concl` (244) | PASS | Divisor and cutoff-wide D_ν endpoints; F2 closed. |
| bpP:p11a:finite-divisor | `finite_divisor` (258) | PASS | Literal pinned signature; same proof modulo helper renames. |

Python compared the entire theorem declaration through the end of its proof against
Round 1: statement equality **True**; whole declaration equality after only
`fd_tel → fd_tel_tail` and `fd_concl → fd_concl_gen` **True**. Header equality against
`/root/code/KAM-inp/.drafts/design/P11BSignatures.lean` L399–411 is **True**, without
whitespace normalization. The helper proof bodies are preserved by the fix diff.

## Proof and definition review

No new def, abbrev, structure, instance, or carrier: all nine declarations are theorems.
Raw objects remain B02's imported definitions. Local aliases are exact aliases.
Ambient types remain Fin n → ℝ / ℂ, Fourier indices Fin n → ℤ, mode length ℓ¹,
frequency norm the Pi max norm. No fallback value is used at an invalid mode/radius.

The new telescope repeats the finite-sum cancellation of the common initial gradient.
For each j∈Ico m ν, nesting supplies b∈K_j; positive t_j puts the same real point in
its analytic collar. The chain's increment bound then gives the ell_j term.
`sum_Ico_eq_sum_range` and an explicit commutation of indices identify the finite sum
with a prefix of the shifted summable nonnegative series. Negative-exponent monotonicity
uses 0<|k|₁≤T_m and τ≥0. At m=ν the finite interval is empty; no future increment occurs.
The unchanged test proof uses hb directly at m=ν and retained recursion for earlier m.
The subtraction helper proves ℓ¹–ℓ∞ duality, bounds one γ error, and subtracts from 2γ.
The new cutoff endpoint uses |k|₁≤T_ν and τ≥0 with positive powers/divisors.

The production parent continues to call the distinctly named helpers. This is harmless:
the requested literal cuts are now separately exported. An independent probe additionally
composes the new `fd_tel`, `fd_test`, and `fd_concl` into the complete pinned
`finite_divisor` type using only its original inputs.

## Validation

All audit Lean/Lake calls were serial, `LEAN_NUM_THREADS=1`, with `nice -n 5`
(the compile wrapper supplies nice). No heartbeat or other budget override was used.

1. Targeted gated build:

   ```sh
   env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-p11b-b08 KAM.Planetary.WeakKAM.FiniteDivisor
   ```

   Exit **0**. After the expected compile-slot wait:

   ```text
   [inp-gate] slot 2 acquired 18:49:58 for KAM.Planetary.WeakKAM.FiniteDivisor
   Build completed successfully (9110 jobs).
   ```

   Replayed dependency warnings only (unused variables/simp arguments and deprecated
   names in Schedule, StripBudget, MaximalStep/FourierCutoffTail, MaximalStep/Parameter
   and Cutoff*); no FiniteDivisor warning.

2. Fresh signature, new-cut composition, and axiom probe:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/B08Audit2.lean
   ```

   Exit **0**. Copied the pinned theorem signature under `audit_B08_signature`, supplied
   `exact finite_divisor d a c ν hc ht hT hτ hγ hs he htail`, and checked
   `example : type_of% @audit_B08_signature := @finite_divisor`.
   A second copy, `audit_B08_new_cuts`, constructs the result from the new named steps:

   ```lean
   intro b hb k hk hkT
   have hm := selectionModeStage_le a hT hk hkT
   have htel := fd_tel hc.toSelectionExtensionChain ht hT hτ hγ hs he hk hm
     (htail _ hm).1 (htail _ hm).2 hb.1
   have hxy := htel.2.1.trans (htel.2.2.1.trans htel.2.2.2.1)
   exact fd_concl a hT hk hγ hτ hkT hxy
     (fd_test hc hm hb (selectionModeStage_mem_shell a hT hk))
   ```

   Exact output:

   ```text
   'KAM.Planetary.selectionModeStage_mem_shell' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selectionModeStage_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.selection_chain_antitone' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.fd_tel_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.fd_tel' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.fd_test' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.fd_concl_gen' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.fd_concl' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.finite_divisor' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.Planetary.audit_B08_new_cuts' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Planetary.WeakKAM.FiniteDivisor
   ```

   Exit **0**. Complete output:

   ```text
   replaying KAM.Planetary.WeakKAM.FiniteDivisor
   ```

4. Repository lint:

   ```sh
   env LEAN_NUM_THREADS=1 nice -n 5 sh scripts/lint_sources.sh
   ```

   Exit **1**, solely the brief's expressly permitted stale generated-root exception.
   Complete output:

   ```text
   KAM.lean is out of date; run scripts/gen_root_imports.py
   check_lean_modules: PASS (831 Lean files, 0 comparator configurations)
   FROZEN-ANCHOR GUARD OK
   ABI HASHES OK (144 frozen declarations)
   ```

   No root regeneration performed; no other lint failure.

5. Static hygiene: **PASS**. Python found **283 physical lines**, maximum **99 characters**,
   no line over 100, and no forbidden token (`sorry`, `admit`, `axiom`, `unsafe`, `opaque`,
   `set_option`, `EuclideanSpace`). The module has the required header, `module`, public
   imports, docstring and public section. For each of the nine names, `rg -l` over all KAM
   sources returns only FiniteDivisor.lean. Every declaration lies in namespace
   KAM.Planetary; there is no root shadow or alternate short-name declaration.

6. Import quarantine: **PASS**. A recursive source-import scan found 64 local KAM modules,
   zero provider modules, zero frozen theorem modules, and 12 frozen definition modules.
   All 12 are manifest-state SEALED: ActionNbhd, ComplexStrip, FrequencyMap,
   HamiltonianVectorField, HamiltonianVectorFieldC, IsDiophantine, IsPrimaryOnStrip,
   IsRealOnReals, OmegaZero, RealHamiltonian, SymplecticForm, Planetary/Phase.
   No DRAFT_SORRY anchor enters the proof.

7. Final workspace/report check: **PASS**. `git diff --check` exits **0**, empty output.
   The new report was separately checked for trailing whitespace and final newline.
   `git status --short` shows only:

   ```text
   ?? docs/tracks/P/audits/B08-audit-2.md
   ```

   Both temporary audit files were removed; no B08Audit2 scratch file remains.

## Notes, errata and limits

No new suspected pinned-source defect or mathematical deviation found. The finite-stage
lemma is labelled “Ours” in the blueprint. The old docstring's “only the final inequality
is public” claim has been removed. The inherited design L325 still describes internal
blocks; the current AUDIT FOCUS requiring literal exports controls this audit.

The only inherited hygiene qualifications are the generated-root comparison above and
the permitted stale-root lint exception recorded above. No inherited package or graph
status is certified by this delta. No frozen anchor/provider type or sealing test applies.
Only this report and temporary `.lake/abi-scratch/B08Audit2*` files were written;
the scratch files are removed after validation. No state-changing git command was used.

Source SHA256: `f58ff137a85c554bf165b653721eeef9c3ecf67cd9ce2435bb787e528dd7c2c7`.
Pinned signature SHA256: `6800132b3e98b3badc215d5cb1cccc6b016e2f14ec976b661519e436cbf39596`.
