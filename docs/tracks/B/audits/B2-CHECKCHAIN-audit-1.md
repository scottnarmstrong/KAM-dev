# B2-CHECKCHAIN independent audit 1

Verdict: **PASS WITH NOTES** for B2-CHECKCHAIN, including `checkOscChain_sound`.
No blocking defect found. This is an ordinary Track B implementation package: there is
no frozen anchor or provider to seal, and no I/N/P anchor closure is claimed.

## Audited scope and authority

- Worktree: `/root/code/KAM-inp-b2ckchain`.
- HEAD: `7ee915a28d5607d4885e8b75554b0fca0a2b346d`.
- `inp` at comparison: `8e5aa1f4bb9321ad4eee6794427274d6f08bf792`.
- Merge base: `f7c71d50cb9f583c77a9dde89ba7dacd993c1a53`.
- `git diff inp...HEAD` adds only `KAM/EffectiveStability/OscillatorChainCheck.lean`
  (190 lines) and `docs/tracks/B/audits/B2-CHECKCHAIN-handoff.md` (36 lines).
- Lean file SHA-256:
  `94de0ee69202e15a3d734cfb68c71d36bc9302c1d78958fc0c161294e7f8b799`.

Read AGENTS, PLAN, DECISIONS, the supplied package-audit brief, the handoff's AUDIT FOCUS,
the B2-CHECKCHAIN and B1-common briefs, Track B SPEC and FREEZE-PROPOSAL, OD-B7–B10,
program-b-plan §3.1–3.2, and the existing OscillatorCheck and OscillatorChain interfaces,
including Chain/Basic and Chain/Smoke. Relevant frozen definitions of the Hamiltonian
field, symplectic form, and oscillator actions were inspected.

The handoff's Track B focus specializes the generic I/N/P audit template: the concrete
contract is B2-CHECKCHAIN's brief and `oscillatorChain_confinement`, rather than an
unrelated I/N/P blueprint node or frozen theorem. Frozen-provider type equality and
seal-body probes are therefore inapplicable. An independent consumer-conclusion probe
was run instead. The user's explicit worktree-local report destination overrides the
generic brief's main-worktree destination. No production source was edited.

## Declaration review

All names below are in `KAM.EffectiveStability`. Locations refer to
`KAM/EffectiveStability/OscillatorChainCheck.lean`.

| Contract/node | Declaration (line) | Verdict | Reason |
|---|---|---|---|
| Certificate data | `OscChainCert` (27) | PASS | Only polynomials, steps, rationals and rational lists; no proof, flow, instance or conclusion fields. Generated constructor/projections simply expose these data. |
| Per-step checks | `oscStepOKB` (52) | PASS | All eight `OscStepOK` fields checked, with both coordinate derivative majorants over `List.range n`. |
| Step soundness | `oscStepOKB_sound` (61) | PASS | Unpacks the Boolean conjunction and constructs precisely `OscStepOK n s`. |
| Chain check | `oscChainOKB` (69) | PASS | Starts at H, advances with each `s.out`, checks the Lie sum and the terminal `Nact(I)+P`. |
| Chain soundness | `oscChainOKB_sound` (74) | PASS | Structural recursion on the list; uses the explicitly authorized `Or.inr` equality-check branch. |
| Domain check | `oscDomOKB` (83) | PASS | Checks both strict budgets with the displacement of the inner tail at each step. |
| Domain soundness | `oscDomOKB_sound` (89) | PASS | Structural recursion; order-preserving rational casts, including the half-width and tail. |
| Complete checker | `checkOscChain` (102) | PASS | Total data-only Boolean; every static premise is supplied as mapped below. |
| Complete soundness | `checkOscChain_sound` (113) | PASS | Only acceptance and the initial chart-box proof are hypotheses beyond data; full consumer conclusion preserved. |
| Smoke data | `harmonicChainCert` (162) | PASS | Literal one-dimensional harmonic Hamiltonian with two zero generators, exact rational bounds. |
| Kernel smoke | `harmonicChainCert_check` (175) | PASS | `decide +kernel`, independently re-elaborated and kernel-replayed. |
| Smoke dynamics | `harmonicChainCert_zeroDrift` (178) | PASS WITH NOTES | Correct projection of soundness; N1 describes the limited initial region. |

## Complete premise and conclusion comparison

| `oscillatorChain_confinement` premise | Checker/soundness source |
|---|---|
| `hH`, `hN`, `hP` | Three `cartFitsB` checks at line 103 and their soundness theorems. |
| `hA` | `cartActOnly c.Nact` at line 103. |
| `hok` | `oscChainOKB n c.Nact c.P c.steps c.H`, with recursive step soundness. |
| `hδc` | `0 < c.δc` at line 105, cast to ℝ. |
| `hεb`, `hT` | `0 < c.εb`, `0 ≤ c.T` at line 105, cast to ℝ. |
| `rl`, `r`, `hrl` | `rl := c.r`, `r i := (c.r.getD i 0 : ℝ)`; alignment is `rfl`, not an omitted obligation. |
| `hr0` | `0 ≤ c.r.getD i 0` at line 107. |
| `hdom1` | `2 * (c.b.getD i 0 + c.εb) ≤ c.r.getD i 0 ^ 2`, line 107. |
| `hdom` | `oscDomOKB n c.r c.δc c.steps` and its cast soundness. |
| `hη` | `0 ≤ c.η.getD i 0`, line 108. |
| `hdrift` | Lines 109–110: bracket bound on `c.r,c.r`, less than or equal to `η_i - 2*r_i*oscChainBound n c.steps c.H/δc`, all computed in ℚ. |
| `hmargin` | Strict `a_i + T*η_i < b_i`, line 111. |
| `w₀`, `hw₀` | Explicit point and initial chart-action bound, lines 114–115. This is the permitted initial condition. |

The per-step check covers `δ > 0`, `0 ≤ ε ≤ 1/2`, `1 ≤ order`, fitting generator and
output polynomials, and both `cartDq`/`cartDp` bounds at replicated radius `s.ρ`.
The chain's base case checks the last output against `cartAdd (cartActSubst Nact) P`.
The recursive case passes `s.out`, not H or the preceding Q, to the next step.
The rational bound itself updates Q in the same order and uses each step's factorial.
The domain checker uses `oscTail l`, excluding the current and earlier steps, in both
`r_i + tail + δ < ρ` and `r_i + δc + tail + δ/2 < ρ`.

Every coordinate quantifier is `List.range n` converted to `Fin n` using `i.2`.
All vector data use identical `getD i 0` conventions; no offset or coordinate swap was
found. The cast proof transports the rational drift expression by `Rat.cast_le` and
`push_cast`, with `δc > 0` checked separately. It does not replace the bound by a
real-valued or less precise computation.

The complete conclusion retains `T₁ > T`, the physical H-flow through
`oscChainMap c.steps w₀`, uniqueness on every order-connected comparison interval,
the chart-image identity, absolute chart-action drift, and the upper action bound
for all `|t| ≤ T`, including endpoints. Oscillator actions use p second and q first,
as required by SPEC. An independent probe copied the conclusion from the existing
consumer theorem, substituted the certificate data, and supplied
`checkOscChain_sound c hc w₀ hw₀`; it elaborated without additional premises.

## Definition classification

- `OscChainCert`: finite unchecked input data on its whole carrier. Dimension is a
  phantom parameter; fitting and coordinate ranges are checked explicitly.
- `oscStepOKB`: exact rational/finite polynomial decision procedure, no fallback.
- `oscChainOKB`: structurally terminating finite checker. Its empty-chain branch
  checks the terminal polynomial identity, rather than accepting unconditionally.
- `oscDomOKB`: structurally terminating radius-budget decision procedure; `true`
  for an empty chain matches `OscDomOK [] = True`.
- `checkOscChain`: finite conjunction of the required checks; no real-number
  decision, classical choice, analytic oracle or flow computation in its body.
- `harmonicChainCert`: concrete literal input, not a replacement Hamiltonian.

Zero padding is an explicit interpretation of lists, shared by the consumer and
checker, rather than junk inserted on a supposedly excluded carrier. Missing entries
remain subject to the same inequalities. Extra entries are treated exactly as in
the existing polynomial majorants. No list-length premise is silently assumed.
Although the module uses the established `public noncomputable section` style,
ordinary computable aliases for all four Boolean functions compiled outside such a
section, confirming their executable dependency chains.

## Checks and exact receipts

All Lean/Lake-bearing commands below were serialized and run under
`systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1`.
The build additionally uses the mandatory compile gate, which internally adds
`nice -n 5`. The lint's internal ABI Lean invocation inherits the same cap and thread
setting. No heartbeat, recursion or synthesis budget override was used.

1. Targeted build:

   ```text
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-b2ckchain KAM.EffectiveStability.OscillatorChainCheck
   [inp-gate] slot 1 acquired 02:08:36 for KAM.EffectiveStability.OscillatorChainCheck
   Build completed successfully (2993 jobs).
   exit 0
   ```

2. Independent probe (consumer conclusion, computable aliases, kernel smoke, rejection
   cases, and every new public theorem's axioms):

   ```text
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env lean .lake/abi-scratch/B2CheckChainAudit.lean
   exit 0
   type checking 26.7ms
   ```

   The time is the profiler's kernel type-checking entry for the independent harmonic
   acceptance example. Rejection examples proved by `decide +kernel` covered zero
   Cauchy width, zero slack, negative T, negative η, insufficient outer action bound,
   missing radii, equality at the strict action margin, order zero, ε above 1/2,
   and equality at a strict domain boundary. These supplement the general proof;
   they do not replace it. An initial audit-only record-update probe failed to infer
   phantom `n`; adding explicit `(n := 1)` fixed that scratch elaboration issue.

   Exact axiom output:

   ```text
   'KAM.EffectiveStability.oscStepOKB_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.EffectiveStability.oscChainOKB_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.EffectiveStability.oscDomOKB_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.EffectiveStability.checkOscChain_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.EffectiveStability.harmonicChainCert_check' depends on axioms: [propext, Classical.choice, Quot.sound]
   'KAM.EffectiveStability.harmonicChainCert_zeroDrift' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

3. Kernel replay of the single new module, which contains all new lemmas:

   ```text
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 lake env leanchecker --verbose KAM.EffectiveStability.OscillatorChainCheck
   replaying KAM.EffectiveStability.OscillatorChainCheck
   exit 0
   ```

4. Public short names:

   ```text
   python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-b2ckchain KAM.EffectiveStability.OscillatorChainCheck
   short-name check OK (no reused public short name)
   exit 0
   ```

5. Source lint:

   ```text
   systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 nice -n 10 env LEAN_NUM_THREADS=1 sh scripts/lint_sources.sh
   PENDING RECEIPT
   ```

6. Static checks: 190 lines; Python Unicode-character width check returned
   `Widths >100: []`. Copyright, `module`, both `public import`s, module docstring,
   exposed public section and ambient carriers conform. No proof escape, prohibited
   option, `native_decide` or `ofReduceBool` appears in the added code.
   A recursive local-source import inspection found 82 KAM modules, zero providers,
   zero DRAFT_SORRY modules, and zero frozen theorem modules.
   `git diff --check inp...HEAD` exited 0 with no output.
   `git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md` and the separate
   `KAM/Root lakefile.lean` comparison produced no output.

## Notes, uncertainties, errata and deviations

**N1 — Smoke coverage, nonblocking.** Lines 170 and 179 use initial actions ≤ 0.
Since oscillator actions are nonnegative sums of squares, this initial region is
the origin. The requested two-zero-generator smoke checks acceptance, composition
wiring and application of soundness, but does not demonstrate nonzero generators,
nonzero action drift or a positive-volume initial region. The general theorem is
not restricted to this smoke certificate.

**N2 — Scope, nonblocking.** Like its audited consumer, this checker starts at a
chart point `w₀` and bounds actions after `oscChainInv`. It does not supply original
physical-box inclusion, physical-action displacement bounds, a literal HH certificate,
parameter-box quantification, or an exponential-stability theorem. Those broader
plan §3.1 deliverables are not claimed by this package's explicit brief. The allowed
`cartEqCheck` branch is sound; no completeness theorem for all possible certificates
or for the literal-equality `OscLieOK` branch is claimed or needed.

No suspected pinned-source or blueprint defect was found in the audited delta;
there is no source quote to register as an erratum. No source-facing signature was
changed. No default-heartbeat or memory design signal occurred. No repository repair
or state-changing git operation was performed. Audit scratch is removed before handoff.
