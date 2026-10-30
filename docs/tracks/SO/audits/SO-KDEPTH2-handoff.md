# SO-KDEPTH2: audit request (log-depth jet compiler, owner ruling D39)

Branch `inp-sokdepth2` (off `inp` at `7e8f8c02`). Land the code commit only: the four Lean files below plus this
handoff. The probes in `.drafts/kd2/` are measurements and do not land. Nothing was touched under `KAM/Frozen/`,
`manifest/`, `README.md` or `KAM.lean`/`KAM/Root/*`.

## The deep traversal found
- **Where.** `slpEmit s op = (s ++ [op], some s.length)` (`Expr/DiffBuild.lean`). The node builders also use `s ++ [op]`
  and `s.length` directly (`slpConstNode`, `slpActionNode`, `slpCharNode`, `slpAddNode`, `slpMulNode`, `slpExpNode`,
  `slpInvNode`/`slpInvPre`, `slpSqrtNode`/`slpSqrtPre`).
- **Why it is deep.** Evaluated by the kernel, the program of `slpCompile` is a left-nested chain of appends,
  `((⋯([c] ++ [o₁]) ⋯) ++ [o_N])`, one per operation. `List.append` recurses on its first argument, so to get the
  head of the program (or its `length`, which every new slot reads) the kernel has to go N levels deep. That is a
  recursion of depth O(#ops) with heavy frames.
  - 887 ops (R2) passes.
  - 3,116 ops (lock) fails.
- **Isolating probe** (`.drafts/kd2/D1.lean`): `lockJ.prog.ops.length = 3116` alone fails with *(kernel) deep
  recursion*. So the program spine is enough to trigger it, with no slot arithmetic involved.
- **Not deep.** The derivative tables (`slpMapSt`: lazy cons per entry) and the expression recursion (expression depth
  is only tens) are fine.

## Changes (bodies and helper lemmas only)
- **NEW `KAM/Certificate/Expr/DiffCompile.lean`.** Everything in `Diff.lean` from `slpScaleNode` through
  `slpCompile_sound` is moved here **verbatim** (same names, statements and bodies). This lets the new compiler import
  the specification compiler. `Diff.lean` re-exports it (`public import … DiffBuf`, which imports `DiffCompile`), so
  every former importer still sees the same declarations.
- **NEW `KAM/Certificate/Expr/DiffBuf.lean`: the buffer compiler.**
  - `SlpBuf` holds the operations in reverse order (`rev`) and the length (`len`).
    - `SlpBuf.ofOpList s = ⟨s.reverse, s.length⟩` and `SlpBuf.opList b = b.rev.reverse`.
    - Emitting an op is a cons: `slpEmitB b op = (⟨op :: b.rev, b.len + 1⟩, some b.len)`.
  - Every builder has a twin with suffix `B` and the same structure: `slpAddOB`, `slpMulOB`, `slpScaleOB`,
    `slpMapStB`, `slpPureB`/`slpCAddB`/`slpCMulB`/`slpCScaleB`, `slpTab{1,2,3}B`, `slpFinishB`, the node twins
    (`slpConstNodeB` … `slpSqrtNodeB`, `slpCrossB`, `slpMulD3B`, `slpExpD3B`, `slpInvD3B`, `slpSqrtD3B`, the
    `Tail`/`Pre` twins), and `slpScaleNodeB`, `slpExpScaleNodeB`, `slpCombineB`, `slpPowNodeB`, `slpTrigNodeB`,
    `slpTrigCharB`, `slpDivNodeB`, `slpCompileB`.
  - **Simulation lemmas.** Each twin has a lemma `…B_ofOpList : twin (ofOpList s) … = (ofOpList (old s …).1,
    (old s …).2)`, or `SlpSim old twin` for computations. So the twin returns the same program and the **same slot
    numbers and tables**. The main one is `slpCompileB_ofOpList`; there is also `slpCompileB_opList`.
  - A file-local macro `slp_sim` discharges the combinator cases.
- **`KAM/Certificate/Expr/Diff.lean`.**
  - `HamExpr.jet` keeps its signature. Its body now runs `slpCompileB e ⟨[.const 0 0 0], 1⟩` and reads the program
    as `r.1.opList`.
  - The old body is kept as `HamExpr.jetAppend`.
  - **`HamExpr.jet_eq : e.jet = e.jetAppend`**, for every `e`.
  - `jet_v0`, `jet_d1`, `jet_d2`, `jet_d3`: statements unchanged. Each proof now opens with `rw [HamExpr.jet_eq]`
    and then runs the old proof on `jetAppend`.
- **`KAM/Certificate/Expr/Ball.lean` (`HamExpr.nonvanishingOn_of_balls`) and `KAM/CertificateSharp/Ham/BallsTrig.lean`
  (`nonvanishingOn_of_ballsTrig`).** These used `List.prefix_refl _` for `(slpCompile e [c₀]).1 <+:
  e.jet.prog.ops`, which held because `jet` unfolded directly to `slpCompile`. That proof term is now
  `by rw [HamExpr.jet_eq]; exact List.prefix_refl _`. Statements unchanged.
- **Unchanged.** `slpCompile`, `slpEmit` and every builder of `DiffBuild`/`DiffNode`/`DiffNodeSqrt` keep their
  bodies; they are the specification. No emitter, mirror or certificate format changed: the compiled `ops` list and
  slot indices are identical by `HamExpr.jet_eq`.

### Why the buffer compiler is kernel-friendly
- **Program spine.** `(slpEmitB b op).1` is already a cons, so the kernel never has to evaluate the earlier program
  to reach it. `opList` is `reverse`, which is tail-recursive (O(1) stack per element; it passed at 20k in
  SO-KDEPTH's P0 probe).
- **Slot numbers.** A slot is `b.len`, a `+1` counter, instead of `List.length` of an append chain.
- **Measured.** The probes below pass on the full 3,116- and 3,158-op lock programs.
- **Limit.** The counter is still a lazy `+1` chain. It passes in practice: operands are demanded roughly in program
  order, and the kernel's whnf cache stores counters already evaluated. I did **not** force the counters with a CPS
  driver. If a much larger program (around 10⁴ ops or more) ever demands a far slot cold, that is where to look next.

## Probe table
Each probe ran alone under `flock …/.kernel-probe.lock systemd-run --user --scope -p MemoryMax=10G
-p MemorySwapMax=0`, with `LEAN_NUM_THREADS=1`, in this worktree (`.drafts/kd2/run.sh`, log `.drafts/kd2/probe.log`).
The probe files are the regenerated gate probes from `/mnt/HC_Volume_106379410/kam-data/so-lock/gate/`, all on the bare
3,116-op `lockHamExpr`; W1 and R2 are mine.

| probe | before (inp 7e8f8c02) | after |
|---|---|---|
| D1 `lockJ.prog.ops.length = 3116` | kernel deep recursion (29 s, 3.0 GB) | pass (32 s, 3.1 GB) |
| D2 `lockJ.v0 == 3115` | stuck (deep recursion inside `Nat.beq`) | (subsumed by G1c_v0) |
| G1a `ops.all opOk` | kernel deep recursion (28 s, 3.0 GB) | pass (31 s, 3.1 GB) |
| G1b bridge (`jetBeq lockJ lockJetLit`, all 5 fields) | kernel deep recursion | **pass** (33 s, 3.5 GB) |
| G1c_v0 / d1 / d2 / d3 | stuck / deep recursion | pass (30 s each, 3.1 GB) |
| G1c_prog_0 / 800 / 1600 / 2400 | deep recursion (prog_0) | pass (32 s each, ≤ 3.4 GB) |
| G1lit, G1asm (literal only) | pass | pass |
| W1 wrapped `.mul (.const (3/2)) lockHamExpr`: `length == 3158 && all opOk`; v0/d1/d2/d3 all `< 3158` | – | **pass** (47 s, 3.1 GB) |
| R2 `jetBeq rotE.jet rotE.jetAppend` and `length = 887`, `rotE = soRotHamExprScaled lunarR2TimeScale` | – | **pass** (73 s, 7.7 GB) |

- **G1b.** It compares the compiled jet with the literal bridge (`lockJetLit`, emitted by the Python mirror) and
  passes. So the new compile is identical to the mirror's program on the lock data.
- **R2.** The new and old compilers give the same jet in the kernel, op by op and table by table.
- **Production client.** The wrapped program is what `lockBarrier_of_exact_torus` uses. It compiles to 3,158 ops in
  the kernel; W1 uses κ = 3/2 as a test value.
- **Final code.** G1a, G1b, W1 and R2 were rerun after the final renames (all pass; `probe.log` 20:45–20:48Z).

## Tests, build, lint, axioms
- **Gate builds.** `KAM.Certificate.Expr.DiffBuf`, `KAM.Certificate.Expr.Ball` and `KAM.CertificateSharp.Ham.BallsTrig`
  succeed. A full **`lake build KAM` succeeds (10737 jobs)**. That build includes every `KAM/Certificate/Tests/*`,
  `KAM/CertificateSharp/Tests/*` and `KAM/CertificateSharp/V2/Tests/*` module (they are imported by the root) and all
  `KAM/SpinOrbit/Lock/*` modules.
- **Warnings.** None in my files.
- **`scripts/lint_sources.sh`.**
  - Passes: `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (158)`.
  - `KAM.lean is out of date`: the root has to be regenerated with `scripts/gen_root_imports.py` at landing, for the
    new modules `Expr/DiffBuf` and `Expr/DiffCompile` (rule 10).
- **Shortnames.** `main_shortname_check.py` on DiffBuf, DiffCompile and Diff: no new reused names. The only hit,
  `JetSmoothOn.charFn`, is pre-existing; it was moved verbatim.
- **Formatting.** Lines are at most 100 columns. No heartbeat or recursion-depth options anywhere.
- **`#print axioms`** gives `[propext, Classical.choice, Quot.sound]` for each of:
  - `HamExpr.jet_eq`
  - `slpCompileB_ofOpList`
  - `HamExpr.jet_v0`
  - `HamExpr.jet_d3`
  - `HamExpr.nonvanishingOn_of_balls`
  - `checkTorusCertificate_sound`
  - `checkTorusCertificateSharp_sound`
  - `V2.checkTorusCertificateV2_sound`
  - `SpinOrbit.Lock.lockBarrier_of_certV2`

## Uncertainties, deviations, errata
- The counter remains a lazy `+1` chain; see "Why the buffer compiler is kernel-friendly".
- Deviation: moving the compiler from `Diff.lean` to `DiffCompile.lean` is a file split, with the import path
  preserved.
- No suspected errata in pinned sources.

## AUDIT FOCUS
1. **Statements unchanged.** Every public declaration of `Diff.lean` on `inp` keeps its exact header, whether it now
   lives in `Diff.lean` or was moved verbatim to `DiffCompile.lean`. This covers `slpCompile`, `slpCompile_sound`,
   `HamExpr.jet`, `jet_v0`…`jet_d3`, `slpCompile_prefix` and the node lemmas. `Ball.lean` and `BallsTrig.lean` change
   one proof term each, not their statements. No builder in `DiffBuild`/`DiffNode`/`DiffNodeSqrt` changed.
2. **Value preservation.**
   - `slpCompileB_ofOpList` (same program and same slot tables for every expression and every starting program) and
     `HamExpr.jet_eq`.
   - Check that each `B` twin matches its original op for op, including:
     - the order of emissions inside `slpScaleOB`;
     - `slpInvPreB`/`slpSqrtPreB` (`.inv b.len` refers to the `sqrt` slot);
     - the `if` guards of `slpActionNodeB`/`slpCharNodeB`.
   - The kernel cross-checks: G1b against the mirror literal, and R2 old against new.
3. **Kernel friendliness.** No append chain or `List.length` of a growing program remains on the `HamExpr.jet` path.
   Judge whether the lazy counter chain is acceptable at the lock scale; the probes say yes.
4. **Consumers.** sharp-v2, Lock and `Sound/*` consume `e.jet` only through `jet_v0`…`jet_d3` and the two
   `nonvanishingOn_of_ball*` lemmas, and the full build passes.
