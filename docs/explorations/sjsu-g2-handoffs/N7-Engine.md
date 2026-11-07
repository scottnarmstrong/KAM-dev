# N7-Engine: the production kernel checker and the SJSU ledger (worker g2-n3)

Status: DRAFT (updated as the ledger runs land). Part 1 (`e13f151d4`) and part 2 (`c457b1484`) are committed and
under audit; this handoff covers parts 3 (the bracket stage) and the ledger.

## Files

Core (`KAM/EffectiveStability/Tube/Engine/`, namespace `KAM.EffectiveStability.Tube`):

| file | content |
|---|---|
| `Deriv.lean` | packed angle derivative `derivZ` (masked column/row parts), `packSum_dlist` |
| `DOpd.lean` | `colsOk_dlist`, `symOk_dlist`, `mx_dlist`, `symOk_of_getD`, `l1_le_of_mx`; `LitD.dopd` (+ `dwf`, `dmx`, `dsym`, `dopd_eval`); `SpD.deriv` (+ `ok_deriv`, `list_deriv`, `deriv_eval`) |
| `Regroup.lean` | `brList` (the terms of one monomial, kernel-cheap), `sum_filter_mon` (N9's filtered bracket sum = sum over `brList`), `mon_eq_iff`, list-sum lemmas |
| `LitCert.lean` | `fCheck`/`fCheck_sound` (a literal copy of a sparse model), `dCheck`/`dCheck_sound` (a derivative literal) |
| `Bracket.lean` | `BrD` (literal data), `BrD.Ok` (certificates), `brCheckL`/`brl_sound` (exact sum of products, packed `ℓ¹`), `brCheck`, `brAll_sound`, `monsUpTo`, `all_of_chunks`, `BrD.ok_of` |
| `Drop.lean` | (g2-n6, N10) `dropCheck`/`dropCheck_sound` |
| `BrChunk.lean` | (part 4) `chunk`, `sum_chunks`, `brCheckC` (one chunk of `m` terms of `brList`), `brChunks_sound`, `BrPOk`, `brAllC_sound` |

Generated (opt-in library `KAMSJSU`): `KAM/EffectiveStability/SJSU/Ledger/H/*` (the Horner-stage ledger),
`KAM/EffectiveStability/SJSU/Ledger/Br/*` (the bracket stage). Small test copies: `Ledger/Small/*`.
Producer: `scripts/sjsu/ledger/{produce,ledger,emit_h,br,bracket,poly,packing}.py`; manifests `manifest-{H,br}.json`.
Build driver: `scripts/sjsu/ledger/build_ledger.py` (part 4); ordered module list `scripts/sjsu/ledger/kamsjsu-modules.txt`.

## The results consumed downstream

- `KAM.EffectiveStability.SJSU.Ledger.Br.Main`:
  - `sjsu_G_bound (j : Fin 3) : ∀ p ∈ truncSet (Fin 3) 8, ∀ φ, |Σ_{mon b = p} coef b · val b φ| ≤ sjsuG j p`
    (N9's `hG`, lambdas `μ = fun e => monOf e.1`, `ν = monOf`, `g = fun e => (e.2.opd Fprm.w Fprm.S).eval Fprm.S`,
    `k = fun t => ((sjsuHD.H t).opd sjsuHD.P).eval sjsuHD.P.S`);
  - `sjsu_drop_bound (j : Fin 3) (hu : ∀ l, |u l| ≤ ((2/1000000 : ℚ) : ℝ)) φ : |Σ_{8 < |mon b|} …| ≤ sjsuDrop j`.
- `KAM.EffectiveStability.SJSU.Ledger.H.Main`: `sjsu_hcerts` (the `h` literals with their C¹ errors `Hc`).

## Part 4 (worker g2-n7b, from 21:25 UTC)

- **`Engine/BrChunk.lean`** (committed `4841de213`, 111 lines): a kept coefficient `G_{j,p}` is checked in chunks of
  `m = 100` consecutive terms of `brList` (`brCheckC`, one declaration per chunk, generated `Br/P<k>`); `sum_chunks`
  splits the exact sum, the triangle inequality is applied only across chunks (`brChunks_sound`), and
  `brAllC_sound` assembles every `p` with `mdeg p ≤ L` from `BrPOk` (length bound, chunk checks, `Σ Gc ≤ G`).
  Loss: a factor 2–3 of the cancellation (per chunk of ~100 terms), not ten orders. Hypotheses: only the
  certificate data (`D.Ok`, `Hl.Nodup`, `inH` ↔ membership) and decidable checks.
- **Producer** committed with it (`br.py` docstring corrected: chunks, not one sum). Its inputs
  `.drafts/g2/data/{F-v1,literal-v1}.json` are untracked (as for the committed `fobs.py`): an audit note.
- **H re-emission (data fix).** The 20:40 emission of `Ledger/H` split `by decide` / `+kernel` across a line break
  in `Check0,2,3,4` and `Asm0` (a parse error: "maximum recursion depth has been reached"; found by building
  `H.Check0–2`). The committed `emit_h.py` already keeps `decide +kernel` together, so `Ledger/H` was re-emitted
  with it (`LEDGER_NOMIRROR=1 python3 scripts/sjsu/ledger/emit_h.py`, 25 s, 2094 modules). 478 files changed;
  all differ from the 20:40 files **only in whitespace** (checked: equal after collapsing whitespace runs, same
  file set); `manifest-H.json` rewritten. `br.py --emit-only` re-emits `Ledger/Br` byte-identically
  (`manifest-br.json` unchanged). So the generated data are exactly the committed producer's output.
- **Assembly design signals (H.Asm0, H.Asm1, H.Main; first production attempts, 7 Nov 01:30–01:45).** No
  heartbeat or recursion overrides; all three fixed in `emit_h.py`, only the assembly modules re-emitted (the
  652 `Check`, the `Lit` and table modules byte-identical, not rebuilt):
  1. `tin`: `rw [show sjsuHD.ns = [..] ++ … (≈650 chunks)]` hit the default heartbeats in `synthesize pending
     MVars` (`++` is `HAppend`: no expected type reaches the literals, every numeral stays pending). Each
     chunk is now ascribed `([..] : List (Nat × Nat × Nat))`.
  2. The following `simp only [List.all_append, tin_k…]` hit the maximum recursion depth on the left-nested
     ≈650-deep chain: the chunks are now joined as a balanced `++` tree (depth ≈10). Asm0 then exceeded
     its share, so the assembly has a new `Asm3` (40 lines; `Asm0–2` ≤ 1239 lines), imported by `Main`.
  3. `Asm1`: a wrapped `rw [show … from by decide +kernel] at` / `hn2` failed `checkColGt` (a hypothesis
     alone on a continuation line). `wrap_expr` now never breaks inside `decide +kernel]` or `at <h>`.
  4. `H.Main`'s `sjsu_allH`: `simp only [sjsuMons, List.all_cons, …]` over the 220-element list hit the
     maximum recursion depth: `sjsuMons` is now rewritten (`decide +kernel`) as a balanced tree of
     ascribed 8-element chunks before the simp.
  `H.Asm0` 18 s, `Asm1` 41 s, `Asm2` 46 s, `Asm3` 2.3 s, `H.Main` 3.9 s on g2heavy (peak RSS ≤ 2.4 GB).
- **Br stage memory (design signal: kernel memory accumulates within a module).** Measured under the 10 GB
  cap (`lake env lean`): one certificate declaration 5.3 GB, ten 7.9 GB, i.e. about +0.3 GB per declaration
  over an import baseline of about 4.8 GB (a module build has about 1.9 GB less baseline). The first emission's
  `Br.Cert0` (142 declarations, cut at 600 lines) was OOM-killed at the cap: `br.py` now emits one certificate
  declaration per module (`BR_CERT_PER`, default 1; 157 `Cert` modules, declarations unchanged, checked by digest).
  `Br.Drop0` (one `dropCheck` declaration over all 87 entries of `Ftab 0`) was OOM-killed too: new core file
  `Engine/DropChunk.lean` (`dropSum_append`, `dropCheckC`, `dropCheck_of_chunks`; committed and audited
  separately by kam-g2) and `br.py`'s `drop_chunks` (exact per-chunk sums in `Ftab` order, chunk claims rounded
  up to 64-bit dyadics, asserted `Σ claims ≤ sjsuDrop j`, so `Prm` and the P modules are unchanged):
  `DropD` (`brDc`), 70 `DropC<j>_<k>` (4 entries each; an 8-entry chunk peaked at 7.9 GB in scratch) and
  `Drop<j>` proving the same `brdrop_j`. Finally `Br.Main`'s list-length facts (`brH_len`, `brF_len_j`) and the
  length argument of `dropCheck_of_chunks` use `decide +kernel` (the elaborator's `decide` on the 220-element
  `sjsuMons` hit the maximum recursion depth).
- **Worst chunk** `Br.P497` (`j = 1`, `p = (3,2,3)`, `k = 0`) on the heavy lane (`g2heavy`): the module 16 s,
  call wall 48 s (with a `Prm` rebuild, 11 s), **peak RSS 5.98 GB** (budget 7.4 GB), rc 0.
- **Build driver (design signal: the D51 driver does not scale to 4.4k modules).** `prebuild_heavy.py --lib KAMSJSU`
  re-runs `lake build --no-build` over the whole library (4447 modules: 120 s) before each one-module build:
  ≈ 150 h of stale checks. Ruling (kam-g2/kam-18): own driver `build_ledger.py`: the import DAG of the
  Ledger closure (4266 modules; no non-ledger KAMSJSU module in it) in DFS post-order, batches of 100, each batch
  re-checked by `lake build --no-build` and skipped if up to date, else one `lake build --fail-fast <batch>`
  under `flock .kernel-probe.lock`, `flock .drafts/g2/lake.lock`, MemAvailable ≥ 12 GB, a scope with
  `MemoryMax=10G`, `MemorySwapMax=0`, nice 5, `LEAN_NUM_THREADS=1`. Test: one such call with three ready modules
  never ran more than one `lean` process, so batches are serial. One log line per module (UTC, module, status,
  wall, VmHWM peak RSS, rc). Launched 21:39 UTC as `kamsjsu-ledger.service`.
- **N9 hookup.** `Br.Main` exports `sjsu_G_bound j` (N9's `hG`, with `G p = sjsuG j (p 0, p 1, p 2)`) and
  `sjsu_drop_bound j (hu : ∀ l, |u l| ≤ ((2/1000000 : ℚ) : ℝ))`; n5b's draft `Eta.lean` passes
  `hu' : |u l| ≤ ((sjsuTailR : ℚ) : ℝ)`, which unfolds (`sjsuTailR := 2 / 1000000`, exposed in `TailAcc`). To be
  type-checked against the built `Br.Main`.

## Approach and design signals

1. **Cancellation.** `KEPT = Σ_p r^|p| G_p` is `(6.48, 2.77, 7.14)·10⁻²⁰` when each `G_{j,p}` is computed exactly; any
   triangle split loses about ten orders (per term `1.2·10⁻¹⁰`, per literal operand `1.16·10⁻¹⁰`, per `h`-monomial
   `4.2·10⁻¹¹`). Every kept coefficient is therefore one exact sum (≈130 products) in one declaration.
2. **Kernel memory (design signal).** The kernel's whnf cache keeps every intermediate value, so memory grows with the
   work of a declaration. Measured at full size (`w = 256`, 15401 slots): a literal expansion ≈ 24 MB, a `derivZ`
   ≈ 135 MB, a sparse-model packing ≈ 26 MB and 0.25 s (symbolic list work). Hence: all operands are literals
   (certified copies of the 277 sparse `F` models, 554 `F` derivative literals, 440 `h` derivative literals, each
   certified once at a narrow width), one kept coefficient per module, built on the 10 GB / one-thread heavy lane.
3. Earlier signals (parts 1–2): heartbeat timeouts in big list literals (chunk definitions), deep recursion in linear
   sums (balanced tree sums), per-digit expansion cost (parallel spread).

## Checks

Production build (`kamsjsu-ledger.service`, driver `build_ledger.py`, 7 Nov 01:38–05:42 UTC after the fixes above;
H checks 6 Nov 21:41–7 Nov 01:30; final `Br.Main` on g2heavy). Per family (lake's wall per module; peak = the
lean process's VmHWM, which includes mmapped olean pages and so exceeds the cgroup's anonymous memory: no module
was OOM-killed after the fixes):

| family | built | wall total | mean | peak VmHWM |
|---|---|---|---|---|
| H.Check | 650 (+2 earlier) | 3.65 h | 20.2 s | 11.3 GB (Check231; anon < 10 GB cap) |
| H.Asm0–3, H.Main | 5 | 1.5 min | | ≤ 2.4 GB |
| Br.Cert | 157 | 0.24 h | 5.6 s | 4.7 GB |
| Br.DropC / DropD / Drop | 70 / 1 / 3 | 0.40 h | 21.5 s | 4.5 GB |
| Br.P | 875 | 2.51 h | 10.4 s | 6.2 GB (P869) |
| Br.Q, Ps, Main | 4 / 1 / 1 | 6 min | | 3.3 GB |

Total built-module wall about 6.9 h (the 1271 + 1318 literal modules were built earlier). Ledger source:
`Ledger/H` 156 MB (2095 modules), `Ledger/Br` 119 MB (2386 modules), `Ledger/F` 1 MB.

Axioms (`#print axioms`, `.drafts/g2/g2lake env lean`): `sjsu_G_bound`, `sjsu_drop_bound`, `sjsu_hcerts`,
`sjsu_hIdx_ne`, `brAllC_sound`, `brChunks_sound`, `dropCheck_of_chunks`: `[propext, Classical.choice, Quot.sound]`.
`sjsu_drop_bound j : (∀ l, |u l| ≤ ↑(2 / 1000000)) → ∀ φ, |Σ_{8 < mdeg} …| ≤ ↑(sjsuDrop ↑j)`.

## Deviations and process notes

- Two kill mistakes, both affecting only my own shell: an earlier `pkill -f "bracket.py"` and a kill loop over
  `ps | grep` PIDs that matched my own shell. Rule: kill only by exact recorded PID.
- The full H emission skips the Python mirror (`LEDGER_NOMIRROR=1`): the mirror re-checks every product in pure Python
  and did not finish in 90 min; the kernel is the check.
- `SpD.Z` (part 1) is not used by the bracket stage (the sparse packing is too expensive in the kernel); the frozen F
  data enter only through the `fCheck` certificates.

## Errata

None found in the pinned sources.
