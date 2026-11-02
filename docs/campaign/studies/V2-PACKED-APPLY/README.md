# V2-PACKED-APPLY: receipts of the byte-identity test

`scripts/packed/apply_packed.py` regenerated LG00's packed sources from LG00's certificate trees and kamx-packed's
mirrors, through the existing emitters on this branch. It reproduced both reference packages byte for byte, for
both tori. Run on 2026-11-02, 02:51–02:57 UTC, by kamx-pk-cons, with the committed driver. No Lean process ran.

## Results

| layout | config | steps | reference | files compared | different | module lists |
|---|---|---|---|---:|---:|---|
| copy | `lg00_tp_copy.json` | `cert`, `port`, `packed` | `v2-packed-gen-int/.lake/lg00p` | 286 | **0** | equal |
| copy | `lg00_tpp_copy.json` | `cert`, `port`, `packed` | the same | 286 | **0** | equal |
| own | `lg00_tp_own.json` | `packed` | `lg00-release/applications/lg00` | 115 | **0** | equal |
| own | `lg00_tpp_own.json` | `packed` | the same | 115 | **0** | equal |

**The copy layout** (`LG00P.*`): for each torus, the certificate copy (19 modules), the ported chain-free proof (170)
and the packed modules (115). They overlap in 18 shared modules, so each run compares 286 distinct files. The
module lists `modules_<T>.json` and the port's lists `ported_LG00P_<T>.json` are equal as well.
- The port records its emitter's path, `prod_cert_gen` (`v2-packed`'s copy there, this branch's here; the two
  scripts are identical), so the port lists are compared by their `modules` field.

**The own layout** (`LG00.<T>.PK.*` at LG00's own constants, the release's 114 modules per torus, plus the shared
`LG00.PKFormat`). The release's emitter flags `--pk-root`, `--pk-format` are `v2-packed-gen` `59ea55407`,
cherry-picked onto this branch.

`gen_packed`'s own records, `packed_<P>_<T>.json`, are byte-equal to the references' in all four runs. They hold the
claims, the frame edges, the torsion margin, the invariance and energy rows, and the layout widths.

**One expected difference, and how it was resolved.** `<P>.PKFormat` is shared by both tori, but its docstring
names the tree emitted last. The references emitted T′ and then T″. After T′ alone it differed in that one line
(`runs.txt`, first block). After T″ was emitted into the same output, in the reference's order, T′'s comparison
was rerun with `--check-only` and every file was identical. This is the emitter's behaviour, not a regeneration
difference.

## Inputs (read only)

| input | pin |
|---|---|
| LG00's certificate trees `lg00-app/applications/lg00/LG00/{TP,TPP}` | `lg00-app` `d9aa4c509` (the trees are generated, not committed: pinned by `lg00-app`'s SHA-256 manifest) |
| kamx-packed's mirrors `v2-packed/.lake/v2-packed-prod/{tp,tpp}/{low,full}_mirror.pkl` | SHA-256 prefixes: tp low `016f0d195568c033`, tp full `b9a0f61a556c0ee4`, tpp low `c3121c2a7116571a`, tpp full `a7650f5b4e0c2b1e` |
| reference: integration package `v2-packed-gen-int/.lake/lg00p` | `modules_TP.json` `1f1ed5ffef206b0b`, `modules_TPP.json` `33897f2b0e92b0a1`; branch `v2-packed-gen-int` `ea51cb10b` |
| reference: release package `lg00-release/applications/lg00` | `modules_TP.json` `103f2ad74d4c964c`, `modules_TPP.json` `2ec1b2f3bef5b974`; `lg00-release` `593ef55dd` |

- **No cache was reused.** The outputs started empty, so `gen_packed` recomputed the jet-fed torsion chain
  (`compute_j`) from the Low mirror, and `inv_energy` from the Full mirror.
- **Cost.** T′'s three steps took 78 s wall and 76.5 CPU-s; the largest process was 1.29 GB (`runs.txt`). The
  own layout's one step took 75 s. Each
  step ran under `py_capped.sh` (8 GB, after the 20 GB anon wait).
- **Outputs.** `~/kam-data/v2-packed-apply/final/{copy,own}` (scratch; regenerable with the commands below). An
  earlier run with a draft of the driver, which lacked the checks of the jet bridge and of the §5 modules, gave the
  same result.

## Fail-closed checks (`fail_closed.txt`)

Each of these stops before any emitter runs or any file is written:
1. **The magnetic example config** (`mag_pilot.example.json`, names `mag*`): the names differ from the emitters'
   (design §6), and every difference is listed.
2. **A dump without `Final/Wit.lean`:** the missing file is named.
3. **Layout `own` without `pk_root`.**
4. **Step `cert` in layout `own`.**
5. **`--out` pointed at the LG00 release package:** refused, because the directory holds no `apply_<T>.json`.
   Nothing was written there.
6. **Step `extract` onto an existing input** (kamx-packed's `low.json`): refused.
7. **A config whose tree differs from the dump's namespace** (`LG00.TP` against `LG00.TPP`).
8. **A package without a module the assembly imports** (`Final/Static.lean`, design §5).

## Files

- `copy/apply_{TP,TPP}.json`, `own/apply_{TP,TPP}.json`: the commands with their exit codes, the SHA-256 and size of
  every emitted file, and the comparison.
- `copy/logs/`, `own/logs/`: each step's stdout and stderr.
- `runs.txt`: the driver's output.
- `fail_closed.txt`: the fail-closed checks.

## Rerun

```
cd /home/scott/KAM-dev-worktrees/v2-packed-apply
O=/home/scott/kam-data/v2-packed-apply/final; C=scripts/packed/apply   # outputs: new directories
INT=/home/scott/KAM-dev-worktrees/v2-packed-gen-int/.lake/lg00p; REL=/home/scott/KAM-dev-worktrees/lg00-release/applications/lg00
python3 -I scripts/packed/apply_packed.py $C/lg00_tp_copy.json  --out=$O/copy --check=$INT
python3 -I scripts/packed/apply_packed.py $C/lg00_tpp_copy.json --out=$O/copy --check=$INT
python3 -I scripts/packed/apply_packed.py $C/lg00_tp_copy.json  --out=$O/copy --check=$INT --check-only
python3 -I scripts/packed/apply_packed.py $C/lg00_tp_own.json   --out=$O/own --check=$REL
python3 -I scripts/packed/apply_packed.py $C/lg00_tpp_own.json  --out=$O/own --check=$REL
python3 -I scripts/packed/apply_packed.py $C/lg00_tp_own.json   --out=$O/own --check=$REL --check-only
```
