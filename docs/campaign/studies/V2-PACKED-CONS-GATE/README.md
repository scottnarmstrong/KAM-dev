# V2-PACKED-CONS gate receipts (LG00 T′)

The consumers of the packed jet (`checkTorsionJ`, `checkInvarianceJ`, `checkEnergyJ`, the frames' `sup |T|` on the
jet's torsion) decided conjunct by conjunct on LG00 T′'s data, one Lean process per module under a 4 GB cgroup cap
(`scripts/packed/cons_run.sh`), in a scratch Lake package outside the default build.

- `cons_plan.json`: the mirror's figures (Gram, torsion final test, invariance rows, energy, frames) and the
  probes in build order.
- `summary.txt`, `summary.json`: per module user + sys CPU, kernel time (`type checking took`, the largest line of
  the module), sampled cgroup peak, exit code, and the Boolean each probe states (`scripts/packed/cons_gate_sum.py`).
- `costs/<module>.cost`: `/usr/bin/time` and the cgroup sampler; `costs/<module>.prof`: the profiler lines.

**Data.** T′'s certificate (lg00-app `8210d92e`, `applications/lg00/LG00/TP/Data`, read only), copied into the
package as `LG00C.*` by kamx-packed's `prod_cert_gen.py --prefix=LG00C` (no advice, no witnesses). The jet's wanted
nodes are the T′ mirror runs of kamx-packed (`jet_low_gen.py --mirror-only`, `.lake/v2-packed-prod/tp/{low,full}_
mirror.pkl` in its worktree, 2026-11-01 14:44 and 15:14 UTC). The probes are stated at the literal jet `lg00Jet`
(production rewrites `lg00Cert.ham.jet` to it with `lg00Ham_jet`) and at `jetSlots` of a ledger holding only the
wanted nodes (production: the whole chain's ledger, `jetCheck`).

**Reproduce** (generation is untrusted Python, about 5 min and 3 GB with both mirrors):

```
P=.lake/v2-packed-cons/pkg       # lakefile requiring kam from "../../..", lake-manifest from kamx-packed's package
python3 -I <v2-packed>/scripts/packed/prod_cert_gen.py $P --prefix=LG00C
python3 -I scripts/packed/cons_gate_gen.py --low=<low_mirror.pkl> --full=<full_mirror.pkl>
python3 -I scripts/packed/cons_run_plan.py $P .lake/v2-packed-cons/logs/gate --cap=4G   # resumable
python3 -I scripts/packed/cons_gate_sum.py $P .lake/v2-packed-cons/logs/gate
```
