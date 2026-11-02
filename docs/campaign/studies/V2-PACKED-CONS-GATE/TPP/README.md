# V2-PACKED-CONS gate receipts: LG00 T″

The same consumer gate as `../README.md` (T′), on LG00 T″'s data: every consumer-side conjunct of `checkTorsionJ`,
`checkInvarianceJ`, `checkEnergyJ` and the frames' `sup |T| ≤ 116` (T″'s claim) decided in its own process,
one Lean process at a time under a 4 GB cgroup cap, after the 20 GB anon wait. The files have the same format as
T′'s: `summary.txt`, `summary.json`, `cons_plan.json` (the mirror's figures and the probes) and `costs/`.

**Caveats (as T′).**
- The jet nodes are an untrusted Python mirror's output.
- The jet chain conjunct inside `jetLowOk`/`jetFullOk` (`jetCheck`) is not decided here; that is kamx-packed's chain
  theorem. Only the box and scale guards of those conjuncts are probed.
- The probes are stated at the literal jet `lg00Jet` and at a ledger holding only the wanted nodes.

**Data, pinned by content** (lg00-app's `applications/lg00/LG00/TPP/Data` is untracked there until its run
passes, so no commit pins it). The sha256 of the sources copied into the package (`LG00D.*`):

```
2d50ab2f831d7d2594a4e9ba7252c5a6742c2a20ba221820cee78a294228b71d  TPP/Data/Cert.lean
4dcc6f8614282630d3cc4c2ea8f6117ed17e4b491ffb743ff3f6af33fbb73985  TPP/Data/DCoeffs.lean
0193e4d2fbca923dddff0aaaa6d1cce30434c92149abe1b8a00db2c15557b69a  TPP/Data/E0.lean
fd68e70730942763249447246ccb2c4626648fbaee57b8c186722781e53c873c  TPP/Data/W8.lean
b61d71067b4ee73a2e888400c18d07b8ee53988bc01440450cefca178c4ac042  TPP/Final/Wit.lean
2a7c714f474f6eb662bceacd2fc03925d5fa30cac89b6fa959f3bfc12351557a  Jet.lean
a6fd427b0d8b57c98cd73baf19a341aef14fccdca4f397050f29ce5168c07b84  gen_tpp_L18/state.pkl (T″'s generator state)
```

**The jet nodes** come from T″'s generator state (`gen_tpp_L18/state.pkl`, torus `tpp_estar_N512`, the run
notes' `$SCRATCH`):
- extracted by the landed `scripts/packed/jet_extract_low.py STATE OUT.json <lg00-app> --stage=Low|Full`;
- mirrored by kamx-packed's `jet_low_gen.py OUT.json --stage=Low|Full --mirror-only --cache=PKL` (`v2-packed-prod`
  `0d5f39d9`), the same computation as the landed script, without the probe emission.

**Reproduce.** The T″ scripts are the committed `cons_gate_gen.py`, `cons_run_plan.py` and `cons_gate_sum.py` with
the tree `TP` replaced by `TPP`, and `HERE` set to the worktree's `scripts/packed`:

```
sed -e 's/%s\.TP\b/%s.TPP/g' -e 's/"\.TP\.Cons/".TPP.Cons/g' -e 's/PRE, "TP", "Cons"/PRE, "TPP", "Cons"/' \
    -e 's/opt("tree", "TP")/opt("tree", "TPP")/' -e 's/T′/T″/g' -e 's/"TP\.Data\./"TPP.Data./g' \
    -e 's|^HERE = .*|HERE = "<worktree>/scripts/packed"|' \
    -e 's|"v2-packed-cons", "pkg")|"v2-packed-cons", "pkg-tpp")|' scripts/packed/<script>.py > <script>_tpp.py
P=.lake/v2-packed-cons/pkg-tpp     # lakefile as T′'s, prefix LG00D
python3 -I <v2-packed>/scripts/packed/prod_cert_gen.py $P --prefix=LG00D --tree=TPP
python3 -I cons_gate_gen_tpp.py --low=<low_mirror.pkl> --full=<full_mirror.pkl> --prefix=LG00D
python3 -I cons_run_plan_tpp.py $P <logs> --cap=4G
python3 -I cons_gate_sum_tpp.py $P <logs>
```
(In `cons_gate_sum_tpp.py` the import of `cons_run_plan` becomes `cons_run_plan_tpp`.)
