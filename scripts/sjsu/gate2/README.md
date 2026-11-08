# SJSU gate 2: near-torus approximate integrals (floating)

This folder holds the producer and the measurement code behind
[docs/explorations/sjsu-near-torus-gate.md](../../../docs/explorations/sjsu-near-torus-gate.md).
They run on the full degree-18 dataset [`applications/sjsu`](../../../applications/sjsu/README.md).

Everything here is float64 and measured, not a certificate. The majorants are floating sums of
floating Fourier coefficients, and no rounding is enclosed.

## Files

`poly.py` and `run_nf.py` use only the standard library. Every other script needs Python 3 with
NumPy; NumPy 2.0.2 under Python 3.9 was used.

| File | What it does |
|---|---|
| `poly.py` | Sparse complex polynomials in (w, w̄), with Poisson bracket, Lie series and majorants (`{w_j, w̄_j} = -i`) |
| `run_nf.py` | Baseline: Birkhoff normal form about the origin through degree K, on the full model. Polydisk geometry of the scout's eq. (4) |
| `ft.py` | Fourier–Taylor engine in action deviations p and the invariant angles (φ₁, φ₂) = (q₁−q₃, q₂−q₃): bracket, Lie series, homological equation, binomial expansion of the modal polynomial |
| `common.py` | Modal diagonalization, nominal point, polar coordinates |
| `test_ft.py` | Checks `ft.py` against `poly.py`: H and three brackets at the nominal point |
| `orbit.py` | RK4 integration of the original field and frequency analysis of the modal coordinates |
| `torus.py` | Stage 1: expansion about constant reference actions, Kolmogorov steps (frequency free), Birkhoff steps, pullback, recentring and the torus graph |
| `torus2.py` | Stage 2: Lagrangian projection of the stage-1 torus (c₀ + ∇S), exact binomial re-expansion of H about B₀(φ), renormalization, pullback, stage-2 torus, then the tube measurement |
| `measure.py` | Tube measurement: truncated bracket-series majorants, dropped products, H tails beyond the truncation degree, and the tube-inclusion margin |
| `verify_flow.py` | Checks the stage-2 integrals F_j along the true degree-18 flow (optional off-torus start) |
| `ecc.py` | Eccentricity ranges over the torus and over the tube |

## Reproduce

Run from the repository root.

- By default everything runs in one process with one thread.
- `FT_THREADS=6 FT_PULL_PROCS=3` speeds it up about 3× (the measured runs used this). Expect
  roughly 12 minutes with it, longer without.
- Memory: `torus2.py` processes the observables one at a time.
  - With `--L 8 --Lv 12 --G2 128` it peaked at 3.8 GB RSS (measured).
  - `--L 10 --Lv 14` needs more (estimated 5–6 GB, not measured), so use a smaller `--G2` on a
    shared machine.
- On a shared machine, prefix the commands with `OMP_NUM_THREADS=1 nice -n 10`.

```sh
D=scripts/sjsu/gate2
python3 $D/test_ft.py
for K in 2 4 6 8; do python3 $D/run_nf.py --K $K; done
python3 $D/orbit.py 4e6 200
python3 $D/torus.py --L 6 --K 30 --LB 3 --kol 5 --recenter 1 --G2 64 --tag test
python3 $D/torus2.py --stage1 test --L 10 --K 50 --LB 8 --kol 4 --G2 128 --Lv 14 --tag t2-L10-K50-LB8-v14
python3 $D/torus2.py --stage1 test --L 10 --K 40 --LB 8 --kol 4 --G2 128 --Lv 14 --tag t2-L10-K40-LB8-v14
python3 $D/torus2.py --stage1 test --L 8 --K 50 --LB 6 --kol 4 --G2 128 --Lv 12 --tag t2-L8-K50-LB6-v12
python3 $D/torus2.py --stage1 test --L 8 --K 50 --LB 6 --kol 4 --G2 128 --Lv 12 --prune 0,1e-30,1e-27,1e-24,1e-21 --tag prune-L8-K50-LB6-v12
python3 $D/torus2.py --stage1 test --L 8 --K 50 --LB 6 --kol 4 --G2 128 --Lv 12 --prune 1e-19,1e-17,1e-15,1e-13 --tag prune2-L8-K50-LB6-v12
python3 $D/verify_flow.py t2-L10-K50-LB8-v14 1e5 20
python3 $D/verify_flow.py t2-L10-K50-LB8-v14 1e5 20 5e-7,-5e-7,2e-7
python3 $D/ecc.py t2-L10-K50-LB8-v14 1e-6 2
```

## Outputs

- `results/*.json` and `results/*.log` are committed.
- The `*.npz` arrays of F (about 30–80 MB each) are not committed; the commands above regenerate
  them.
- `torus.py` takes its reference actions from the time means of the modal actions over 200 kyr
  from `orbit.py`, rescaled to the nominal AMD. Recentring makes the result insensitive to that
  choice.

## Parameters

| Flag | Meaning |
|---|---|
| `--L` | Maximum degree in p (stage 1) or u (stage 2) of the normal form |
| `--K` | Fourier cutoff \|k₁\| + \|k₂\| + \|k₁ + k₂\| ≤ K |
| `--LB` | Birkhoff degree |
| `--kol` | Number of Kolmogorov iterations |
| `--G2` | Angle grid of the torus graph and the tube composition |
| `--Lv` | Truncation degree of the tube series in v. Its tail beyond Lv is bounded separately |
| `--kappa` | Tube width factor: the tube is \|v_j\| ≤ κδ. The default κ = 2 |
| `--prune` | Comma-separated pruning thresholds. For each one, F_j drops coefficients with \|c\| (κ·`--prune-delta`)^\|m\| below it, and the tube is measured again (0 = no pruning) |
