# SJS-X1: FH25's torus in double-double, and its Fourier support

Untrusted design tooling for gate X1 of [sjs-plan](../../../docs/explorations/sjs-plan.md) §5.2. The report is
[docs/explorations/sjs-x1-support.md](../../../docs/explorations/sjs-x1-support.md). Python 3 with numpy, scipy and mpmath;
SJS-PLAN's scripts in `../plan/` are imported read-only.

| File | What it does |
|---|---|
| `dd.py` | Double-double arithmetic on numpy arrays (two-sum, Dekker's product, sine and cosine by table and Taylor series), a complex DD type and a mixed-radix (2, 3) DD FFT; `python3 dd.py` self-tests against mpmath |
| `hsyn.py` | FH25's Hamiltonian in the synodic regular chart, with regular Kepler variables, over float, DD or mpmath numbers, with sparse first and second derivatives; `python3 hsyn.py` checks it against SJS-PLAN's chart code, against SJS-PLAN's Delaunay route at 200 bits and against mpmath finite differences |
| `x1_torus.py` | The p grid in an adapted frame; `init` (SJS-PLAN's torus into the synodic chart), `newton` (FH25's quasi-Newton step at fixed frequency, double, slab by slab); the DD residual |
| `x1_dd.py` | Double-double defect correction: DD residual, Newton correction in double, DD update on an exact band |
| `x1_regrid.py` | Moves a state to another grid |
| `x1_spectrum.py` | S(L) in SJS-PLAN's definition, noise floor, extents, box ratio, robust frame search, per-axis envelopes |
| `x1_compare.py` | Two tori on different grids, mode by mode and by S(L) |
| `x1_check.py` | Energy on the torus, ⟨Ĝ⟩, action and eccentricity ranges (none used by the solver) |
| `x1_resonance.py` | Isolated near-resonant modes and their clusters along the great-inequality direction |
| `x1_cost.py` | SJS-PLAN's cost model with the measured S(L), plus V2-PACKED's literal-input rates |

Defaults: band |k′ᵢ| ≤ 0.45 Nᵢ; FFT lengths must be 2ᵃ3ᵇ; one thread (`OMP_NUM_THREADS=1`). The production grid
72×144×243 peaks at 3.1 GB; one double-double iteration there takes about 2.5 minutes. Run one process at a time.

`results/`: the logs (`torus_96.log`, `x1_newton_*.log`, `x1_dd_*.log`; `x1_dd_s1.log` is the divergent run of §2 of the
report), the iteration histories saved in the states (`x1_dd_*_hist.json`), the spectra (`x1_spec_*.json`), the grid
comparison, the checks, the near-resonance list, the cost update and the self-tests. Torus files (0.3–0.5 GB) are not
committed; the report's §7 regenerates them.
