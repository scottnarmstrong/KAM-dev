# scripts/spin_orbit (SO-GEN, untrusted tooling)

Pipeline (see `.drafts/handoff-SO-GEN.md` of the SO-GEN package for results and timings):

    export OMP_NUM_THREADS=1
    python3 exact_constants.py ../../certificates/lunar-spin-orbit/exact_constants.json
    python3 run_hp.py lower  WORKDIR 4 12      # double continuation, 256x64 + 512x128 chord iteration (pickles)
    python3 run_hp.py upper  WORKDIR 4 12
    python3 emit.py lower WORKDIR/lower_512.pkl ../../certificates/lunar-spin-orbit/lower.json
    python3 emit.py upper WORKDIR/upper_512.pkl ../../certificates/lunar-spin-orbit/upper.json
    python3 analyze.py ../../certificates/lunar-spin-orbit/lower.json ../../certificates/lunar-spin-orbit/lower_truncation_residuals.json
    python3 exact_residual.py ../../certificates/lunar-spin-orbit/lower.json

`model.py` documents the pi-free residual R(v); `exact_residual.py` is the Fraction / Q(sqrt5) reference evaluator.
