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

## SO-GEN2: rotated frame (owner ruling O5), package R1, enclosed norms

    export OMP_NUM_THREADS=1
    python3 exact_constants.py R1 C M [out.json]                 # exact R1 threshold at time scale C, size M
    python3 rot_norms.py lower 40                                # quick norm enclosures on a coarse candidate
    python3 rot_scan.py lower OUT.jsonl [mode:]Lv,LE,LJ[,S] ...  # truncation scan (exact residual bounds)
    python3 rot_emit.py lower Lv LE LJ S C M ../../certificates/lunar-spin-orbit/lower_rot.json [mode]

`rotlib.py`: exact sparse Fourier models (dyadic integers, parity phase, sup radius on the strip, weighted-l1
norms with a rigorous weight table) mirroring the checker's CertModel semantics.  `rot_build.py`: the rotated
candidate K' = (psi + v/2pi, phi, p, p + J) from the SO-GEN 440-bit solution, its exact invariance-error rows
(Q(sqrt5) as integer pairs), the exp-witness error of E ~ exp(2iv) and the gate G-J budgets.  `rot_norms.py`:
DK, domain, H' majorant, Gram inverse (approximate inverse + Neumann check), bordered torsion inverse.
Results and method: `.drafts/handoff-SO-GEN2.md` of the SO-GEN2 package.
