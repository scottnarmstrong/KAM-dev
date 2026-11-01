# SJSU scope prototype

> **Update (1 November 2026, SJSU-P0):** the full degree-18 reconstruction of the SLG13/GLS17
> secular model, with its generator, validation tables and a public dataset, now lives in
> [`applications/sjsu/`](../../applications/sjsu/README.md); see also
> [the recovery report](../../docs/explorations/sjsu-model-recovery.md). This prototype is kept
> unchanged as the 78-term `SJSU4-table` pilot.

This is a floating numerical scout, not a certificate. Its model is the **78
printed decimal monomials** in SLG13 Appendix A, interpreted as exact rational
numbers, with the unprinted degrees omitted by definition. It is a separate
degree-four polynomial, not the full degree-18 SLG13/GLS17 secular Hamiltonian.

From the repository root, with NumPy available to isolated Python:

```sh
nice -n 10 python3 -I scripts/sjsu/scout.py --order 10
nice -n 10 python3 -I scripts/sjsu/scout.py --order 10 --initial table2
python3 -I scripts/sjsu/validate.py
```

The producer forces one numerical thread, a 3 GiB address-space limit and a
3,300-second CPU limit. Measured degree-ten runs took about 14 seconds CPU and
50 MiB RSS. It writes `results/scout-k10*.json` and `results/curve-k10*.csv`.
Timings may vary. NumPy 2.5.3 was used; the non-timing values should reproduce
to ordinary floating tolerance, not necessarily bit for bit on other BLAS builds.

`--order K` is the maximum **Cartesian polynomial degree** of the generated
approximate integrals. Degree two is the uncorrected control. The program
normalizes the quadratic-plus-quartic generator model by finite Lie series,
pulls the quadratic actions back in inverse order, and computes their full
brackets against the input polynomial. No coefficient of these final brackets
is discarded by a degree or magnitude cutoff. Eigenvector and roundoff errors
are not enclosed, so even the coefficient majorants are unvalidated estimates.

`r=1` is a polydisk containing a nominal source point; `r<1` scales the point's
amplitudes toward zero and **excludes it**. `R` is the outer polydisk radius
factor, searched on a small stated grid. `T_year_estimate=0` denotes failure of
this sufficient boundary-gap test, not observed escape. Positive times are
limiting ratios; a rigorous implementation would request a strictly smaller
time, such as half that ratio. Table 1 orbital elements and Table 2 modal data
give separate experiments; their correspondence is not certified.

The JSON also records an **exact rational** nonzero bracket of the printed
polynomial with the standard quadratic AMD. This is not floating error.
`validate.py` checks one coefficient independently by differentiation and
checks normal-form residuals, substitution, and independently evaluated brackets.
The source issue is discussed in the report; the prototype does not silently
symmetrize the model.

To reproduce the transcription, obtain the 14-page article-in-press PDF pinned
in `slg13_quartic.json`, run `pdftotext -layout`, then:

```sh
python3 -I scripts/sjsu/extract_table.py /path/to/paper.txt --output /tmp/slg13_quartic.json
```

The text-layer convention is PDF-specific: xi indices precede exponents, eta
exponents precede indices. The table was also inspected on rendered page 12.
The committed JSON makes ordinary prototype replay independent of PDF extraction.
See [the report](../../docs/explorations/sjsu-effective-stability.md) for scope,
sources, numerical results, source discrepancies, and the proposed proof plan.
