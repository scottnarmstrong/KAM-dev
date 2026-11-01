# MAIN.md amendments from PROOF-AUDIT-1 (normative)

Audit: [`PROOF-AUDIT-1.md`](PROOF-AUDIT-1.md) (independent Opus 5.5 refute-first audit, verdict **PASS WITH NOTES**,
no blocking issue; SHA-256 `614d3755e3bfbe931ff5e81bfabcd1c959f80d1981fe60d8c0cfe6c182bf707c`). To keep
`MAIN.md` line-addressable, N1 is fixed in place (same line) and N2–N12 are recorded here as amendments that
**override** the cited MAIN lines. Every Lean statement and every freeze proposal follows MAIN as amended here.

| Note | MAIN location | Amendment |
|---|---|---|
| N1 | L7, line 238 | Fixed in place: `Γ d(−ϖ) = (x dy − y dx)/2`. |
| N2 | L6 line 179, L8 line 257, L14 line 472 | **One shared compact `U ⊂ 𝒬`** for Lemmas 6, 8 and 14: `U` contains the closed `4r_g`-tube (sup norm) about `L_δ`; its modulus `Ω_B` is used in (17), in Lemma 8 (`Ω_B(4r_g) ≤ δ/16`) and in (39); require `r ≤ r_g`. |
| N3 | L8, line 271 | State `r_* ≤ 4r_g` explicitly. Then every point of (22) lies within sup distance `max(r_*, 4s, 4b)` of the compact set `K′` (projection over `I⁰ ∈ L_δ` of the closed set of line 261), as `KAM.Planetary.tube` needs. |
| N4 | L12, (35) | (35) is a remark, not a formal dependency (the paper route inverts only `k·ω(I⁰)`). |
| N5 | L10 | Flow existence, Lie-series identification and `c_D` are sketched; they matter only for the optional packages 9–11 (not on the shortest route). |
| N6 | L13, line 442 | State the widths: `2πs₁ < 4s` with a margin for convergence of `Σ e^{2πs₁|k|₁}`; `w < 4b`; `D₀√μ < r_*`; `J` = the stopped interval of Lemma 14; `F = realWfield b.c (realHamiltonianExt b b.rB (liftFast h + f))`. On this route the stopped radius is `r = D₀√μ` and the improvement is to `r/2` (not `r/4`); (39) still gives `C ≤ B(I(t)) − δ + nr/2 + Ω_B(r/2) ≤ B(I(t)) − 3δ/4`. |
| N7 | T15 dependencies | Lemmas 12 and 13 are **alternative** suppliers of the stopped drift; each proof route lists exactly one (roadmap §4). The Lean route uses Lemma 13. |
| N8 | §1 (2); T15 | AMD convention: MAIN's `C = ΣI − |L|` vs the repository's signed `physicalAMD`. With the signed form, `physicalAMD ≤ B − δ` forces `L > 0`; equivalence needs the reflection reduction. Freeze one convention and prove the bridge (OWNER-DECISIONS OD-1; package LP-MOM item 9). |
| N9 | L4, line 158 | The interior-minimizer / geometric-realization paragraph is not used downstream; off the critical path. |
| N10 | L16 | The final `μ₀` also satisfies `A_osc μ₀ ≤ d_⋆/2` and `2A_osc μ₀ ≤ d_pair/2`; the headline constant list records this. |
| N11 | L5 | Define `d_⋆ := a_min m² / (2 I_max²)` first, then bound `|p_i| ≤ ν_i √(2/d_⋆)`. |
| N12 | roadmap, spatial | `ComplexTube.tube` is typed on `Phase (n+n)`; the spatial chart (n fast, 2n slow pairs) needs its gluing proof re-typed. Engineering only. |

Recommended order (audit §6, relayed by root-b8): (1) the sharp barrier, Lemmas 2–6 planar; (2) EARLY, a
one-centre test of the Lemma 13 adapter (physical orbit → rescaled chart → `nonresonant`), the riskiest
interface; (3) Lemma 8 via the repository `tube` theorem; (4) Lemma 14, Theorem 15, Lemma 16; (5) spatial last
(Lemma 17 the largest).
