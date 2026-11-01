# W6-PREP handoff (in progress)

Package W6-PREP (blueprint `blueprint-W/parts/w6-iteration.tex`, `bpW:w6`), worktree `/root/code/KAM-inp-wpl`,
branch `inp-wpn`. Off the frontier: source-faithful infrastructure used by several nodes; the dependency graph is
still being built. Modules under `KAM/Wave/Iteration/`, namespace `KAM.Wave`.

## Labels and declarations (so far)

| label | status | module | declarations |
|---|---|---|---|
| `sequences` | done | `Sequences` | `w6Tau`, `w6T`, `w6CF`, `w6C0`, `w6C2`, `w6Gamma0`, `W6SeqData` (+ `Valid`), `sigma`, `s`, `alpha`, `M`, `lam`, `eps`, `eta`, `r`, `q`, `dom`, `K0`, `K`, `Kprev`, `sInf`; `s_antitone`, `s_tendsto`, `sInf_le_s`, `sigma_le_min`, `lam_ge`, `one_le_K0`, `two_pow_le_K`, `eps_succ_eq_kappa` |
| `iter-lemma` | W5-free part only | `IterArith` | `w6Iter_q_bounds` (`q_ν ≤ γ₀2^{-ν}`, `q_{ν+1} ≤ q_ν/4`), `eta_le`, `eps_le_small` (W5 smallness), `eps_succ_le`, `lam_succ_le`, `lip_growth_le`, `M_growth_le`, `one_add_mul_one_add_rpow_le`, `div_arith`, `stepMF_eq`, `transf_arith` |
| `k0` | done in the inductive form | `K0` | `w6K0_of_increments` |
