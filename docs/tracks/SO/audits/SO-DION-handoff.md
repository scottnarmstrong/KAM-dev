# Handoff SO-DION: lunar frequencies and Diophantine lemmas for general N

## Files (new; no existing file changed)
- `KAM/Certificate/QuadraticDiophantineN.lean` (456 lines)
- `KAM/SpinOrbit/RotFreqN.lean` (124 lines)
Landed N = 40 declarations untouched.

## Mathematics
m = 2N − 1, L = N² − N − 1, D = ((2N−1)² − 5)/2 = 2L. Then 1/(N+g) = (m − √5)/D,
ν∓ = 1 ∓ (m − √5)/D, minimal polynomials
L x² − (2N² − 4N − 1) x + (N² − 3N + 1) = 0 (ν₋), L x² − (2N² − 3) x + (N² + N − 1) = 0 (ν₊)
(N = 40: 1559, 3039, 1481 / 3197, 1639 — match the landed ones).
Norm argument: |N(aν+b)| ≥ 1 gives |aν+b|·|aν'+b| ≥ 1/L, |ν − ν'| = √5/L; constant c works
whenever c²/4 + c√5/L ≤ 1/L and c ≤ 1/2. With c = 2/(N+2) this is 2√5(N+2) ≤ 5N + 5, which holds
for N ≥ 8 (using √5 < 9/4). The order 1/N is sharp up to a constant: (a,b) = (1,−1) gives
|ν − 1| ≈ 1/N.

## γ(N) (exact)
- Original frame `![ν±, 1]`, τ = 1: **γ(N) = lunarGammaN N = 2/(N + 2)**, N ≥ 8.
- Rotated frame `![ν± − 1, 1]`: **1/(N + 2)** (transfer factor 2).
- RotFreq `lunarRotFreq ν κ = κ(ν−1, 1)`: **κ/(N + 2)**.
| N  | γ(N) | rotated | RotFreq |
| 40 | 1/21 (= landed) | 1/42 (= landed) | κ/42 (= landed) |
| 55 | 2/57 | 1/57 | κ/57 |
| 60 | 1/31 | 1/62 | κ/62 |
| 65 | 2/67 | 1/67 | κ/67 |
The certificate's rotated γ parameter must not exceed κ/(N+2) (κ/67 at N = 65).

## General statements (namespace KAM.Certificate)
- `lunarNuMinusN N = 1 - 1/(N + lunarG)`, `lunarNuPlusN N = 1 + 1/(N + lunarG)`, `lunarGammaN N = 2/(N+2)`
- `lunarNuMinusN_eq / lunarNuPlusN_eq (N)`: ν∓ = 1 ∓ (2N − 1 − √5)/(((2N − 1)² − 5)/2) (all N)
- `lunarNuMinusN_quadratic / lunarNuPlusN_quadratic (N)` (all N)
- `lunarNuMinusN_lower / lunarNuPlusN_lower (N) (hN : 8 ≤ N) a b (hab)`:
  `lunarGammaN N / (|a| + |b|) ≤ |a ν + b|`
- `lunarNuMinusN_isDiophantine / lunarNuPlusN_isDiophantine (N) (hN : 8 ≤ N)`:
  `IsDiophantine (lunarGammaN N) 1 ![ν, 1]`
- `lunarNuMinusN_rot_isDiophantine / lunarNuPlusN_rot_isDiophantine (N) (hN)`:
  `IsDiophantine (1 / (N + 2)) 1 ![ν − 1, 1]`
- Instances `lunarNu{Minus,Plus}N_rot_isDiophantine_{65,60,55}` at 1/67, 1/62, 1/57.
- Sanity: `lunarNuMinusN_forty : lunarNuMinusN 40 = lunarNuMinus`, `lunarNuPlusN_forty`,
  `lunarGammaN_forty : lunarGammaN 40 = 1/21`, `lunarNuMinusN_isDiophantine_forty` (re-derives the landed
  `IsDiophantine (1/21) 1 ![lunarNuMinus, 1]`), `lunarNuPlusN_rot_isDiophantine_forty` (landed 1/42 statement).
## RotFreq layer (namespace KAM.SpinOrbit)
- `lunarRotFreqMinusN_eq N κ : lunarRotFreq (lunarNuMinusN N) κ =
   algFreq 2 [[-(2N−1)κ/(2(N²−N−1)), κ/(2(N²−N−1))], [κ]] √5`; `lunarRotFreqPlusN_eq` with signs flipped
  (all N; at N = 40 the coefficients are −79κ/3118, κ/3118 as landed).
- `lunarRotFreq{Minus,Plus}N_isDiophantine N (hN : 8 ≤ N) (hκ : 0 < κ)`:
  `IsDiophantine (κ / (N + 2)) 1 (lunarRotFreq ν κ)`; instances `_65` (κ/67), `_60` (κ/62), `_55` (κ/57);
  `lunarRotFreqMinusN_forty` recovers the landed κ/42.

## Checks
- Gate build: `inp_lake_build.sh /root/code/KAM-inp-sodion KAM.Certificate.QuadraticDiophantineN
  KAM.SpinOrbit.RotFreqN` → `Built ... QuadraticDiophantineN (24s)`, `Built ... RotFreqN (4.0s)`,
  `Build completed successfully`; no warnings, no sorry.
- `main_shortname_check.py` on both modules: `Short-name check OK (no reused public short name)`.
- Lines ≤ 100 columns (checked); no heartbeat overrides.
- `scripts/lint_sources.sh`: check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK; the only
  failure is `KAM.lean is out of date; run scripts/gen_root_imports.py` (caused by the two new modules;
  KAM.lean is generated and I did not touch it per rule 10 — the orchestrator regenerates it on landing).
## Axioms
All of `lunarNu{Minus,Plus}N_lower`, `_quadratic`, `_rot_isDiophantine`, the forty sanity theorems,
`lunarRotFreqMinusN_eq`, `lunarRotFreqPlusN_isDiophantine_65`, `lunarRotFreqMinusN_forty`:
`[propext, Classical.choice, Quot.sound]`.

## Uncertainties / errata / deviations
- Diophantine results assume N ≥ 8 (closed forms and quadratics hold for all N). Not a restriction for 55/60/65.
- Private helpers (rotIdx, algFreq_two, smul-eq) were re-proved under new private names because the landed ones are
  private. No errata found in sources.
- No design signals; nothing near heartbeat limits.

AUDIT FOCUS: (1) mathematical correctness of the general-N norm argument: the minimal polynomials, the closed forms ν∓ = 1 ∓ (2N−1−√5)/D, the lower bound |aν + b| ≥ (2/(N+2))/(|a|+|b|) for N ≥ 8 (check the inequality 2√5(N+2) ≤ 5N+5 and every step), and the transfer to the rotated frame (γ/2) and to lunarRotFreq (κ·γ); (2) that IsDiophantine here is the landed definition (the same one checkTorusCertificate_sound / checkTorusCertificateSharp_sound consume), with the same norm convention (|a|+|b|) and τ = 1; (3) the algFreq forms lunarRotFreq{Minus,Plus}N_eq are exactly what a certificate's frequency box check (checkAlgBox with checkRootEnclosure for √5) needs; (4) the N = 40 sanity theorems really re-derive the landed statements; (5) no landed declaration changed; names, kernel replay, axioms, lint.
