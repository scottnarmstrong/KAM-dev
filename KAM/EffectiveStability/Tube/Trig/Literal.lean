/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Round

/-!
# Whitened literals (T2-CONF, N3)

The kernel keys its caches of large natural-number literals by their low 64 bits. Literals whose
chunks share low limbs (zero headroom bits, long runs of equal bytes) make lookups walk long
collision chains: phase-1 gate SR-6 measured 6.4 s per product declaration on raw packed chunks
against 0.09 s on chunks with random low limbs (`docs/explorations/sjsu-g2-gates.md`, SR-6), and
LOCK-DATA measured the same hazard for byte-coded rows (`KAM/SpinOrbit/Data/LockN65/ZCodeX.lean`).
Every big literal is therefore stored XOR-whitened and unwhitened in the kernel. Two forms:

* **Packed naturals** (operands of packed products). Chunk `i` (`b` bits) is XOR-ed with
  `(i + 1) · wmul s`, an odd 64-bit multiplier of a per-literal salt `s`; the key is the closed form
  `wkey s b n = natRamp b n · wmul s` (a few GMP operations, no loop over the chunks).
  `unwhiten_whiten`: unwhitening inverts whitening. The literal itself is written by the generator
  as explicit `Nat.add`/`Nat.shiftLeft` application trees of ≤ 288-bit chunks in sub-definitions of
  ≤ 256 chunks (notation `+`/`<<<` over thousands of leaves exceeds the elaborator's recursion
  depth: SR-6).
* **Byte-coded integer rows** (a lock-independent core copy of `zdecsX`): entries zigzag-coded as
  little-endian base-128 varints, byte `j` of row `r` XOR-ed with `zkey s r j`. **Decode lemma**
  `zdecsX_zwhitenRows`: the whitened rows decode to exactly what the plain rows decode to, whenever
  each row's whitened byte count covers the bytes its entries use (`zdecC`).

The data stay untrusted: a checker checks whatever the decoders denote.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open KAM.CertificateSharp.Packed

/-! ### Whitened packed naturals -/

/-- The odd 64-bit multiplier of the salt `s` (a Weyl/golden-ratio step). -/
def wmul (s : ℕ) : ℕ := ((s * 11400714819323198485 + 15119558931263122691) % 2 ^ 64) ||| 1

/-- The whitening key of a packed literal of `n` chunks of `b` bits: chunk `i` is
`(i + 1) · wmul s` (no carries between chunks when `(n + 1) 2^64 < 2^b`). -/
def wkey (s b n : ℕ) : ℕ := natRamp b n * wmul s

/-- Whiten a packed natural (generator side). -/
def whiten (s b n N : ℕ) : ℕ := N ^^^ wkey s b n

/-- Unwhiten a literal (kernel side): one XOR with the closed-form key. -/
def unwhiten (s b n L : ℕ) : ℕ := L ^^^ wkey s b n

/-- **Decode lemma** of whitened packed naturals. -/
theorem unwhiten_whiten (s b n N : ℕ) : unwhiten s b n (whiten s b n N) = N :=
  natUnmask N (wkey s b n)

theorem wmul_odd (s : ℕ) : wmul s % 2 = 1 := by
  unfold wmul
  rw [Nat.or_mod_two_eq_one]
  right; rfl

/-! ### Whitened byte-coded integer rows (core copy of `zdecsX`) -/

/-- One varint from the low bytes of `n` (at most `f` bytes): the value and the remaining bytes. -/
def zvar : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, n, acc, _ => (acc, n)
  | f + 1, n, acc, sh =>
    if n % 256 < 128 then (acc + n % 256 * 2 ^ sh, n / 256)
    else zvar f (n / 256) (acc + (n % 256 - 128) * 2 ^ sh) (sh + 7)

/-- The zigzag decoding `2v ↦ v`, `2v + 1 ↦ -v - 1`. -/
def unzig (v : ℕ) : ℤ := if v % 2 = 0 then ((v / 2 : ℕ) : ℤ) else -(((v + 1) / 2 : ℕ) : ℤ)

/-- The first `k` plain entries coded in `n` (entries of at most `168` bits). -/
def zdec : ℕ → ℕ → List ℤ
  | 0, _ => []
  | k + 1, n => unzig (zvar 24 n 0 0).1 :: zdec k (zvar 24 n 0 0).2

/-- The entries of plain chunked rows `(k, c)`. -/
def zdecs (cs : List (ℕ × ℕ)) : List ℤ := cs.flatMap fun c => zdec c.1 c.2

/-- The key byte of position `j` of row `r` under the salt `s`. -/
def zkey (s r j : ℕ) : ℕ := (s * 167 + r * 199 + j * 131 + r * j * 59 + 97) % 256

/-- One varint of a whitened row (byte `j` of row `r` is XOR-ed with `zkey s r j`): the value,
the remaining bytes and the next position. -/
def zvarX : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ × ℕ × ℕ
  | 0, _, _, j, n, acc, _ => (acc, n, j)
  | f + 1, s, r, j, n, acc, sh =>
    if Nat.xor (n % 256) (zkey s r j) < 128 then
      (acc + Nat.xor (n % 256) (zkey s r j) <<< sh, n / 256, j + 1)
    else
      zvarX f s r (j + 1) (n / 256) (acc + (Nat.xor (n % 256) (zkey s r j) - 128) <<< sh)
        (sh + 7)

/-- The first `k` entries of whitened row `r`, its bytes from position `j` on coded in `n`. -/
def zdecX (s r : ℕ) : ℕ → ℕ → ℕ → List ℤ
  | 0, _, _ => []
  | k + 1, j, n =>
    unzig (zvarX 24 s r j n 0 0).1 ::
      zdecX s r k (zvarX 24 s r j n 0 0).2.2 (zvarX 24 s r j n 0 0).2.1

/-- The entries of whitened rows from row index `r` on. -/
def zdecsXAux (s : ℕ) : ℕ → List (ℕ × ℕ) → List ℤ
  | _, [] => []
  | r, c :: cs => zdecX s r c.1 0 c.2 ++ zdecsXAux s (r + 1) cs

/-- The entries of whitened chunked rows: each pair `(k, c)` codes `k` whole entries. -/
def zdecsX (s : ℕ) (cs : List (ℕ × ℕ)) : List ℤ := zdecsXAux s 0 cs

/-! #### The decode lemma -/

/-- Whiten the low `L` bytes of `m` with the key stream of row `r` from position `j`. -/
def zwhiten (s r : ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, 0, m => m
  | j, L + 1, m => Nat.xor (m % 256) (zkey s r j) + 256 * zwhiten s r (j + 1) L (m / 256)

/-- The number of bytes `zvar f n` reads. -/
def zvarC : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if n % 256 < 128 then 1 else 1 + zvarC f (n / 256)

/-- The number of bytes `zdec k n` reads. -/
def zdecC : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => zvarC 24 n + zdecC k (zvar 24 n 0 0).2

theorem zkey_lt (s r j : ℕ) : zkey s r j < 256 := Nat.mod_lt _ (by norm_num)

theorem xor_lt_256 {x y : ℕ} (hx : x < 256) (hy : y < 256) : Nat.xor x y < 256 := by
  have := Nat.xor_lt_two_pow (n := 8) (by simpa using hx) (by simpa using hy)
  simpa using this

theorem zwhiten_mod (s r j L m : ℕ) :
    zwhiten s r j (L + 1) m % 256 = Nat.xor (m % 256) (zkey s r j) := by
  rw [zwhiten, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (xor_lt_256 (Nat.mod_lt _ (by norm_num)) (zkey_lt s r j))]

theorem zwhiten_div (s r j L m : ℕ) :
    zwhiten s r j (L + 1) m / 256 = zwhiten s r (j + 1) L (m / 256) := by
  rw [zwhiten, Nat.add_mul_div_left _ _ (by norm_num),
    Nat.div_eq_of_lt (xor_lt_256 (Nat.mod_lt _ (by norm_num)) (zkey_lt s r j)), zero_add]

theorem xor_xor_cancel_right (x k : ℕ) : Nat.xor (Nat.xor x k) k = x := by
  change (x ^^^ k) ^^^ k = x
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- One whitened varint reads as the plain one. -/
theorem zvarX_zwhiten (s r : ℕ) : ∀ (f j L n acc sh : ℕ), zvarC f n ≤ L →
    zvarX f s r j (zwhiten s r j L n) acc sh =
      ((zvar f n acc sh).1, zwhiten s r (j + zvarC f n) (L - zvarC f n) (zvar f n acc sh).2,
        j + zvarC f n)
  | 0, j, L, n, acc, sh, _ => by simp [zvarX, zvar, zvarC]
  | f + 1, j, L, n, acc, sh, hL => by
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by
      have : 1 ≤ zvarC (f + 1) n := by unfold zvarC; split_ifs <;> omega
      omega⟩
    have hb : Nat.xor (zwhiten s r j (L + 1) n % 256) (zkey s r j) = n % 256 := by
      rw [zwhiten_mod, xor_xor_cancel_right]
    rw [zvarX, hb, zwhiten_div]
    by_cases h : n % 256 < 128
    · simp only [h, ↓reduceIte, zvar, zvarC, Nat.shiftLeft_eq]
      simp
    · simp only [h, ↓reduceIte, zvar, zvarC] at hL ⊢
      have ih := zvarX_zwhiten s r f (j + 1) L (n / 256) (acc + (n % 256 - 128) * 2 ^ sh) (sh + 7)
        (by omega)
      rw [Nat.shiftLeft_eq, ih]
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · simp only
        congr 1 <;> omega
      · simp only; omega

/-- A whitened row decodes as the plain row. -/
theorem zdecX_zwhiten (s r : ℕ) : ∀ (k j L n : ℕ), zdecC k n ≤ L →
    zdecX s r k j (zwhiten s r j L n) = zdec k n
  | 0, _, _, _, _ => rfl
  | k + 1, j, L, n, hL => by
    simp only [zdecC] at hL
    rw [zdecX, zdec, zvarX_zwhiten s r 24 j L n 0 0 (by omega)]
    simp only
    rw [zdecX_zwhiten s r k _ _ _ (by omega)]

/-- Whiten rows `(k, L, c)` (`k` entries, `L` whitened bytes, plain bytes `c`) from row index
`r`. -/
def zwhitenRows (s : ℕ) : ℕ → List (ℕ × ℕ × ℕ) → List (ℕ × ℕ)
  | _, [] => []
  | r, c :: cs => (c.1, zwhiten s r 0 c.2.1 c.2.2) :: zwhitenRows s (r + 1) cs

/-- **The decode lemma.** Whitened rows decode to what the plain rows decode to, provided each
row's whitened byte count covers the bytes its entries use. -/
theorem zdecsX_zwhitenRows (s : ℕ) (cs : List (ℕ × ℕ × ℕ))
    (h : ∀ c ∈ cs, zdecC c.1 c.2.2 ≤ c.2.1) :
    zdecsX s (zwhitenRows s 0 cs) = zdecs (cs.map fun c => (c.1, c.2.2)) := by
  unfold zdecsX zdecs
  suffices ∀ r, zdecsXAux s r (zwhitenRows s r cs) =
      (cs.map fun c => (c.1, c.2.2)).flatMap fun c => zdec c.1 c.2 from this 0
  induction cs with
  | nil => intro r; simp [zwhitenRows, zdecsXAux]
  | cons c cs ih =>
    intro r
    rw [zwhitenRows, zdecsXAux, ih (fun x hx => h x (by simp [hx])) (r + 1)]
    simp only [List.map_cons, List.flatMap_cons]
    rw [zdecX_zwhiten s r c.1 0 c.2.1 c.2.2 (h c (by simp))]

/-- `ZCode`'s test rows, plain and whitened under salt 0. -/
theorem zdecs_test : zdecs [(2, 0x0405), (3, 0x0103)] = [-3, 2, -2, -1, 0] := by decide +kernel

theorem zdecsX_test : zdecsX 0 [(2, 0xe064), (3, 0xa4e72b)] = [-3, 2, -2, -1, 0] := by
  decide +kernel

end KAM.EffectiveStability.Tube

end
