# V2-PACKED-PROD: the packed jet API and the shared-data format

Owner: kamx-packed, branch `v2-packed-prod`. For kamx-pk-cons (consumers, `jetBase`) and kamx-pk-gen (engine, harness,
end-to-end run). Lean: `KAM/CertificateSharp/Packed/JetKeyed.lean`, `JetCheck.lean`.

## 1. The contract (Lean, additive, standard axioms)

```lean
structure JetData where
  jb : JBook                 -- the box Lb, the window, the scale P, the guards
  L : JLedger                -- List (JKeyT × JLed): every exported node, by key
  kbs : List KBlock          -- the blocks, in order, by their keys only
  cert : List (List ℕ)       -- order certificate: cert[i][t] = earlier block exporting import t of block i

structure JLed where         -- an α-free node: radius and norm bound as rationals
  u : Bool  A : ℕ  e : ℕ  x : PC  r : ℚ  nb : ℚ

def jetCheck (n : ℕ) (W : CertWeight) (pe : PiEnclosure α) (cfg : ModelConfig α)
    (K : CertEmbedding α) (p : Slp) (jd : JetData) (B : ℕ) (wanted : List ℕ) : Bool

theorem jetPacked_sound {sw Nw : ℕ} (hW : checkWeight W sw Nw = true)
    (hpe : checkPiEnclosure pe = true) {K : CertEmbedding α} {p : Slp} {jd : JetData} {B : ℕ}
    {wanted : List ℕ} (h : jetCheck n W pe cfg K p jd B wanted = true) :
    ∀ i ∈ wanted, PEnc jd.jb.Lb B jd.jb.P (jetNode jd i) (jetRad (α := α) jd i)
      (jetNb (α := α) jd i) n W.rho (fun θ => p.val n (K.eval n θ) i)
```

- `jetNode jd i : PC`, `jetRad jd i : α := ofRatUp (jd.led i).r`, `jetNb jd i : α := ofRatUp (jd.led i).nb`,
  where `jd.led i` is the ledger entry of key `slotK i = .inl (.inl i)`.
- The enclosure is `Packed/Enc.lean`'s `PEnc`: digits bounded by `B` on the box `jd.jb.Lb`, scale `2^P`, degree 0.
- **Consumers take these per-slot `PEnc` facts as hypotheses**; `jetBase`'s theorem discharges them with
  `jetPacked_sound S.hW S.hpe <chain theorem>`, where `S := checkStatic_sound hs` (`S.hW : checkWeight c.weight
  c.expHalvings c.expOrder = true`, `S.hpe : checkPiEnclosure c.piEnc = true`).
- `jetCheck` is `jetChainOk … && wanted.all (jetWantedOk jd B)`; it holds no landed `Slp.compose`.
- `jetCheck_of` builds the Boolean from its parts (book, each block, order, wanted slots).

## 2. The arguments at a certificate `c` (the T′ instance)

| chain | `cfg` | `p`, `K`, `W`, `pe` | `wanted` | `B` |
|---|---|---|---|---|
| Low | `c.cfgLow` | `c.ham.jet.prog`, `c.emb`, `c.weight`, `c.piEnc` | `torsionSlots n c.ham.jet` (2n first, (2n)² second derivatives) | generated constant `bLow` (the largest load of a wanted node) |
| Full | `c.cfgFull` | the same | `c.ham.jet.v0 :: d1Slots n c.ham.jet` | generated constant `bFull` |

- `cfg` is read only through `cfg.toMant` (leaf conversion); the advice is not read. So a certificate whose
  `cfgLow`/`cfgFull` carry no advice and whose `wit` is empty is accepted. `CertifiedTorus` does not read
  `wit`, `cfg*`, `gramInv`, `torsInv`, `piEnc` or `weight`, so such a copy certifies the same torus.
- **The Low box is the torsion box.** `jdLow.jb.Lb` is to equal B3b's `rb.Lb` (half-width 25, stride 101). The
  generator takes the slot width as a parameter (`--width`), so the jet nodes can be the torsion's memo values
  without repacking; kamx-pk-cons states the agreement as a checked `layoutEq`.

## 3. The shared-data format (generated; outside the default build)

Module prefix `<P>` (set by kamx-pk-gen's harness; default `LG00P`). Every module: copyright, `module`,
`public import`, docstring, `@[expose] public noncomputable section`.

| module | defines |
|---|---|
| `<P>.Data.Cert` | `abbrev LGF := CertFixed 128`; `lgCert : TorusCertificate 2 LGF` (T′, no advice, no witnesses) and its named parts (`lgProg : Slp`, `lgEmb`, …) |
| `<P>.Jet.<C>.Book` | `jb<C> : JBook`, `b<C> : ℕ` |
| `<P>.Jet.<C>.Led<k>` | the ledger nodes `n<C>_<key> : JLed` of part `k`, and `led<C>_<k> : JLedger` |
| `<P>.Jet.<C>.Data` | `kb<C>_<i> : KBlock`, `blocks<C> := [kb<C>_0, …]`, `cert<C> : List (List ℕ)`, `jd<C> : JetData := ⟨jb<C>, led<C>_0 ++ …, blocks<C>, cert<C>⟩` |
| `<P>.Jet.<C>.B<i>` | `blk<C>_<i> : (kb<C>_<i>.toT (jd<C>.L.look (α := LGF))).ok 2 lgCert.weight lgCert.piEnc lgCert.cfg<C> jb<C> lgCert.emb lgCert.ham.jet.prog = true` (`decide +kernel`, one process) |
| `<P>.Jet.<C>.Chain` | `jet<C>_check : jetCheck 2 lgCert.weight lgCert.piEnc lgCert.cfg<C> lgCert.emb lgCert.ham.jet.prog jd<C> b<C> wanted<C> = true` (from the block theorems, `jetCheck_of`) |

`<C>` is `Low` or `Full`. The chain theorem is the single theorem per chain; the block order is the decided
`orderOk` (keys only), so no node equality is decided.
