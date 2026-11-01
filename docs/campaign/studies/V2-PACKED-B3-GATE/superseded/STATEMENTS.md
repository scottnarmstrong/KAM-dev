# The superseded monolithic torsion core probe

`TorsCore` decided the whole core in one process, with `eps` recomputed from the packed Gram core inside
the same declaration:

    noncomputable def tEps : LGF :=
      ((gramPackedCore 2 lg00GramInv gW gCfg gBook gMemo
        ((73 / 50 : ℚ) - 1 / 100000)).bind gramInvRadius).getD ⟨0⟩

    theorem probe :
        torsPackedCore 2 lg00GramInv gW gCfg lg00Box (1000001 / 1000000 : ℚ) tBook gMemo tMemo tEps
          lg00TorsInv ((21 / 100 : ℚ) - 1 / 100000) = true := by
      decide +kernel

It was OOM-killed at the 4 GB cap after 22 s user (receipt `TorsCore.cost`: max RSS 5.6 GB). The gate now
takes `δβ` and `eps` as literals from the bit-exact mirror `gram_core` (checked by `TorsGramVal` and
`TorsEps`) and decides the three conjuncts of the core in separate processes (`TorsLay`, `TorsPack`,
`TorsFinal`). The data body was that of the current generator, without `tDB` and with the `tEps` above.
