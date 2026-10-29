/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.WrapperNodeChain
public import KAM.Planetary.Preparation.WrapperNodeTube

/-!
# Literal node exports for the wrapper steps (GAP-WR)

Facade for `p11_wr_chain_node`, `p11_wr_xi_node`, `p11_wr_ham_node` (`stepP:p11:wr-chain`, on the
literal carrier `|r| < 2`, `|ρ'| < π/2`) and `p11_wr_tube_node` (`stepP:p11:wr-tube`, with the
literal constants `4 n ε` and `2 n ε`).
-/

public section
