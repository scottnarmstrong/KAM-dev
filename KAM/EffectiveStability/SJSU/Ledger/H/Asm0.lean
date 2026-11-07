/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ledger.H.Checks0

/-!
# Ledger blocks (generated)
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem tin : sjsuHD.ns.all sjsuHD.tIn = true := by
  rw [show sjsuHD.ns = ((((((((([(0, 0, 2), (0, 0, 4)] : List (Nat × Nat × Nat)) ++ ([(0, 0, 6), (0,
    0, 8)] : List (Nat × Nat × Nat))) ++ (([(0, 0, 10), (0, 0, 12)] : List (Nat × Nat × Nat)) ++ (([
    (0, 0, 14), (0, 0, 16)] : List (Nat × Nat × Nat)) ++ ([(0, 0, 18), (0, 1, 1)] : List (Nat × Nat
    × Nat))))) ++ ((([(0, 1, 3), (0, 1, 5)] : List (Nat × Nat × Nat)) ++ (([(0, 1, 7), (0, 1, 9)] :
    List (Nat × Nat × Nat)) ++ ([(0, 1, 11), (0, 1, 13)] : List (Nat × Nat × Nat)))) ++ (([(0, 1, 15
    ), (0, 1, 17)] : List (Nat × Nat × Nat)) ++ (([(0, 2, 0), (0, 2, 2)] : List (Nat × Nat × Nat))
    ++ ([(0, 2, 4), (0, 2, 6)] : List (Nat × Nat × Nat)))))) ++ (((([(0, 2, 8), (0, 2, 10)] : List (
    Nat × Nat × Nat)) ++ ([(0, 2, 12), (0, 2, 14)] : List (Nat × Nat × Nat))) ++ (([(0, 2, 16), (0,
    3, 1)] : List (Nat × Nat × Nat)) ++ (([(0, 3, 3), (0, 3, 5)] : List (Nat × Nat × Nat)) ++ ([(0,
    3, 7), (0, 3, 9)] : List (Nat × Nat × Nat))))) ++ ((([(0, 3, 11), (0, 3, 13)] : List (Nat × Nat
    × Nat)) ++ (([(0, 3, 15), (0, 4, 0)] : List (Nat × Nat × Nat)) ++ ([(0, 4, 2), (0, 4, 4)] : List
    (Nat × Nat × Nat)))) ++ (([(0, 4, 6), (0, 4, 8)] : List (Nat × Nat × Nat)) ++ (([(0, 4, 10), (0,
    4, 12)] : List (Nat × Nat × Nat)) ++ ([(0, 4, 14), (0, 5, 1)] : List (Nat × Nat × Nat))))))) ++
    ((((([(0, 5, 3), (0, 5, 5)] : List (Nat × Nat × Nat)) ++ ([(0, 5, 7), (0, 5, 9)] : List (Nat ×
    Nat × Nat))) ++ (([(0, 5, 11), (0, 5, 13)] : List (Nat × Nat × Nat)) ++ (([(0, 6, 0), (0, 6, 2)]
    : List (Nat × Nat × Nat)) ++ ([(0, 6, 4), (0, 6, 6)] : List (Nat × Nat × Nat))))) ++ ((([(0, 6,
    8), (0, 6, 10)] : List (Nat × Nat × Nat)) ++ (([(0, 6, 12), (0, 7, 1)] : List (Nat × Nat × Nat))
    ++ ([(0, 7, 3), (0, 7, 5)] : List (Nat × Nat × Nat)))) ++ (([(0, 7, 7), (0, 7, 9)] : List (Nat ×
    Nat × Nat)) ++ (([(0, 7, 11), (0, 8, 0)] : List (Nat × Nat × Nat)) ++ ([(0, 8, 2), (0, 8, 4)] :
    List (Nat × Nat × Nat)))))) ++ (((([(0, 8, 6), (0, 8, 8)] : List (Nat × Nat × Nat)) ++ ([(0, 8,
    10), (0, 9, 1)] : List (Nat × Nat × Nat))) ++ (([(0, 9, 3), (0, 9, 5)] : List (Nat × Nat × Nat))
    ++ (([(0, 9, 7), (0, 9, 9)] : List (Nat × Nat × Nat)) ++ ([(0, 10, 0), (0, 10, 2)] : List (Nat ×
    Nat × Nat))))) ++ ((([(0, 10, 4), (0, 10, 6)] : List (Nat × Nat × Nat)) ++ (([(0, 10, 8), (0, 11
    , 1)] : List (Nat × Nat × Nat)) ++ ([(0, 11, 3), (0, 11, 5)] : List (Nat × Nat × Nat)))) ++ (([(
    0, 11, 7), (0, 12, 0)] : List (Nat × Nat × Nat)) ++ (([(0, 12, 2), (0, 12, 4)] : List (Nat × Nat
    × Nat)) ++ ([(0, 12, 6), (0, 13, 1)] : List (Nat × Nat × Nat)))))))) ++ (((((([(0, 13, 3), (0,
    13, 5)] : List (Nat × Nat × Nat)) ++ ([(0, 14, 0), (0, 14, 2)] : List (Nat × Nat × Nat))) ++ (([
    (0, 14, 4), (0, 15, 1)] : List (Nat × Nat × Nat)) ++ (([(0, 15, 3), (0, 16, 0)] : List (Nat ×
    Nat × Nat)) ++ ([(0, 16, 2), (0, 17, 1)] : List (Nat × Nat × Nat))))) ++ ((([(0, 18, 0), (1, 0,
    1)] : List (Nat × Nat × Nat)) ++ (([(1, 0, 3), (1, 0, 5)] : List (Nat × Nat × Nat)) ++ ([(1, 0,
    7), (1, 0, 9)] : List (Nat × Nat × Nat)))) ++ (([(1, 0, 11), (1, 0, 13)] : List (Nat × Nat × Nat
    )) ++ (([(1, 0, 15), (1, 0, 17)] : List (Nat × Nat × Nat)) ++ ([(1, 1, 0), (1, 1, 2)] : List (
    Nat × Nat × Nat)))))) ++ (((([(1, 1, 4), (1, 1, 6)] : List (Nat × Nat × Nat)) ++ ([(1, 1, 8), (1
    , 1, 10)] : List (Nat × Nat × Nat))) ++ (([(1, 1, 12), (1, 1, 14)] : List (Nat × Nat × Nat)) ++
    (([(1, 1, 16), (1, 2, 1)] : List (Nat × Nat × Nat)) ++ ([(1, 2, 3), (1, 2, 5)] : List (Nat × Nat
    × Nat))))) ++ ((([(1, 2, 7), (1, 2, 9)] : List (Nat × Nat × Nat)) ++ (([(1, 2, 11), (1, 2, 13)]
    : List (Nat × Nat × Nat)) ++ ([(1, 2, 15), (1, 3, 0)] : List (Nat × Nat × Nat)))) ++ (([(1, 3, 2
    ), (1, 3, 4)] : List (Nat × Nat × Nat)) ++ (([(1, 3, 6), (1, 3, 8)] : List (Nat × Nat × Nat)) ++
    ([(1, 3, 10), (1, 3, 12)] : List (Nat × Nat × Nat))))))) ++ ((((([(1, 3, 14), (1, 4, 1)] : List
    (Nat × Nat × Nat)) ++ ([(1, 4, 3), (1, 4, 5)] : List (Nat × Nat × Nat))) ++ (([(1, 4, 7), (1, 4,
    9)] : List (Nat × Nat × Nat)) ++ (([(1, 4, 11), (1, 4, 13)] : List (Nat × Nat × Nat)) ++ ([(1, 5
    , 0), (1, 5, 2)] : List (Nat × Nat × Nat))))) ++ ((([(1, 5, 4), (1, 5, 6)] : List (Nat × Nat ×
    Nat)) ++ (([(1, 5, 8), (1, 5, 10)] : List (Nat × Nat × Nat)) ++ ([(1, 5, 12), (1, 6, 1)] : List
    (Nat × Nat × Nat)))) ++ (([(1, 6, 3), (1, 6, 5)] : List (Nat × Nat × Nat)) ++ (([(1, 6, 7), (1,
    6, 9)] : List (Nat × Nat × Nat)) ++ ([(1, 6, 11), (1, 7, 0)] : List (Nat × Nat × Nat)))))) ++ ((
    (([(1, 7, 2), (1, 7, 4)] : List (Nat × Nat × Nat)) ++ (([(1, 7, 6), (1, 7, 8)] : List (Nat × Nat
    × Nat)) ++ ([(1, 7, 10), (1, 8, 1)] : List (Nat × Nat × Nat)))) ++ (([(1, 8, 3), (1, 8, 5)] :
    List (Nat × Nat × Nat)) ++ (([(1, 8, 7), (1, 8, 9)] : List (Nat × Nat × Nat)) ++ ([(1, 9, 0), (1
    , 9, 2)] : List (Nat × Nat × Nat))))) ++ ((([(1, 9, 4), (1, 9, 6)] : List (Nat × Nat × Nat)) ++
    (([(1, 9, 8), (1, 10, 1)] : List (Nat × Nat × Nat)) ++ ([(1, 10, 3), (1, 10, 5)] : List (Nat ×
    Nat × Nat)))) ++ (([(1, 10, 7), (1, 11, 0)] : List (Nat × Nat × Nat)) ++ (([(1, 11, 2), (1, 11,
    4)] : List (Nat × Nat × Nat)) ++ ([(1, 11, 6), (1, 12, 1)] : List (Nat × Nat × Nat))))))))) ++ (
    (((((([(1, 12, 3), (1, 12, 5)] : List (Nat × Nat × Nat)) ++ ([(1, 13, 0), (1, 13, 2)] : List (
    Nat × Nat × Nat))) ++ (([(1, 13, 4), (1, 14, 1)] : List (Nat × Nat × Nat)) ++ (([(1, 14, 3), (1,
    15, 0)] : List (Nat × Nat × Nat)) ++ ([(1, 15, 2), (1, 16, 1)] : List (Nat × Nat × Nat))))) ++ (
    (([(1, 17, 0), (2, 0, 0)] : List (Nat × Nat × Nat)) ++ (([(2, 0, 2), (2, 0, 4)] : List (Nat ×
    Nat × Nat)) ++ ([(2, 0, 6), (2, 0, 8)] : List (Nat × Nat × Nat)))) ++ (([(2, 0, 10), (2, 0, 12)]
    : List (Nat × Nat × Nat)) ++ (([(2, 0, 14), (2, 0, 16)] : List (Nat × Nat × Nat)) ++ ([(2, 1, 1)
    , (2, 1, 3)] : List (Nat × Nat × Nat)))))) ++ (((([(2, 1, 5), (2, 1, 7)] : List (Nat × Nat × Nat
    )) ++ ([(2, 1, 9), (2, 1, 11)] : List (Nat × Nat × Nat))) ++ (([(2, 1, 13), (2, 1, 15)] : List (
    Nat × Nat × Nat)) ++ (([(2, 2, 0), (2, 2, 2)] : List (Nat × Nat × Nat)) ++ ([(2, 2, 4), (2, 2, 6
    )] : List (Nat × Nat × Nat))))) ++ ((([(2, 2, 8), (2, 2, 10)] : List (Nat × Nat × Nat)) ++ (([(2
    , 2, 12), (2, 2, 14)] : List (Nat × Nat × Nat)) ++ ([(2, 3, 1), (2, 3, 3)] : List (Nat × Nat ×
    Nat)))) ++ (([(2, 3, 5), (2, 3, 7)] : List (Nat × Nat × Nat)) ++ (([(2, 3, 9), (2, 3, 11)] :
    List (Nat × Nat × Nat)) ++ ([(2, 3, 13), (2, 4, 0)] : List (Nat × Nat × Nat))))))) ++ ((((([(2,
    4, 2), (2, 4, 4)] : List (Nat × Nat × Nat)) ++ ([(2, 4, 6), (2, 4, 8)] : List (Nat × Nat × Nat))
    ) ++ (([(2, 4, 10), (2, 4, 12)] : List (Nat × Nat × Nat)) ++ (([(2, 5, 1), (2, 5, 3)] : List (
    Nat × Nat × Nat)) ++ ([(2, 5, 5), (2, 5, 7)] : List (Nat × Nat × Nat))))) ++ ((([(2, 5, 9), (2,
    5, 11)] : List (Nat × Nat × Nat)) ++ (([(2, 6, 0), (2, 6, 2)] : List (Nat × Nat × Nat)) ++ ([(2,
    6, 4), (2, 6, 6)] : List (Nat × Nat × Nat)))) ++ (([(2, 6, 8), (2, 6, 10)] : List (Nat × Nat ×
    Nat)) ++ (([(2, 7, 1), (2, 7, 3)] : List (Nat × Nat × Nat)) ++ ([(2, 7, 5), (2, 7, 7)] : List (
    Nat × Nat × Nat)))))) ++ (((([(2, 7, 9), (2, 8, 0)] : List (Nat × Nat × Nat)) ++ ([(2, 8, 2), (2
    , 8, 4)] : List (Nat × Nat × Nat))) ++ (([(2, 8, 6), (2, 8, 8)] : List (Nat × Nat × Nat)) ++ (([
    (2, 9, 1), (2, 9, 3)] : List (Nat × Nat × Nat)) ++ ([(2, 9, 5), (2, 9, 7)] : List (Nat × Nat ×
    Nat))))) ++ ((([(2, 10, 0), (2, 10, 2)] : List (Nat × Nat × Nat)) ++ (([(2, 10, 4), (2, 10, 6)]
    : List (Nat × Nat × Nat)) ++ ([(2, 11, 1), (2, 11, 3)] : List (Nat × Nat × Nat)))) ++ (([(2, 11,
    5), (2, 12, 0)] : List (Nat × Nat × Nat)) ++ (([(2, 12, 2), (2, 12, 4)] : List (Nat × Nat × Nat)
    ) ++ ([(2, 13, 1), (2, 13, 3)] : List (Nat × Nat × Nat)))))))) ++ (((((([(2, 14, 0), (2, 14, 2)]
    : List (Nat × Nat × Nat)) ++ ([(2, 15, 1), (2, 16, 0)] : List (Nat × Nat × Nat))) ++ (([(3, 0, 1
    ), (3, 0, 3)] : List (Nat × Nat × Nat)) ++ (([(3, 0, 5), (3, 0, 7)] : List (Nat × Nat × Nat)) ++
    ([(3, 0, 9), (3, 0, 11)] : List (Nat × Nat × Nat))))) ++ ((([(3, 0, 13), (3, 0, 15)] : List (Nat
    × Nat × Nat)) ++ (([(3, 1, 0), (3, 1, 2)] : List (Nat × Nat × Nat)) ++ ([(3, 1, 4), (3, 1, 6)] :
    List (Nat × Nat × Nat)))) ++ (([(3, 1, 8), (3, 1, 10)] : List (Nat × Nat × Nat)) ++ (([(3, 1, 12
    ), (3, 1, 14)] : List (Nat × Nat × Nat)) ++ ([(3, 2, 1), (3, 2, 3)] : List (Nat × Nat × Nat)))))
    ) ++ (((([(3, 2, 5), (3, 2, 7)] : List (Nat × Nat × Nat)) ++ ([(3, 2, 9), (3, 2, 11)] : List (
    Nat × Nat × Nat))) ++ (([(3, 2, 13), (3, 3, 0)] : List (Nat × Nat × Nat)) ++ (([(3, 3, 2), (3, 3
    , 4)] : List (Nat × Nat × Nat)) ++ ([(3, 3, 6), (3, 3, 8)] : List (Nat × Nat × Nat))))) ++ ((([(
    3, 3, 10), (3, 3, 12)] : List (Nat × Nat × Nat)) ++ (([(3, 4, 1), (3, 4, 3)] : List (Nat × Nat ×
    Nat)) ++ ([(3, 4, 5), (3, 4, 7)] : List (Nat × Nat × Nat)))) ++ (([(3, 4, 9), (3, 4, 11)] : List
    (Nat × Nat × Nat)) ++ (([(3, 5, 0), (3, 5, 2)] : List (Nat × Nat × Nat)) ++ ([(3, 5, 4), (3, 5,
    6)] : List (Nat × Nat × Nat))))))) ++ ((((([(3, 5, 8), (3, 5, 10)] : List (Nat × Nat × Nat)) ++
    ([(3, 6, 1), (3, 6, 3)] : List (Nat × Nat × Nat))) ++ (([(3, 6, 5), (3, 6, 7)] : List (Nat × Nat
    × Nat)) ++ (([(3, 6, 9), (3, 7, 0)] : List (Nat × Nat × Nat)) ++ ([(3, 7, 2), (3, 7, 4)] : List
    (Nat × Nat × Nat))))) ++ ((([(3, 7, 6), (3, 7, 8)] : List (Nat × Nat × Nat)) ++ (([(3, 8, 1), (3
    , 8, 3)] : List (Nat × Nat × Nat)) ++ ([(3, 8, 5), (3, 8, 7)] : List (Nat × Nat × Nat)))) ++ (([
    (3, 9, 0), (3, 9, 2)] : List (Nat × Nat × Nat)) ++ (([(3, 9, 4), (3, 9, 6)] : List (Nat × Nat ×
    Nat)) ++ ([(3, 10, 1), (3, 10, 3)] : List (Nat × Nat × Nat)))))) ++ (((([(3, 10, 5), (3, 11, 0)]
    : List (Nat × Nat × Nat)) ++ (([(3, 11, 2), (3, 11, 4)] : List (Nat × Nat × Nat)) ++ ([(3, 12, 1
    ), (3, 12, 3)] : List (Nat × Nat × Nat)))) ++ (([(3, 13, 0), (3, 13, 2)] : List (Nat × Nat × Nat
    )) ++ (([(3, 14, 1), (3, 15, 0)] : List (Nat × Nat × Nat)) ++ ([(4, 0, 0), (4, 0, 2)] : List (
    Nat × Nat × Nat))))) ++ ((([(4, 0, 4), (4, 0, 6)] : List (Nat × Nat × Nat)) ++ (([(4, 0, 8), (4,
    0, 10)] : List (Nat × Nat × Nat)) ++ ([(4, 0, 12), (4, 0, 14)] : List (Nat × Nat × Nat)))) ++ ((
    [(4, 1, 1), (4, 1, 3)] : List (Nat × Nat × Nat)) ++ (([(4, 1, 5), (4, 1, 7)] : List (Nat × Nat ×
    Nat)) ++ ([(4, 1, 9), (4, 1, 11)] : List (Nat × Nat × Nat)))))))))) ++ (((((((([(4, 1, 13), (4,
    2, 0)] : List (Nat × Nat × Nat)) ++ ([(4, 2, 2), (4, 2, 4)] : List (Nat × Nat × Nat))) ++ (([(4,
    2, 6), (4, 2, 8)] : List (Nat × Nat × Nat)) ++ (([(4, 2, 10), (4, 2, 12)] : List (Nat × Nat ×
    Nat)) ++ ([(4, 3, 1), (4, 3, 3)] : List (Nat × Nat × Nat))))) ++ ((([(4, 3, 5), (4, 3, 7)] :
    List (Nat × Nat × Nat)) ++ (([(4, 3, 9), (4, 3, 11)] : List (Nat × Nat × Nat)) ++ ([(4, 4, 0), (
    4, 4, 2)] : List (Nat × Nat × Nat)))) ++ (([(4, 4, 4), (4, 4, 6)] : List (Nat × Nat × Nat)) ++ (
    ([(4, 4, 8), (4, 4, 10)] : List (Nat × Nat × Nat)) ++ ([(4, 5, 1), (4, 5, 3)] : List (Nat × Nat
    × Nat)))))) ++ (((([(4, 5, 5), (4, 5, 7)] : List (Nat × Nat × Nat)) ++ ([(4, 5, 9), (4, 6, 0)] :
    List (Nat × Nat × Nat))) ++ (([(4, 6, 2), (4, 6, 4)] : List (Nat × Nat × Nat)) ++ (([(4, 6, 6),
    (4, 6, 8)] : List (Nat × Nat × Nat)) ++ ([(4, 7, 1), (4, 7, 3)] : List (Nat × Nat × Nat))))) ++
    ((([(4, 7, 5), (4, 7, 7)] : List (Nat × Nat × Nat)) ++ (([(4, 8, 0), (4, 8, 2)] : List (Nat ×
    Nat × Nat)) ++ ([(4, 8, 4), (4, 8, 6)] : List (Nat × Nat × Nat)))) ++ (([(4, 9, 1), (4, 9, 3)] :
    List (Nat × Nat × Nat)) ++ (([(4, 9, 5), (4, 10, 0)] : List (Nat × Nat × Nat)) ++ ([(4, 10, 2),
    (4, 10, 4)] : List (Nat × Nat × Nat))))))) ++ ((((([(4, 11, 1), (4, 11, 3)] : List (Nat × Nat ×
    Nat)) ++ ([(4, 12, 0), (4, 12, 2)] : List (Nat × Nat × Nat))) ++ (([(4, 13, 1), (4, 14, 0)] :
    List (Nat × Nat × Nat)) ++ (([(5, 0, 1), (5, 0, 3)] : List (Nat × Nat × Nat)) ++ ([(5, 0, 5), (5
    , 0, 7)] : List (Nat × Nat × Nat))))) ++ ((([(5, 0, 9), (5, 0, 11)] : List (Nat × Nat × Nat)) ++
    (([(5, 0, 13), (5, 1, 0)] : List (Nat × Nat × Nat)) ++ ([(5, 1, 2), (5, 1, 4)] : List (Nat × Nat
    × Nat)))) ++ (([(5, 1, 6), (5, 1, 8)] : List (Nat × Nat × Nat)) ++ (([(5, 1, 10), (5, 1, 12)] :
    List (Nat × Nat × Nat)) ++ ([(5, 2, 1), (5, 2, 3)] : List (Nat × Nat × Nat)))))) ++ (((([(5, 2,
    5), (5, 2, 7)] : List (Nat × Nat × Nat)) ++ ([(5, 2, 9), (5, 2, 11)] : List (Nat × Nat × Nat)))
    ++ (([(5, 3, 0), (5, 3, 2)] : List (Nat × Nat × Nat)) ++ (([(5, 3, 4), (5, 3, 6)] : List (Nat ×
    Nat × Nat)) ++ ([(5, 3, 8), (5, 3, 10)] : List (Nat × Nat × Nat))))) ++ ((([(5, 4, 1), (5, 4, 3)
    ] : List (Nat × Nat × Nat)) ++ (([(5, 4, 5), (5, 4, 7)] : List (Nat × Nat × Nat)) ++ ([(5, 4, 9)
    , (5, 5, 0)] : List (Nat × Nat × Nat)))) ++ (([(5, 5, 2), (5, 5, 4)] : List (Nat × Nat × Nat))
    ++ (([(5, 5, 6), (5, 5, 8)] : List (Nat × Nat × Nat)) ++ ([(5, 6, 1), (5, 6, 3)] : List (Nat ×
    Nat × Nat)))))))) ++ (((((([(5, 6, 5), (5, 6, 7)] : List (Nat × Nat × Nat)) ++ ([(5, 7, 0), (5,
    7, 2)] : List (Nat × Nat × Nat))) ++ (([(5, 7, 4), (5, 7, 6)] : List (Nat × Nat × Nat)) ++ (([(5
    , 8, 1), (5, 8, 3)] : List (Nat × Nat × Nat)) ++ ([(5, 8, 5), (5, 9, 0)] : List (Nat × Nat × Nat
    ))))) ++ ((([(5, 9, 2), (5, 9, 4)] : List (Nat × Nat × Nat)) ++ (([(5, 10, 1), (5, 10, 3)] :
    List (Nat × Nat × Nat)) ++ ([(5, 11, 0), (5, 11, 2)] : List (Nat × Nat × Nat)))) ++ (([(5, 12, 1
    ), (5, 13, 0)] : List (Nat × Nat × Nat)) ++ (([(6, 0, 0), (6, 0, 2)] : List (Nat × Nat × Nat))
    ++ ([(6, 0, 4), (6, 0, 6)] : List (Nat × Nat × Nat)))))) ++ (((([(6, 0, 8), (6, 0, 10)] : List (
    Nat × Nat × Nat)) ++ ([(6, 0, 12), (6, 1, 1)] : List (Nat × Nat × Nat))) ++ (([(6, 1, 3), (6, 1,
    5)] : List (Nat × Nat × Nat)) ++ (([(6, 1, 7), (6, 1, 9)] : List (Nat × Nat × Nat)) ++ ([(6, 1,
    11), (6, 2, 0)] : List (Nat × Nat × Nat))))) ++ ((([(6, 2, 2), (6, 2, 4)] : List (Nat × Nat ×
    Nat)) ++ (([(6, 2, 6), (6, 2, 8)] : List (Nat × Nat × Nat)) ++ ([(6, 2, 10), (6, 3, 1)] : List (
    Nat × Nat × Nat)))) ++ (([(6, 3, 3), (6, 3, 5)] : List (Nat × Nat × Nat)) ++ (([(6, 3, 7), (6, 3
    , 9)] : List (Nat × Nat × Nat)) ++ ([(6, 4, 0), (6, 4, 2)] : List (Nat × Nat × Nat))))))) ++ (((
    (([(6, 4, 4), (6, 4, 6)] : List (Nat × Nat × Nat)) ++ ([(6, 4, 8), (6, 5, 1)] : List (Nat × Nat
    × Nat))) ++ (([(6, 5, 3), (6, 5, 5)] : List (Nat × Nat × Nat)) ++ (([(6, 5, 7), (6, 6, 0)] :
    List (Nat × Nat × Nat)) ++ ([(6, 6, 2), (6, 6, 4)] : List (Nat × Nat × Nat))))) ++ ((([(6, 6, 6)
    , (6, 7, 1)] : List (Nat × Nat × Nat)) ++ (([(6, 7, 3), (6, 7, 5)] : List (Nat × Nat × Nat)) ++
    ([(6, 8, 0), (6, 8, 2)] : List (Nat × Nat × Nat)))) ++ (([(6, 8, 4), (6, 9, 1)] : List (Nat ×
    Nat × Nat)) ++ (([(6, 9, 3), (6, 10, 0)] : List (Nat × Nat × Nat)) ++ ([(6, 10, 2), (6, 11, 1)]
    : List (Nat × Nat × Nat)))))) ++ (((([(6, 12, 0), (7, 0, 1)] : List (Nat × Nat × Nat)) ++ (([(7,
    0, 3), (7, 0, 5)] : List (Nat × Nat × Nat)) ++ ([(7, 0, 7), (7, 0, 9)] : List (Nat × Nat × Nat))
    )) ++ (([(7, 0, 11), (7, 1, 0)] : List (Nat × Nat × Nat)) ++ (([(7, 1, 2), (7, 1, 4)] : List (
    Nat × Nat × Nat)) ++ ([(7, 1, 6), (7, 1, 8)] : List (Nat × Nat × Nat))))) ++ ((([(7, 1, 10), (7,
    2, 1)] : List (Nat × Nat × Nat)) ++ (([(7, 2, 3), (7, 2, 5)] : List (Nat × Nat × Nat)) ++ ([(7,
    2, 7), (7, 2, 9)] : List (Nat × Nat × Nat)))) ++ (([(7, 3, 0), (7, 3, 2)] : List (Nat × Nat ×
    Nat)) ++ (([(7, 3, 4), (7, 3, 6)] : List (Nat × Nat × Nat)) ++ ([(7, 3, 8), (7, 4, 1)] : List (
    Nat × Nat × Nat))))))))) ++ ((((((([(7, 4, 3), (7, 4, 5)] : List (Nat × Nat × Nat)) ++ ([(7, 4,
    7), (7, 5, 0)] : List (Nat × Nat × Nat))) ++ (([(7, 5, 2), (7, 5, 4)] : List (Nat × Nat × Nat))
    ++ (([(7, 5, 6), (7, 6, 1)] : List (Nat × Nat × Nat)) ++ ([(7, 6, 3), (7, 6, 5)] : List (Nat ×
    Nat × Nat))))) ++ ((([(7, 7, 0), (7, 7, 2)] : List (Nat × Nat × Nat)) ++ (([(7, 7, 4), (7, 8, 1)
    ] : List (Nat × Nat × Nat)) ++ ([(7, 8, 3), (7, 9, 0)] : List (Nat × Nat × Nat)))) ++ (([(7, 9,
    2), (7, 10, 1)] : List (Nat × Nat × Nat)) ++ (([(7, 11, 0), (8, 0, 0)] : List (Nat × Nat × Nat))
    ++ ([(8, 0, 2), (8, 0, 4)] : List (Nat × Nat × Nat)))))) ++ (((([(8, 0, 6), (8, 0, 8)] : List (
    Nat × Nat × Nat)) ++ ([(8, 0, 10), (8, 1, 1)] : List (Nat × Nat × Nat))) ++ (([(8, 1, 3), (8, 1,
    5)] : List (Nat × Nat × Nat)) ++ (([(8, 1, 7), (8, 1, 9)] : List (Nat × Nat × Nat)) ++ ([(8, 2,
    0), (8, 2, 2)] : List (Nat × Nat × Nat))))) ++ ((([(8, 2, 4), (8, 2, 6)] : List (Nat × Nat × Nat
    )) ++ (([(8, 2, 8), (8, 3, 1)] : List (Nat × Nat × Nat)) ++ ([(8, 3, 3), (8, 3, 5)] : List (Nat
    × Nat × Nat)))) ++ (([(8, 3, 7), (8, 4, 0)] : List (Nat × Nat × Nat)) ++ (([(8, 4, 2), (8, 4, 4)
    ] : List (Nat × Nat × Nat)) ++ ([(8, 4, 6), (8, 5, 1)] : List (Nat × Nat × Nat))))))) ++ ((((([(
    8, 5, 3), (8, 5, 5)] : List (Nat × Nat × Nat)) ++ ([(8, 6, 0), (8, 6, 2)] : List (Nat × Nat ×
    Nat))) ++ (([(8, 6, 4), (8, 7, 1)] : List (Nat × Nat × Nat)) ++ (([(8, 7, 3), (8, 8, 0)] : List
    (Nat × Nat × Nat)) ++ ([(8, 8, 2), (8, 9, 1)] : List (Nat × Nat × Nat))))) ++ ((([(8, 10, 0), (9
    , 0, 1)] : List (Nat × Nat × Nat)) ++ (([(9, 0, 3), (9, 0, 5)] : List (Nat × Nat × Nat)) ++ ([(9
    , 0, 7), (9, 0, 9)] : List (Nat × Nat × Nat)))) ++ (([(9, 1, 0), (9, 1, 2)] : List (Nat × Nat ×
    Nat)) ++ (([(9, 1, 4), (9, 1, 6)] : List (Nat × Nat × Nat)) ++ ([(9, 1, 8), (9, 2, 1)] : List (
    Nat × Nat × Nat)))))) ++ (((([(9, 2, 3), (9, 2, 5)] : List (Nat × Nat × Nat)) ++ (([(9, 2, 7), (
    9, 3, 0)] : List (Nat × Nat × Nat)) ++ ([(9, 3, 2), (9, 3, 4)] : List (Nat × Nat × Nat)))) ++ ((
    [(9, 3, 6), (9, 4, 1)] : List (Nat × Nat × Nat)) ++ (([(9, 4, 3), (9, 4, 5)] : List (Nat × Nat ×
    Nat)) ++ ([(9, 5, 0), (9, 5, 2)] : List (Nat × Nat × Nat))))) ++ ((([(9, 5, 4), (9, 6, 1)] :
    List (Nat × Nat × Nat)) ++ (([(9, 6, 3), (9, 7, 0)] : List (Nat × Nat × Nat)) ++ ([(9, 7, 2), (9
    , 8, 1)] : List (Nat × Nat × Nat)))) ++ (([(9, 9, 0), (10, 0, 0)] : List (Nat × Nat × Nat)) ++ (
    ([(10, 0, 2), (10, 0, 4)] : List (Nat × Nat × Nat)) ++ ([(10, 0, 6), (10, 0, 8)] : List (Nat ×
    Nat × Nat)))))))) ++ (((((([(10, 1, 1), (10, 1, 3)] : List (Nat × Nat × Nat)) ++ ([(10, 1, 5), (
    10, 1, 7)] : List (Nat × Nat × Nat))) ++ (([(10, 2, 0), (10, 2, 2)] : List (Nat × Nat × Nat)) ++
    (([(10, 2, 4), (10, 2, 6)] : List (Nat × Nat × Nat)) ++ ([(10, 3, 1), (10, 3, 3)] : List (Nat ×
    Nat × Nat))))) ++ ((([(10, 3, 5), (10, 4, 0)] : List (Nat × Nat × Nat)) ++ (([(10, 4, 2), (10, 4
    , 4)] : List (Nat × Nat × Nat)) ++ ([(10, 5, 1), (10, 5, 3)] : List (Nat × Nat × Nat)))) ++ (([(
    10, 6, 0), (10, 6, 2)] : List (Nat × Nat × Nat)) ++ (([(10, 7, 1), (10, 8, 0)] : List (Nat × Nat
    × Nat)) ++ ([(11, 0, 1), (11, 0, 3)] : List (Nat × Nat × Nat)))))) ++ (((([(11, 0, 5), (11, 0, 7
    )] : List (Nat × Nat × Nat)) ++ ([(11, 1, 0), (11, 1, 2)] : List (Nat × Nat × Nat))) ++ (([(11,
    1, 4), (11, 1, 6)] : List (Nat × Nat × Nat)) ++ (([(11, 2, 1), (11, 2, 3)] : List (Nat × Nat ×
    Nat)) ++ ([(11, 2, 5), (11, 3, 0)] : List (Nat × Nat × Nat))))) ++ ((([(11, 3, 2), (11, 3, 4)] :
    List (Nat × Nat × Nat)) ++ (([(11, 4, 1), (11, 4, 3)] : List (Nat × Nat × Nat)) ++ ([(11, 5, 0),
    (11, 5, 2)] : List (Nat × Nat × Nat)))) ++ (([(11, 6, 1), (11, 7, 0)] : List (Nat × Nat × Nat))
    ++ (([(12, 0, 0), (12, 0, 2)] : List (Nat × Nat × Nat)) ++ ([(12, 0, 4), (12, 0, 6)] : List (Nat
    × Nat × Nat))))))) ++ ((((([(12, 1, 1), (12, 1, 3)] : List (Nat × Nat × Nat)) ++ ([(12, 1, 5), (
    12, 2, 0)] : List (Nat × Nat × Nat))) ++ (([(12, 2, 2), (12, 2, 4)] : List (Nat × Nat × Nat)) ++
    (([(12, 3, 1), (12, 3, 3)] : List (Nat × Nat × Nat)) ++ ([(12, 4, 0), (12, 4, 2)] : List (Nat ×
    Nat × Nat))))) ++ ((([(12, 5, 1), (12, 6, 0)] : List (Nat × Nat × Nat)) ++ (([(13, 0, 1), (13, 0
    , 3)] : List (Nat × Nat × Nat)) ++ ([(13, 0, 5), (13, 1, 0)] : List (Nat × Nat × Nat)))) ++ (([(
    13, 1, 2), (13, 1, 4)] : List (Nat × Nat × Nat)) ++ (([(13, 2, 1), (13, 2, 3)] : List (Nat × Nat
    × Nat)) ++ ([(13, 3, 0), (13, 3, 2)] : List (Nat × Nat × Nat)))))) ++ (((([(13, 4, 1), (13, 5, 0
    )] : List (Nat × Nat × Nat)) ++ (([(14, 0, 0), (14, 0, 2)] : List (Nat × Nat × Nat)) ++ ([(14, 0
    , 4), (14, 1, 1)] : List (Nat × Nat × Nat)))) ++ (([(14, 1, 3), (14, 2, 0)] : List (Nat × Nat ×
    Nat)) ++ (([(14, 2, 2), (14, 3, 1)] : List (Nat × Nat × Nat)) ++ ([(14, 4, 0), (15, 0, 1)] :
    List (Nat × Nat × Nat))))) ++ ((([(15, 0, 3), (15, 1, 0)] : List (Nat × Nat × Nat)) ++ (([(15, 1
    , 2), (15, 2, 1)] : List (Nat × Nat × Nat)) ++ ([(15, 3, 0), (16, 0, 0)] : List (Nat × Nat × Nat
    )))) ++ (([(16, 0, 2), (16, 1, 1)] : List (Nat × Nat × Nat)) ++ (([(16, 2, 0), (17, 0, 1)] :
    List (Nat × Nat × Nat)) ++ ([(17, 1, 0), (18, 0, 0)] : List (Nat × Nat × Nat))))))))))) from by
    decide +kernel]
  simp only [List.all_append, tin_0, tin_1, tin_2, tin_3, tin_4, tin_5, tin_6, tin_7, tin_8, tin_9,
    tin_10, tin_11, tin_12, tin_13, tin_14, tin_15, tin_16, tin_17, tin_18, tin_19, tin_20, tin_21,
    tin_22, tin_23, tin_24, tin_25, tin_26, tin_27, tin_28, tin_29, tin_30, tin_31, tin_32, tin_33,
    tin_34, tin_35, tin_36, tin_37, tin_38, tin_39, tin_40, tin_41, tin_42, tin_43, tin_44, tin_45,
    tin_46, tin_47, tin_48, tin_49, tin_50, tin_51, tin_52, tin_53, tin_54, tin_55, tin_56, tin_57,
    tin_58, tin_59, tin_60, tin_61, tin_62, tin_63, tin_64, tin_65, tin_66, tin_67, tin_68, tin_69,
    tin_70, tin_71, tin_72, tin_73, tin_74, tin_75, tin_76, tin_77, tin_78, tin_79, tin_80, tin_81,
    tin_82, tin_83, tin_84, tin_85, tin_86, tin_87, tin_88, tin_89, tin_90, tin_91, tin_92, tin_93,
    tin_94, tin_95, tin_96, tin_97, tin_98, tin_99, tin_100, tin_101, tin_102, tin_103, tin_104,
    tin_105, tin_106, tin_107, tin_108, tin_109, tin_110, tin_111, tin_112, tin_113, tin_114,
    tin_115, tin_116, tin_117, tin_118, tin_119, tin_120, tin_121, tin_122, tin_123, tin_124,
    tin_125, tin_126, tin_127, tin_128, tin_129, tin_130, tin_131, tin_132, tin_133, tin_134,
    tin_135, tin_136, tin_137, tin_138, tin_139, tin_140, tin_141, tin_142, tin_143, tin_144,
    tin_145, tin_146, tin_147, tin_148, tin_149, tin_150, tin_151, tin_152, tin_153, tin_154,
    tin_155, tin_156, tin_157, tin_158, tin_159, tin_160, tin_161, tin_162, tin_163, tin_164,
    tin_165, tin_166, tin_167, tin_168, tin_169, tin_170, tin_171, tin_172, tin_173, tin_174,
    tin_175, tin_176, tin_177, tin_178, tin_179, tin_180, tin_181, tin_182, tin_183, tin_184,
    tin_185, tin_186, tin_187, tin_188, tin_189, tin_190, tin_191, tin_192, tin_193, tin_194,
    tin_195, tin_196, tin_197, tin_198, tin_199, tin_200, tin_201, tin_202, tin_203, tin_204,
    tin_205, tin_206, tin_207, tin_208, tin_209, tin_210, tin_211, tin_212, tin_213, tin_214,
    tin_215, tin_216, tin_217, tin_218, tin_219, tin_220, tin_221, tin_222, tin_223, tin_224,
    tin_225, tin_226, tin_227, tin_228, tin_229, tin_230, tin_231, tin_232, tin_233, tin_234,
    tin_235, tin_236, tin_237, tin_238, tin_239, tin_240, tin_241, tin_242, tin_243, tin_244,
    tin_245, tin_246, tin_247, tin_248, tin_249, tin_250, tin_251, tin_252, tin_253, tin_254,
    tin_255, tin_256, tin_257, tin_258, tin_259, tin_260, tin_261, tin_262, tin_263, tin_264,
    tin_265, tin_266, tin_267, tin_268, tin_269, tin_270, tin_271, tin_272, tin_273, tin_274,
    tin_275, tin_276, tin_277, tin_278, tin_279, tin_280, tin_281, tin_282, tin_283, tin_284,
    tin_285, tin_286, tin_287, tin_288, tin_289, tin_290, tin_291, tin_292, tin_293, tin_294,
    tin_295, tin_296, tin_297, tin_298, tin_299, tin_300, tin_301, tin_302, tin_303, tin_304,
    tin_305, tin_306, tin_307, tin_308, tin_309, tin_310, tin_311, tin_312, tin_313, tin_314,
    tin_315, tin_316, tin_317, tin_318, tin_319, tin_320, tin_321, tin_322, tin_323, tin_324,
    tin_325, tin_326, tin_327, tin_328, tin_329, tin_330, tin_331, tin_332, tin_333, tin_334,
    tin_335, tin_336, tin_337, tin_338, tin_339, tin_340, tin_341, tin_342, tin_343, tin_344,
    tin_345, tin_346, tin_347, tin_348, tin_349, tin_350, tin_351, tin_352, tin_353, tin_354,
    tin_355, tin_356, Bool.and_self]

theorem pall0 : sjsuHD.pAll 0 (sjsuSq 0) (sjsuIv 0) (sjsuPp 0) = true := by
  simp only [HData.pAll, Bool.and_eq_true]
  refine ⟨⟨⟨pb_0, ?_⟩, pm_0⟩, ?_⟩
  · rw [List.all_eq_true]
    intro k hk
    rw [show List.range (sjsuHD.Nmax + 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18] from by decide] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl
    exacts [rfl, rfl, rfl, pw_0_3, pw_0_4, pw_0_5, pw_0_6, pw_0_7, pw_0_8, pw_0_9, pw_0_10, pw_0_11,
      pw_0_12, pw_0_13, pw_0_14, pw_0_15, pw_0_16, pw_0_17, pw_0_18]
  · rw [List.all_eq_true]
    intro k hk
    rw [show List.range (2 * sjsuHD.M + 2) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19] from by decide] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [rfl, rfl, rfl, pn_0_3, pn_0_4, pn_0_5, pn_0_6, pn_0_7, pn_0_8, pn_0_9, pn_0_10, pn_0_11,
      pn_0_12, pn_0_13, pn_0_14, pn_0_15, pn_0_16, pn_0_17, pn_0_18, pn_0_19]

theorem pall1 : sjsuHD.pAll 1 (sjsuSq 1) (sjsuIv 1) (sjsuPp 1) = true := by
  simp only [HData.pAll, Bool.and_eq_true]
  refine ⟨⟨⟨pb_1, ?_⟩, pm_1⟩, ?_⟩
  · rw [List.all_eq_true]
    intro k hk
    rw [show List.range (sjsuHD.Nmax + 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18] from by decide] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl
    exacts [rfl, rfl, rfl, pw_1_3, pw_1_4, pw_1_5, pw_1_6, pw_1_7, pw_1_8, pw_1_9, pw_1_10, pw_1_11,
      pw_1_12, pw_1_13, pw_1_14, pw_1_15, pw_1_16, pw_1_17, pw_1_18]
  · rw [List.all_eq_true]
    intro k hk
    rw [show List.range (2 * sjsuHD.M + 2) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19] from by decide] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [rfl, rfl, rfl, pn_1_3, pn_1_4, pn_1_5, pn_1_6, pn_1_7, pn_1_8, pn_1_9, pn_1_10, pn_1_11,
      pn_1_12, pn_1_13, pn_1_14, pn_1_15, pn_1_16, pn_1_17, pn_1_18, pn_1_19]

theorem pall2 : sjsuHD.pAll 2 (sjsuSq 2) (sjsuIv 2) (sjsuPp 2) = true := by
  simp only [HData.pAll, Bool.and_eq_true]
  refine ⟨⟨⟨pb_2, ?_⟩, pm_2⟩, ?_⟩
  · rw [List.all_eq_true]
    intro k hk
    rw [show List.range (sjsuHD.Nmax + 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18] from by decide] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl
    exacts [rfl, rfl, rfl, pw_2_3, pw_2_4, pw_2_5, pw_2_6, pw_2_7, pw_2_8, pw_2_9, pw_2_10, pw_2_11,
      pw_2_12, pw_2_13, pw_2_14, pw_2_15, pw_2_16, pw_2_17, pw_2_18]
  · rw [List.all_eq_true]
    intro k hk
    rw [show List.range (2 * sjsuHD.M + 2) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
        16, 17, 18, 19] from by decide] at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [rfl, rfl, rfl, pn_2_3, pn_2_4, pn_2_5, pn_2_6, pn_2_7, pn_2_8, pn_2_9, pn_2_10, pn_2_11,
      pn_2_12, pn_2_13, pn_2_14, pn_2_15, pn_2_16, pn_2_17, pn_2_18, pn_2_19]

theorem vb_0_0 : sjsuHD.vBlock 0 0 (sjsuUp 0 0) (sjsuVp 0 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 0 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] from
        by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_0_0_0, vu_0_0_1, vu_0_0_2, vu_0_0_3, vu_0_0_4, vu_0_0_5, vu_0_0_6, vu_0_0_7, vu_0_0_8
      , vu_0_0_9, vu_0_0_10, vu_0_0_11, vu_0_0_12, vu_0_0_13, vu_0_0_14, vu_0_0_15, vu_0_0_16,
      vu_0_0_17, vu_0_0_18]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_0_0_0, vv_0_0_1, vv_0_0_2, vv_0_0_3, vv_0_0_4, vv_0_0_5, vv_0_0_6, vv_0_0_7, vv_0_0_8
      , vv_0_0_9]

theorem vb_0_1 : sjsuHD.vBlock 0 1 (sjsuUp 0 1) (sjsuVp 0 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 0 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] from
        by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_0_1_0, vu_0_1_1, vu_0_1_2, vu_0_1_3, vu_0_1_4, vu_0_1_5, vu_0_1_6, vu_0_1_7, vu_0_1_8
      , vu_0_1_9, vu_0_1_10, vu_0_1_11, vu_0_1_12, vu_0_1_13, vu_0_1_14, vu_0_1_15, vu_0_1_16,
      vu_0_1_17, vu_0_1_18]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_0_1_0, vv_0_1_1, vv_0_1_2, vv_0_1_3, vv_0_1_4, vv_0_1_5, vv_0_1_6, vv_0_1_7, vv_0_1_8
      ]

theorem vb_0_2 : sjsuHD.vBlock 0 2 (sjsuUp 0 2) (sjsuVp 0 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 0 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] from
        by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_0_2_0, vu_0_2_1, vu_0_2_2, vu_0_2_3, vu_0_2_4, vu_0_2_5, vu_0_2_6, vu_0_2_7, vu_0_2_8
      , vu_0_2_9, vu_0_2_10, vu_0_2_11, vu_0_2_12, vu_0_2_13, vu_0_2_14, vu_0_2_15, vu_0_2_16,
      vu_0_2_17, vu_0_2_18]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_0_2_0, vv_0_2_1, vv_0_2_2, vv_0_2_3, vv_0_2_4, vv_0_2_5, vv_0_2_6, vv_0_2_7]

theorem vb_0_3 : sjsuHD.vBlock 0 3 (sjsuUp 0 3) (sjsuVp 0 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 0 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] from
        by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_0_3_0, vu_0_3_1, vu_0_3_2, vu_0_3_3, vu_0_3_4, vu_0_3_5, vu_0_3_6, vu_0_3_7, vu_0_3_8
      , vu_0_3_9, vu_0_3_10, vu_0_3_11, vu_0_3_12, vu_0_3_13, vu_0_3_14, vu_0_3_15, vu_0_3_16,
      vu_0_3_17, vu_0_3_18]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_0_3_0, vv_0_3_1, vv_0_3_2, vv_0_3_3, vv_0_3_4, vv_0_3_5, vv_0_3_6]

theorem vb_0_4 : sjsuHD.vBlock 0 4 (sjsuUp 0 4) (sjsuVp 0 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 0 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] from
        by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_0_4_0, vu_0_4_1, vu_0_4_2, vu_0_4_3, vu_0_4_4, vu_0_4_5, vu_0_4_6, vu_0_4_7, vu_0_4_8
      , vu_0_4_9, vu_0_4_10, vu_0_4_11, vu_0_4_12, vu_0_4_13, vu_0_4_14, vu_0_4_15, vu_0_4_16,
      vu_0_4_17, vu_0_4_18]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_0_4_0, vv_0_4_1, vv_0_4_2, vv_0_4_3, vv_0_4_4, vv_0_4_5]

theorem vb_0_5 : sjsuHD.vBlock 0 5 (sjsuUp 0 5) (sjsuVp 0 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 0 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] from
        by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_0_5_0, vu_0_5_1, vu_0_5_2, vu_0_5_3, vu_0_5_4, vu_0_5_5, vu_0_5_6, vu_0_5_7, vu_0_5_8
      , vu_0_5_9, vu_0_5_10, vu_0_5_11, vu_0_5_12, vu_0_5_13, vu_0_5_14, vu_0_5_15, vu_0_5_16,
      vu_0_5_17, vu_0_5_18]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_0_5_0, vv_0_5_1, vv_0_5_2, vv_0_5_3, vv_0_5_4]

theorem vb_0_6 : sjsuHD.vBlock 0 6 (sjsuUp 0 6) (sjsuVp 0 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 0 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] from
        by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_0_6_0, vu_0_6_1, vu_0_6_2, vu_0_6_3, vu_0_6_4, vu_0_6_5, vu_0_6_6, vu_0_6_7, vu_0_6_8
      , vu_0_6_9, vu_0_6_10, vu_0_6_11, vu_0_6_12, vu_0_6_13, vu_0_6_14, vu_0_6_15, vu_0_6_16,
      vu_0_6_17, vu_0_6_18]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_0_6_0, vv_0_6_1, vv_0_6_2, vv_0_6_3]

theorem vb_0_7 : sjsuHD.vBlock 0 7 (sjsuUp 0 7) (sjsuVp 0 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 0 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] from
        by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_0_7_0, vu_0_7_1, vu_0_7_2, vu_0_7_3, vu_0_7_4, vu_0_7_5, vu_0_7_6, vu_0_7_7, vu_0_7_8
      , vu_0_7_9, vu_0_7_10, vu_0_7_11, vu_0_7_12, vu_0_7_13, vu_0_7_14, vu_0_7_15, vu_0_7_16,
      vu_0_7_17, vu_0_7_18]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_0_7_0, vv_0_7_1, vv_0_7_2]

theorem vb_0_8 : sjsuHD.vBlock 0 8 (sjsuUp 0 8) (sjsuVp 0 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 0 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] from
        by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_0_8_0, vu_0_8_1, vu_0_8_2, vu_0_8_3, vu_0_8_4, vu_0_8_5, vu_0_8_6, vu_0_8_7, vu_0_8_8
      , vu_0_8_9, vu_0_8_10, vu_0_8_11, vu_0_8_12, vu_0_8_13, vu_0_8_14, vu_0_8_15, vu_0_8_16,
      vu_0_8_17, vu_0_8_18]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_0_8_0, vv_0_8_1]

theorem vb_0_9 : sjsuHD.vBlock 0 9 (sjsuUp 0 9) (sjsuVp 0 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 0 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] from
        by decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vu_0_9_0, vu_0_9_1, vu_0_9_2, vu_0_9_3, vu_0_9_4, vu_0_9_5, vu_0_9_6, vu_0_9_7, vu_0_9_8
      , vu_0_9_9, vu_0_9_10, vu_0_9_11, vu_0_9_12, vu_0_9_13, vu_0_9_14, vu_0_9_15, vu_0_9_16,
      vu_0_9_17, vu_0_9_18]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_0_9_0]

theorem vb_1_0 : sjsuHD.vBlock 1 0 (sjsuUp 1 0) (sjsuVp 1 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    exacts [vu_1_0_0, vu_1_0_1, vu_1_0_2, vu_1_0_3, vu_1_0_4, vu_1_0_5, vu_1_0_6, vu_1_0_7, vu_1_0_8
      , vu_1_0_9, vu_1_0_10, vu_1_0_11, vu_1_0_12, vu_1_0_13, vu_1_0_14, vu_1_0_15, vu_1_0_16,
      vu_1_0_17]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_1_0_0, vv_1_0_1, vv_1_0_2, vv_1_0_3, vv_1_0_4, vv_1_0_5, vv_1_0_6, vv_1_0_7, vv_1_0_8
      , vv_1_0_9]

theorem vb_1_1 : sjsuHD.vBlock 1 1 (sjsuUp 1 1) (sjsuVp 1 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    exacts [vu_1_1_0, vu_1_1_1, vu_1_1_2, vu_1_1_3, vu_1_1_4, vu_1_1_5, vu_1_1_6, vu_1_1_7, vu_1_1_8
      , vu_1_1_9, vu_1_1_10, vu_1_1_11, vu_1_1_12, vu_1_1_13, vu_1_1_14, vu_1_1_15, vu_1_1_16,
      vu_1_1_17]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_1_1_0, vv_1_1_1, vv_1_1_2, vv_1_1_3, vv_1_1_4, vv_1_1_5, vv_1_1_6, vv_1_1_7, vv_1_1_8
      ]

theorem vb_1_2 : sjsuHD.vBlock 1 2 (sjsuUp 1 2) (sjsuVp 1 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    exacts [vu_1_2_0, vu_1_2_1, vu_1_2_2, vu_1_2_3, vu_1_2_4, vu_1_2_5, vu_1_2_6, vu_1_2_7, vu_1_2_8
      , vu_1_2_9, vu_1_2_10, vu_1_2_11, vu_1_2_12, vu_1_2_13, vu_1_2_14, vu_1_2_15, vu_1_2_16,
      vu_1_2_17]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_1_2_0, vv_1_2_1, vv_1_2_2, vv_1_2_3, vv_1_2_4, vv_1_2_5, vv_1_2_6, vv_1_2_7]

theorem vb_1_3 : sjsuHD.vBlock 1 3 (sjsuUp 1 3) (sjsuVp 1 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    exacts [vu_1_3_0, vu_1_3_1, vu_1_3_2, vu_1_3_3, vu_1_3_4, vu_1_3_5, vu_1_3_6, vu_1_3_7, vu_1_3_8
      , vu_1_3_9, vu_1_3_10, vu_1_3_11, vu_1_3_12, vu_1_3_13, vu_1_3_14, vu_1_3_15, vu_1_3_16,
      vu_1_3_17]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_1_3_0, vv_1_3_1, vv_1_3_2, vv_1_3_3, vv_1_3_4, vv_1_3_5, vv_1_3_6]

theorem vb_1_4 : sjsuHD.vBlock 1 4 (sjsuUp 1 4) (sjsuVp 1 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    exacts [vu_1_4_0, vu_1_4_1, vu_1_4_2, vu_1_4_3, vu_1_4_4, vu_1_4_5, vu_1_4_6, vu_1_4_7, vu_1_4_8
      , vu_1_4_9, vu_1_4_10, vu_1_4_11, vu_1_4_12, vu_1_4_13, vu_1_4_14, vu_1_4_15, vu_1_4_16,
      vu_1_4_17]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_1_4_0, vv_1_4_1, vv_1_4_2, vv_1_4_3, vv_1_4_4, vv_1_4_5]

theorem vb_1_5 : sjsuHD.vBlock 1 5 (sjsuUp 1 5) (sjsuVp 1 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    exacts [vu_1_5_0, vu_1_5_1, vu_1_5_2, vu_1_5_3, vu_1_5_4, vu_1_5_5, vu_1_5_6, vu_1_5_7, vu_1_5_8
      , vu_1_5_9, vu_1_5_10, vu_1_5_11, vu_1_5_12, vu_1_5_13, vu_1_5_14, vu_1_5_15, vu_1_5_16,
      vu_1_5_17]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_1_5_0, vv_1_5_1, vv_1_5_2, vv_1_5_3, vv_1_5_4]

theorem vb_1_6 : sjsuHD.vBlock 1 6 (sjsuUp 1 6) (sjsuVp 1 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    exacts [vu_1_6_0, vu_1_6_1, vu_1_6_2, vu_1_6_3, vu_1_6_4, vu_1_6_5, vu_1_6_6, vu_1_6_7, vu_1_6_8
      , vu_1_6_9, vu_1_6_10, vu_1_6_11, vu_1_6_12, vu_1_6_13, vu_1_6_14, vu_1_6_15, vu_1_6_16,
      vu_1_6_17]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_1_6_0, vv_1_6_1, vv_1_6_2, vv_1_6_3]

theorem vb_1_7 : sjsuHD.vBlock 1 7 (sjsuUp 1 7) (sjsuVp 1 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    exacts [vu_1_7_0, vu_1_7_1, vu_1_7_2, vu_1_7_3, vu_1_7_4, vu_1_7_5, vu_1_7_6, vu_1_7_7, vu_1_7_8
      , vu_1_7_9, vu_1_7_10, vu_1_7_11, vu_1_7_12, vu_1_7_13, vu_1_7_14, vu_1_7_15, vu_1_7_16,
      vu_1_7_17]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_1_7_0, vv_1_7_1, vv_1_7_2]

theorem vb_1_8 : sjsuHD.vBlock 1 8 (sjsuUp 1 8) (sjsuVp 1 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    exacts [vu_1_8_0, vu_1_8_1, vu_1_8_2, vu_1_8_3, vu_1_8_4, vu_1_8_5, vu_1_8_6, vu_1_8_7, vu_1_8_8
      , vu_1_8_9, vu_1_8_10, vu_1_8_11, vu_1_8_12, vu_1_8_13, vu_1_8_14, vu_1_8_15, vu_1_8_16,
      vu_1_8_17]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_1_8_0, vv_1_8_1]

theorem vb_1_9 : sjsuHD.vBlock 1 9 (sjsuUp 1 9) (sjsuVp 1 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 1 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    exacts [vu_1_9_0, vu_1_9_1, vu_1_9_2, vu_1_9_3, vu_1_9_4, vu_1_9_5, vu_1_9_6, vu_1_9_7, vu_1_9_8
      , vu_1_9_9, vu_1_9_10, vu_1_9_11, vu_1_9_12, vu_1_9_13, vu_1_9_14, vu_1_9_15, vu_1_9_16,
      vu_1_9_17]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_1_9_0]

theorem vb_2_0 : sjsuHD.vBlock 2 0 (sjsuUp 2 0) (sjsuVp 2 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 2 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    exacts [vu_2_0_0, vu_2_0_1, vu_2_0_2, vu_2_0_3, vu_2_0_4, vu_2_0_5, vu_2_0_6, vu_2_0_7, vu_2_0_8
      , vu_2_0_9, vu_2_0_10, vu_2_0_11, vu_2_0_12, vu_2_0_13, vu_2_0_14, vu_2_0_15, vu_2_0_16]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_2_0_0, vv_2_0_1, vv_2_0_2, vv_2_0_3, vv_2_0_4, vv_2_0_5, vv_2_0_6, vv_2_0_7, vv_2_0_8
      , vv_2_0_9]

theorem vb_2_1 : sjsuHD.vBlock 2 1 (sjsuUp 2 1) (sjsuVp 2 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 2 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    exacts [vu_2_1_0, vu_2_1_1, vu_2_1_2, vu_2_1_3, vu_2_1_4, vu_2_1_5, vu_2_1_6, vu_2_1_7, vu_2_1_8
      , vu_2_1_9, vu_2_1_10, vu_2_1_11, vu_2_1_12, vu_2_1_13, vu_2_1_14, vu_2_1_15, vu_2_1_16]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_2_1_0, vv_2_1_1, vv_2_1_2, vv_2_1_3, vv_2_1_4, vv_2_1_5, vv_2_1_6, vv_2_1_7, vv_2_1_8
      ]

theorem vb_2_2 : sjsuHD.vBlock 2 2 (sjsuUp 2 2) (sjsuVp 2 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 2 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    exacts [vu_2_2_0, vu_2_2_1, vu_2_2_2, vu_2_2_3, vu_2_2_4, vu_2_2_5, vu_2_2_6, vu_2_2_7, vu_2_2_8
      , vu_2_2_9, vu_2_2_10, vu_2_2_11, vu_2_2_12, vu_2_2_13, vu_2_2_14, vu_2_2_15, vu_2_2_16]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_2_2_0, vv_2_2_1, vv_2_2_2, vv_2_2_3, vv_2_2_4, vv_2_2_5, vv_2_2_6, vv_2_2_7]

theorem vb_2_3 : sjsuHD.vBlock 2 3 (sjsuUp 2 3) (sjsuVp 2 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 2 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    exacts [vu_2_3_0, vu_2_3_1, vu_2_3_2, vu_2_3_3, vu_2_3_4, vu_2_3_5, vu_2_3_6, vu_2_3_7, vu_2_3_8
      , vu_2_3_9, vu_2_3_10, vu_2_3_11, vu_2_3_12, vu_2_3_13, vu_2_3_14, vu_2_3_15, vu_2_3_16]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_2_3_0, vv_2_3_1, vv_2_3_2, vv_2_3_3, vv_2_3_4, vv_2_3_5, vv_2_3_6]

theorem vb_2_4 : sjsuHD.vBlock 2 4 (sjsuUp 2 4) (sjsuVp 2 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 2 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    exacts [vu_2_4_0, vu_2_4_1, vu_2_4_2, vu_2_4_3, vu_2_4_4, vu_2_4_5, vu_2_4_6, vu_2_4_7, vu_2_4_8
      , vu_2_4_9, vu_2_4_10, vu_2_4_11, vu_2_4_12, vu_2_4_13, vu_2_4_14, vu_2_4_15, vu_2_4_16]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_2_4_0, vv_2_4_1, vv_2_4_2, vv_2_4_3, vv_2_4_4, vv_2_4_5]

theorem vb_2_5 : sjsuHD.vBlock 2 5 (sjsuUp 2 5) (sjsuVp 2 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 2 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    exacts [vu_2_5_0, vu_2_5_1, vu_2_5_2, vu_2_5_3, vu_2_5_4, vu_2_5_5, vu_2_5_6, vu_2_5_7, vu_2_5_8
      , vu_2_5_9, vu_2_5_10, vu_2_5_11, vu_2_5_12, vu_2_5_13, vu_2_5_14, vu_2_5_15, vu_2_5_16]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_2_5_0, vv_2_5_1, vv_2_5_2, vv_2_5_3, vv_2_5_4]

theorem vb_2_6 : sjsuHD.vBlock 2 6 (sjsuUp 2 6) (sjsuVp 2 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 2 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    exacts [vu_2_6_0, vu_2_6_1, vu_2_6_2, vu_2_6_3, vu_2_6_4, vu_2_6_5, vu_2_6_6, vu_2_6_7, vu_2_6_8
      , vu_2_6_9, vu_2_6_10, vu_2_6_11, vu_2_6_12, vu_2_6_13, vu_2_6_14, vu_2_6_15, vu_2_6_16]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_2_6_0, vv_2_6_1, vv_2_6_2, vv_2_6_3]

theorem vb_2_7 : sjsuHD.vBlock 2 7 (sjsuUp 2 7) (sjsuVp 2 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 2 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    exacts [vu_2_7_0, vu_2_7_1, vu_2_7_2, vu_2_7_3, vu_2_7_4, vu_2_7_5, vu_2_7_6, vu_2_7_7, vu_2_7_8
      , vu_2_7_9, vu_2_7_10, vu_2_7_11, vu_2_7_12, vu_2_7_13, vu_2_7_14, vu_2_7_15, vu_2_7_16]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_2_7_0, vv_2_7_1, vv_2_7_2]

theorem vb_2_8 : sjsuHD.vBlock 2 8 (sjsuUp 2 8) (sjsuVp 2 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 2 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    exacts [vu_2_8_0, vu_2_8_1, vu_2_8_2, vu_2_8_3, vu_2_8_4, vu_2_8_5, vu_2_8_6, vu_2_8_7, vu_2_8_8
      , vu_2_8_9, vu_2_8_10, vu_2_8_11, vu_2_8_12, vu_2_8_13, vu_2_8_14, vu_2_8_15, vu_2_8_16]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_2_8_0, vv_2_8_1]

theorem vb_2_9 : sjsuHD.vBlock 2 9 (sjsuUp 2 9) (sjsuVp 2 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 2 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    exacts [vu_2_9_0, vu_2_9_1, vu_2_9_2, vu_2_9_3, vu_2_9_4, vu_2_9_5, vu_2_9_6, vu_2_9_7, vu_2_9_8
      , vu_2_9_9, vu_2_9_10, vu_2_9_11, vu_2_9_12, vu_2_9_13, vu_2_9_14, vu_2_9_15, vu_2_9_16]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_2_9_0]

theorem vb_3_0 : sjsuHD.vBlock 3 0 (sjsuUp 3 0) (sjsuVp 3 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 3 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    exacts [vu_3_0_0, vu_3_0_1, vu_3_0_2, vu_3_0_3, vu_3_0_4, vu_3_0_5, vu_3_0_6, vu_3_0_7, vu_3_0_8
      , vu_3_0_9, vu_3_0_10, vu_3_0_11, vu_3_0_12, vu_3_0_13, vu_3_0_14, vu_3_0_15]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_3_0_0, vv_3_0_1, vv_3_0_2, vv_3_0_3, vv_3_0_4, vv_3_0_5, vv_3_0_6, vv_3_0_7, vv_3_0_8
      , vv_3_0_9]

theorem vb_3_1 : sjsuHD.vBlock 3 1 (sjsuUp 3 1) (sjsuVp 3 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 3 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    exacts [vu_3_1_0, vu_3_1_1, vu_3_1_2, vu_3_1_3, vu_3_1_4, vu_3_1_5, vu_3_1_6, vu_3_1_7, vu_3_1_8
      , vu_3_1_9, vu_3_1_10, vu_3_1_11, vu_3_1_12, vu_3_1_13, vu_3_1_14, vu_3_1_15]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_3_1_0, vv_3_1_1, vv_3_1_2, vv_3_1_3, vv_3_1_4, vv_3_1_5, vv_3_1_6, vv_3_1_7, vv_3_1_8
      ]

theorem vb_3_2 : sjsuHD.vBlock 3 2 (sjsuUp 3 2) (sjsuVp 3 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 3 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    exacts [vu_3_2_0, vu_3_2_1, vu_3_2_2, vu_3_2_3, vu_3_2_4, vu_3_2_5, vu_3_2_6, vu_3_2_7, vu_3_2_8
      , vu_3_2_9, vu_3_2_10, vu_3_2_11, vu_3_2_12, vu_3_2_13, vu_3_2_14, vu_3_2_15]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_3_2_0, vv_3_2_1, vv_3_2_2, vv_3_2_3, vv_3_2_4, vv_3_2_5, vv_3_2_6, vv_3_2_7]

theorem vb_3_3 : sjsuHD.vBlock 3 3 (sjsuUp 3 3) (sjsuVp 3 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 3 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    exacts [vu_3_3_0, vu_3_3_1, vu_3_3_2, vu_3_3_3, vu_3_3_4, vu_3_3_5, vu_3_3_6, vu_3_3_7, vu_3_3_8
      , vu_3_3_9, vu_3_3_10, vu_3_3_11, vu_3_3_12, vu_3_3_13, vu_3_3_14, vu_3_3_15]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_3_3_0, vv_3_3_1, vv_3_3_2, vv_3_3_3, vv_3_3_4, vv_3_3_5, vv_3_3_6]

theorem vb_3_4 : sjsuHD.vBlock 3 4 (sjsuUp 3 4) (sjsuVp 3 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 3 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    exacts [vu_3_4_0, vu_3_4_1, vu_3_4_2, vu_3_4_3, vu_3_4_4, vu_3_4_5, vu_3_4_6, vu_3_4_7, vu_3_4_8
      , vu_3_4_9, vu_3_4_10, vu_3_4_11, vu_3_4_12, vu_3_4_13, vu_3_4_14, vu_3_4_15]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_3_4_0, vv_3_4_1, vv_3_4_2, vv_3_4_3, vv_3_4_4, vv_3_4_5]

theorem vb_3_5 : sjsuHD.vBlock 3 5 (sjsuUp 3 5) (sjsuVp 3 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 3 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    exacts [vu_3_5_0, vu_3_5_1, vu_3_5_2, vu_3_5_3, vu_3_5_4, vu_3_5_5, vu_3_5_6, vu_3_5_7, vu_3_5_8
      , vu_3_5_9, vu_3_5_10, vu_3_5_11, vu_3_5_12, vu_3_5_13, vu_3_5_14, vu_3_5_15]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_3_5_0, vv_3_5_1, vv_3_5_2, vv_3_5_3, vv_3_5_4]

theorem vb_3_6 : sjsuHD.vBlock 3 6 (sjsuUp 3 6) (sjsuVp 3 6) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 3 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    exacts [vu_3_6_0, vu_3_6_1, vu_3_6_2, vu_3_6_3, vu_3_6_4, vu_3_6_5, vu_3_6_6, vu_3_6_7, vu_3_6_8
      , vu_3_6_9, vu_3_6_10, vu_3_6_11, vu_3_6_12, vu_3_6_13, vu_3_6_14, vu_3_6_15]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 6) = [0, 1, 2, 3] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl
    exacts [vv_3_6_0, vv_3_6_1, vv_3_6_2, vv_3_6_3]

theorem vb_3_7 : sjsuHD.vBlock 3 7 (sjsuUp 3 7) (sjsuVp 3 7) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 3 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    exacts [vu_3_7_0, vu_3_7_1, vu_3_7_2, vu_3_7_3, vu_3_7_4, vu_3_7_5, vu_3_7_6, vu_3_7_7, vu_3_7_8
      , vu_3_7_9, vu_3_7_10, vu_3_7_11, vu_3_7_12, vu_3_7_13, vu_3_7_14, vu_3_7_15]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 7) = [0, 1, 2] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl
    exacts [vv_3_7_0, vv_3_7_1, vv_3_7_2]

theorem vb_3_8 : sjsuHD.vBlock 3 8 (sjsuUp 3 8) (sjsuVp 3 8) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 3 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    exacts [vu_3_8_0, vu_3_8_1, vu_3_8_2, vu_3_8_3, vu_3_8_4, vu_3_8_5, vu_3_8_6, vu_3_8_7, vu_3_8_8
      , vu_3_8_9, vu_3_8_10, vu_3_8_11, vu_3_8_12, vu_3_8_13, vu_3_8_14, vu_3_8_15]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 8) = [0, 1] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl
    exacts [vv_3_8_0, vv_3_8_1]

theorem vb_3_9 : sjsuHD.vBlock 3 9 (sjsuUp 3 9) (sjsuVp 3 9) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 3 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    exacts [vu_3_9_0, vu_3_9_1, vu_3_9_2, vu_3_9_3, vu_3_9_4, vu_3_9_5, vu_3_9_6, vu_3_9_7, vu_3_9_8
      , vu_3_9_9, vu_3_9_10, vu_3_9_11, vu_3_9_12, vu_3_9_13, vu_3_9_14, vu_3_9_15]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 9) = [0] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl
    exacts [vv_3_9_0]

theorem vb_4_0 : sjsuHD.vBlock 4 0 (sjsuUp 4 0) (sjsuVp 4 0) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 4 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    exacts [vu_4_0_0, vu_4_0_1, vu_4_0_2, vu_4_0_3, vu_4_0_4, vu_4_0_5, vu_4_0_6, vu_4_0_7, vu_4_0_8
      , vu_4_0_9, vu_4_0_10, vu_4_0_11, vu_4_0_12, vu_4_0_13, vu_4_0_14]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 0) = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_4_0_0, vv_4_0_1, vv_4_0_2, vv_4_0_3, vv_4_0_4, vv_4_0_5, vv_4_0_6, vv_4_0_7, vv_4_0_8
      , vv_4_0_9]

theorem vb_4_1 : sjsuHD.vBlock 4 1 (sjsuUp 4 1) (sjsuVp 4 1) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 4 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    exacts [vu_4_1_0, vu_4_1_1, vu_4_1_2, vu_4_1_3, vu_4_1_4, vu_4_1_5, vu_4_1_6, vu_4_1_7, vu_4_1_8
      , vu_4_1_9, vu_4_1_10, vu_4_1_11, vu_4_1_12, vu_4_1_13, vu_4_1_14]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 1) = [0, 1, 2, 3, 4, 5, 6, 7, 8] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_4_1_0, vv_4_1_1, vv_4_1_2, vv_4_1_3, vv_4_1_4, vv_4_1_5, vv_4_1_6, vv_4_1_7, vv_4_1_8
      ]

theorem vb_4_2 : sjsuHD.vBlock 4 2 (sjsuUp 4 2) (sjsuVp 4 2) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 4 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    exacts [vu_4_2_0, vu_4_2_1, vu_4_2_2, vu_4_2_3, vu_4_2_4, vu_4_2_5, vu_4_2_6, vu_4_2_7, vu_4_2_8
      , vu_4_2_9, vu_4_2_10, vu_4_2_11, vu_4_2_12, vu_4_2_13, vu_4_2_14]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 2) = [0, 1, 2, 3, 4, 5, 6, 7] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_4_2_0, vv_4_2_1, vv_4_2_2, vv_4_2_3, vv_4_2_4, vv_4_2_5, vv_4_2_6, vv_4_2_7]

theorem vb_4_3 : sjsuHD.vBlock 4 3 (sjsuUp 4 3) (sjsuVp 4 3) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 4 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    exacts [vu_4_3_0, vu_4_3_1, vu_4_3_2, vu_4_3_3, vu_4_3_4, vu_4_3_5, vu_4_3_6, vu_4_3_7, vu_4_3_8
      , vu_4_3_9, vu_4_3_10, vu_4_3_11, vu_4_3_12, vu_4_3_13, vu_4_3_14]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 3) = [0, 1, 2, 3, 4, 5, 6] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_4_3_0, vv_4_3_1, vv_4_3_2, vv_4_3_3, vv_4_3_4, vv_4_3_5, vv_4_3_6]

theorem vb_4_4 : sjsuHD.vBlock 4 4 (sjsuUp 4 4) (sjsuVp 4 4) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 4 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    exacts [vu_4_4_0, vu_4_4_1, vu_4_4_2, vu_4_4_3, vu_4_4_4, vu_4_4_5, vu_4_4_6, vu_4_4_7, vu_4_4_8
      , vu_4_4_9, vu_4_4_10, vu_4_4_11, vu_4_4_12, vu_4_4_13, vu_4_4_14]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 4) = [0, 1, 2, 3, 4, 5] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [vv_4_4_0, vv_4_4_1, vv_4_4_2, vv_4_4_3, vv_4_4_4, vv_4_4_5]

theorem vb_4_5 : sjsuHD.vBlock 4 5 (sjsuUp 4 5) (sjsuVp 4 5) = true := by
  simp only [HData.vBlock, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro n2 hn2
    rw [show sjsuHD.n2s 4 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] from by
        decide +kernel] at hn2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn2
    rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    exacts [vu_4_5_0, vu_4_5_1, vu_4_5_2, vu_4_5_3, vu_4_5_4, vu_4_5_5, vu_4_5_6, vu_4_5_7, vu_4_5_8
      , vu_4_5_9, vu_4_5_10, vu_4_5_11, vu_4_5_12, vu_4_5_13, vu_4_5_14]
  · rw [List.all_eq_true]
    intro m2 hm2
    rw [show List.range (sjsuHD.M + 1 - 5) = [0, 1, 2, 3, 4] from by decide] at hm2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    rcases hm2 with rfl | rfl | rfl | rfl | rfl
    exacts [vv_4_5_0, vv_4_5_1, vv_4_5_2, vv_4_5_3, vv_4_5_4]


end KAM.EffectiveStability.SJSU

end
