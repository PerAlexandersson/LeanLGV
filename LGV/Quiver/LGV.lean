/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Quiver.Collision

/-!
# Weighted Lindström--Gessel--Viennot cancellation for ranked quivers
-/

namespace LGV

open Quiver
open scoped BigOperators

noncomputable section

universe u v

namespace RankedQuiverNetwork

variable {R : Type u} {V : Type v} {n : ℕ}
variable [Quiver V] [Fintype V] [DecidableEq V]
variable [∀ a b : V, Fintype (a ⟶ b)]

/-- The canonical involution on intersecting signed path families. -/
def firstCollisionSwap [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n)) :
    {family : N.toFinitePathNetwork.SignedPathFamily //
      ¬N.SignedVertexDisjoint family} →
    {family : N.toFinitePathNetwork.SignedPathFamily //
      ¬N.SignedVertexDisjoint family} :=
  fun b => ⟨N.swapAtFirstCollision b.1 b.2,
    N.swapAtFirstCollision_not_signedVertexDisjoint b.1 b.2⟩

theorem signedFamilyWeight_swapAtFirstCollision [CommRing R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.toFinitePathNetwork.signedFamilyWeight
        (N.swapAtFirstCollision family hbad) =
      -N.toFinitePathNetwork.signedFamilyWeight family := by
  let i := N.firstCollisionLeft family hbad
  let j := N.firstCollisionRight family hbad
  let x := N.firstCollisionVertex family hbad
  have hij : i ≠ j := (N.firstCollisionLeft_lt_right family hbad).ne
  have hxi : x ∈ (family.2 i).vertices :=
    N.firstCollisionVertex_mem_left family hbad
  have hxj : x ∈ (family.2 j).vertices :=
    N.firstCollisionVertex_mem_right family hbad
  simpa [swapAtFirstCollision, i, j, x] using
    (N.signedFamilyWeight_swapSignedFamilyAt family i j hij x hxi hxj)

theorem swapAtFirstCollision_twice [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.swapAtFirstCollision
        (N.swapAtFirstCollision family hbad)
        (N.swapAtFirstCollision_not_signedVertexDisjoint family hbad) =
      family := by
  let i := N.firstCollisionLeft family hbad
  let j := N.firstCollisionRight family hbad
  let x := N.firstCollisionVertex family hbad
  have hij : i ≠ j := (N.firstCollisionLeft_lt_right family hbad).ne
  have hxi : x ∈ (family.2 i).vertices :=
    N.firstCollisionVertex_mem_left family hbad
  have hxj : x ∈ (family.2 j).vertices :=
    N.firstCollisionVertex_mem_right family hbad
  have hbad' : ¬N.SignedVertexDisjoint
      (N.swapSignedFamilyAt family i j hij x hxi hxj) :=
    N.not_signedVertexDisjoint_swapSignedFamilyAt family i j hij x hxi hxj
  have hi' : N.firstCollisionLeft
      (N.swapSignedFamilyAt family i j hij x hxi hxj) hbad' = i := by
    simpa [swapAtFirstCollision, i, j, x] using
      N.firstCollisionLeft_swapAtFirstCollision family hbad
  have hj' : N.firstCollisionRight
      (N.swapSignedFamilyAt family i j hij x hxi hxj) hbad' = j := by
    simpa [swapAtFirstCollision, i, j, x] using
      N.firstCollisionRight_swapAtFirstCollision family hbad
  have hx' : N.firstCollisionVertex
      (N.swapSignedFamilyAt family i j hij x hxi hxj) hbad' = x := by
    simpa [swapAtFirstCollision, i, j, x] using
      N.firstCollisionVertex_swapAtFirstCollision family hbad
  simpa [swapAtFirstCollision, i, j, x, hi', hj', hx'] using
    N.swapSignedFamilyAt_twice family i j hij x hxi hxj

end RankedQuiverNetwork

end

end LGV
