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

theorem swapAtFirstCollision_ne [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.swapAtFirstCollision family hbad ≠ family := by
  let i := N.firstCollisionLeft family hbad
  let j := N.firstCollisionRight family hbad
  have hij : i ≠ j := (N.firstCollisionLeft_lt_right family hbad).ne
  intro heq
  have hperm := congrArg (fun f => f.1 i) heq
  have hji : j = i := family.1.injective (by
    simpa [swapAtFirstCollision, i, j, swapSignedFamilyAt,
      Equiv.Perm.mul_apply] using hperm)
  exact hij hji.symm

theorem firstCollisionSwap_involutive [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (b : {family : N.toFinitePathNetwork.SignedPathFamily //
      ¬N.SignedVertexDisjoint family}) :
    N.firstCollisionSwap (N.firstCollisionSwap b) = b := by
  apply Subtype.ext
  exact N.swapAtFirstCollision_twice b.1 b.2

theorem det_pathMatrix_eq_sum_signedVertexDisjoint [CommRing R]
    (N : RankedQuiverNetwork R V (Fin n)) :
    Matrix.det N.pathMatrix =
      ∑ family : {family : N.toFinitePathNetwork.SignedPathFamily //
        N.SignedVertexDisjoint family},
        N.toFinitePathNetwork.signedFamilyWeight family.1 := by
  let swap := N.firstCollisionSwap
  apply FinitePathNetwork.det_matrix_eq_sum_goodFamilies_of_bad_involution
    N.toFinitePathNetwork N.SignedVertexDisjoint swap
  · intro b
    exact N.toFinitePathNetwork.signedFamilyWeight_add_eq_zero_of_swap_eq_neg
      (N.signedFamilyWeight_swapAtFirstCollision b.1 b.2)
  · intro b _ hb
    apply N.swapAtFirstCollision_ne b.1 b.2
    exact congrArg Subtype.val hb
  · intro b
    exact N.firstCollisionSwap_involutive b

def orderedCancellationCertificate [CommRing R]
    (N : RankedQuiverNetwork R V (Fin n))
    (hcross : FinitePathNetwork.HasTwoPathObstruction
      N.toFinitePathNetwork (fun p q => VertexDisjoint p q)) :
    FinitePathNetwork.OrderedCancellationCertificate N.toFinitePathNetwork :=
  { Disjoint := fun p q => VertexDisjoint p q
    decidable := N.instDecidablePredSignedVertexDisjoint
    hcross := hcross
    swap := N.firstCollisionSwap
    weight_swap := fun b => N.signedFamilyWeight_swapAtFirstCollision b.1 b.2
    ne_fixed_of_weight_ne_zero := fun b _ => by
      intro hb
      apply N.swapAtFirstCollision_ne b.1 b.2
      exact congrArg Subtype.val hb
    involutive := N.firstCollisionSwap_involutive }

theorem det_pathMatrix_eq_sum_vertexDisjoint [CommRing R]
    (N : RankedQuiverNetwork R V (Fin n))
    (hcross : FinitePathNetwork.HasTwoPathObstruction
      N.toFinitePathNetwork (fun p q => VertexDisjoint p q)) :
    Matrix.det N.pathMatrix =
      ∑ family : {family : N.toFinitePathNetwork.SignedPathFamily //
        N.SignedVertexDisjoint family},
        N.toFinitePathNetwork.familyWeight family.1.2 := by
  let C := N.orderedCancellationCertificate hcross
  let _ := N.instDecidablePredSignedVertexDisjoint
  convert C.det_eq_sum_pairwiseDisjoint using 1 <;> rfl

theorem det_pathMatrix_nonneg [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (N : RankedQuiverNetwork R V (Fin n))
    (hcross : FinitePathNetwork.HasTwoPathObstruction
      N.toFinitePathNetwork (fun p q => VertexDisjoint p q))
    (hweight : ∀ {a b : V} (e : a ⟶ b), 0 ≤ N.edgeWeight e) :
    0 ≤ Matrix.det N.pathMatrix := by
  apply FinitePathNetwork.OrderedCancellationCertificate.det_nonneg
    (N.orderedCancellationCertificate hcross)
  exact N.pathWeight_nonneg hweight

end RankedQuiverNetwork

end

end LGV
