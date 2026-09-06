/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Quiver.Split
import Mathlib.Combinatorics.Quiver.Cast

/-!
# Tail swaps in quiver path families

This file lifts the two-path tail swap to signed path families. Swapping the
tails at source indices `i` and `j` right-multiplies the realized sink
permutation by the transposition of `i` and `j`.
-/

namespace LGV

open Quiver
open scoped BigOperators

noncomputable section

universe u v

namespace RankedQuiverNetwork

variable {R : Type u} {V : Type v} {n : ℕ}
variable [Quiver V] [Fintype V]
variable [∀ a b : V, Fintype (a ⟶ b)]

/-- Change only the sink label of a quiver path along an equality of designated
sink indices. -/
def castSinkPath (N : RankedQuiverNetwork R V (Fin n))
    {i j k : Fin n} (h : j = k)
    (p : Quiver.Path (N.source i) (N.sink j)) :
    Quiver.Path (N.source i) (N.sink k) :=
  p.cast rfl (congrArg N.sink h)

omit [Fintype V] [∀ a b : V, Fintype (a ⟶ b)] in
@[simp] theorem weight_castSinkPath [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    {i j k : Fin n} (h : j = k)
    (p : Quiver.Path (N.source i) (N.sink j)) :
    Quiver.Path.weight N.edgeWeight (N.castSinkPath h p) =
      Quiver.Path.weight N.edgeWeight p := by
  subst k
  simp [castSinkPath]

omit [Fintype V] [∀ a b : V, Fintype (a ⟶ b)] in
@[simp] theorem vertices_castSinkPath
    (N : RankedQuiverNetwork R V (Fin n))
    {i j k : Fin n} (h : j = k)
    (p : Quiver.Path (N.source i) (N.sink j)) :
    (N.castSinkPath h p).vertices = p.vertices := by
  subst k
  simp [castSinkPath]

/-- Swap two tails in a signed path family at a specified common vertex. -/
def swapSignedFamilyAt [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (_hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) :
    N.toFinitePathNetwork.SignedPathFamily := by
  classical
  refine ⟨family.1 * Equiv.swap i j, ?_⟩
  intro k
  by_cases hki : k = i
  · subst k
    change Quiver.Path (N.source i)
      (N.sink ((family.1 * Equiv.swap i j) i))
    exact N.castSinkPath (by simp [Equiv.Perm.mul_apply])
      (N.swapFirstAt (family.2 i) (family.2 j) hxi hxj)
  · by_cases hkj : k = j
    · subst k
      change Quiver.Path (N.source j)
        (N.sink ((family.1 * Equiv.swap i j) j))
      exact N.castSinkPath (by simp [Equiv.Perm.mul_apply])
        (N.swapSecondAt (family.2 i) (family.2 j) hxi hxj)
    · change Quiver.Path (N.source k)
        (N.sink ((family.1 * Equiv.swap i j) k))
      exact N.castSinkPath (by
        simp [Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne hki hkj]) (family.2 k)

@[simp] theorem swapSignedFamilyAt_perm [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) :
    (N.swapSignedFamilyAt family i j hij x hxi hxj).1 =
      family.1 * Equiv.swap i j :=
  rfl

@[simp] theorem swapSignedFamilyAt_weight_left [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) :
    N.toFinitePathNetwork.weight
        ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 i) =
      Quiver.Path.weight N.edgeWeight
        (N.swapFirstAt (family.2 i) (family.2 j) hxi hxj) := by
  simp [swapSignedFamilyAt]

@[simp] theorem swapSignedFamilyAt_weight_right [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) :
    N.toFinitePathNetwork.weight
        ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 j) =
      Quiver.Path.weight N.edgeWeight
        (N.swapSecondAt (family.2 i) (family.2 j) hxi hxj) := by
  have hji : j ≠ i := hij.symm
  simp [swapSignedFamilyAt, hji]

theorem swapSignedFamilyAt_weight_of_ne [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j k : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices)
    (hki : k ≠ i) (hkj : k ≠ j) :
    N.toFinitePathNetwork.weight
        ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 k) =
      N.toFinitePathNetwork.weight (family.2 k) := by
  simp [swapSignedFamilyAt, hki, hkj]

theorem mem_swapSignedFamilyAt_left [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) :
    x ∈ ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 i).vertices := by
  simpa only [swapSignedFamilyAt, if_pos rfl, dif_pos rfl, dite_true,
    dite_false, id_eq, vertices_castSinkPath] using
    N.mem_swapFirstAt_vertices (family.2 i) (family.2 j) hxi hxj

theorem mem_swapSignedFamilyAt_right [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) :
    x ∈ ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 j).vertices := by
  simpa only [swapSignedFamilyAt, if_neg hij.symm, dif_neg hij.symm,
    if_pos rfl, dif_pos rfl, dite_true, dite_false, id_eq,
    vertices_castSinkPath] using
    N.mem_swapSecondAt_vertices (family.2 i) (family.2 j) hxi hxj

/-- A family tail swap preserves its unsigned product weight. -/
theorem familyWeight_swapSignedFamilyAt [CommMonoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) :
    N.toFinitePathNetwork.familyWeight
        (N.swapSignedFamilyAt family i j hij x hxi hxj).2 =
      N.toFinitePathNetwork.familyWeight family.2 := by
  let rest : Finset (Fin n) := (Finset.univ.erase i).erase j
  have hjmem : j ∈ (Finset.univ : Finset (Fin n)).erase i := by
    simp [hij.symm]
  have hrest (k : Fin n) (hk : k ∈ rest) :
      N.toFinitePathNetwork.weight
          ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 k) =
        N.toFinitePathNetwork.weight (family.2 k) := by
    have hki : k ≠ i := by
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    exact N.swapSignedFamilyAt_weight_of_ne
      family i j k hij x hxi hxj hki hkj
  let f : Fin n → R := fun k => N.toFinitePathNetwork.weight
    ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 k)
  let g : Fin n → R := fun k => N.toFinitePathNetwork.weight (family.2 k)
  have hpair : f i * f j = g i * g j := by
    change N.toFinitePathNetwork.weight
          ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 i) *
        N.toFinitePathNetwork.weight
          ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 j) =
      N.toFinitePathNetwork.weight (family.2 i) *
        N.toFinitePathNetwork.weight (family.2 j)
    rw [N.swapSignedFamilyAt_weight_left,
      N.swapSignedFamilyAt_weight_right]
    simp only [toFinitePathNetwork_weight]
    exact N.weight_swapFirstAt_mul_weight_swapSecondAt
      (family.2 i) (family.2 j) hxi hxj
  change (∏ k : Fin n, f k) = ∏ k : Fin n, g k
  calc
    (∏ k : Fin n, f k) =
        f i * ∏ k ∈ Finset.univ.erase i, f k := by
      simpa using (Finset.mul_prod_erase Finset.univ f
        (Finset.mem_univ i)).symm
    _ = f i * (f j * ∏ k ∈ rest, f k) := by
      congr 1
      simpa [rest] using (Finset.mul_prod_erase
        (Finset.univ.erase i) f hjmem).symm
    _ = g i * (g j * ∏ k ∈ rest, g k) := by
      rw [← mul_assoc, hpair, mul_assoc]
      congr 2
      exact Finset.prod_congr rfl fun k hk => hrest k hk
    _ = g i * ∏ k ∈ Finset.univ.erase i, g k := by
      congr 1
      simpa [rest] using Finset.mul_prod_erase
        (Finset.univ.erase i) g hjmem
    _ = ∏ k : Fin n, g k := by
      simpa using Finset.mul_prod_erase Finset.univ g (Finset.mem_univ i)

/-- A family tail swap negates the signed LGV weight. -/
theorem signedFamilyWeight_swapSignedFamilyAt [CommRing R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) :
    N.toFinitePathNetwork.signedFamilyWeight
        (N.swapSignedFamilyAt family i j hij x hxi hxj) =
      -N.toFinitePathNetwork.signedFamilyWeight family := by
  apply N.toFinitePathNetwork.signedFamilyWeight_eq_neg_of_right_swap hij
  · exact N.swapSignedFamilyAt_perm family i j hij x hxi hxj
  · exact N.familyWeight_swapSignedFamilyAt family i j hij x hxi hxj

/-- Swapping at a common vertex produces another intersecting family. -/
theorem not_signedVertexDisjoint_swapSignedFamilyAt [Monoid R] [DecidableEq V]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) :
    ¬N.SignedVertexDisjoint
      (N.swapSignedFamilyAt family i j hij x hxi hxj) := by
  intro hdisjoint
  have hpq : VertexDisjoint
      ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 i)
      ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 j) :=
    hdisjoint i j hij
  apply (not_vertexDisjoint_iff _ _).mpr ⟨x, ?_, ?_⟩ hpq
  · exact N.mem_swapSignedFamilyAt_left family i j hij x hxi hxj
  · exact N.mem_swapSignedFamilyAt_right family i j hij x hxi hxj

end RankedQuiverNetwork

end


end LGV
