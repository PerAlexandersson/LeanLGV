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
@[simp] theorem castSinkPath_rfl
    (N : RankedQuiverNetwork R V (Fin n))
    {i j : Fin n} (p : Quiver.Path (N.source i) (N.sink j)) :
    N.castSinkPath rfl p = p := by
  simp [castSinkPath]

omit [Fintype V] [∀ a b : V, Fintype (a ⟶ b)] in
theorem castSinkPath_trans
    (N : RankedQuiverNetwork R V (Fin n))
    {i j k l : Fin n} (hjk : j = k) (hkl : k = l)
    (p : Quiver.Path (N.source i) (N.sink j)) :
    N.castSinkPath hkl (N.castSinkPath hjk p) =
      N.castSinkPath (hjk.trans hkl) p := by
  subst k
  subst l
  simp

omit [Fintype V] [∀ a b : V, Fintype (a ⟶ b)] in
theorem castSinkPath_heq
    (N : RankedQuiverNetwork R V (Fin n))
    {i j k : Fin n} (h : j = k)
    (p : Quiver.Path (N.source i) (N.sink j)) :
    N.castSinkPath h p ≍ p :=
  Quiver.Path.cast_heq rfl (congrArg N.sink h) p

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

omit [Fintype V] [∀ a b : V, Fintype (a ⟶ b)] in
/-- Tail swapping commutes with changing the two sink labels. -/
theorem swapFirstAt_castSinkPaths
    (N : RankedQuiverNetwork R V (Fin n))
    {s t t' u v v' : Fin n} {z : V}
    (ht : t = t') (hv : v = v')
    (p : Quiver.Path (N.source s) (N.sink t))
    (q : Quiver.Path (N.source u) (N.sink v))
    (hzp : z ∈ p.vertices) (hzq : z ∈ q.vertices)
    (hzp' : z ∈ (N.castSinkPath ht p).vertices)
    (hzq' : z ∈ (N.castSinkPath hv q).vertices) :
    N.swapFirstAt (N.castSinkPath ht p) (N.castSinkPath hv q) hzp' hzq' =
      N.castSinkPath hv (N.swapFirstAt p q hzp hzq) := by
  cases ht
  cases hv
  simp [castSinkPath]

omit [Fintype V] [∀ a b : V, Fintype (a ⟶ b)] in
theorem swapSecondAt_castSinkPaths
    (N : RankedQuiverNetwork R V (Fin n))
    {s t t' u v v' : Fin n} {z : V}
    (ht : t = t') (hv : v = v')
    (p : Quiver.Path (N.source s) (N.sink t))
    (q : Quiver.Path (N.source u) (N.sink v))
    (hzp : z ∈ p.vertices) (hzq : z ∈ q.vertices)
    (hzp' : z ∈ (N.castSinkPath ht p).vertices)
    (hzq' : z ∈ (N.castSinkPath hv q).vertices) :
    N.swapSecondAt (N.castSinkPath ht p) (N.castSinkPath hv q) hzp' hzq' =
      N.castSinkPath ht (N.swapSecondAt p q hzp hzq) := by
  cases ht
  cases hv
  simp [castSinkPath]

/-- The sink-label equality used by the left branch of a family swap. -/
def swapLeftSinkEq [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) : family.1 j = (family.1 * Equiv.swap i j) i := by
  simp [Equiv.Perm.mul_apply]

/-- The sink-label equality used by the right branch of a family swap. -/
def swapRightSinkEq [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) : family.1 i = (family.1 * Equiv.swap i j) j := by
  simp [Equiv.Perm.mul_apply]

/-- Away from the swapped indices, the sink label is unchanged. -/
def swapOtherSinkEq [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) :
    family.1 k = (family.1 * Equiv.swap i j) k := by
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]

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
    exact N.castSinkPath (N.swapLeftSinkEq family i j)
      (N.swapFirstAt (family.2 i) (family.2 j) hxi hxj)
  · by_cases hkj : k = j
    · subst k
      change Quiver.Path (N.source j)
        (N.sink ((family.1 * Equiv.swap i j) j))
      exact N.castSinkPath (N.swapRightSinkEq family i j)
        (N.swapSecondAt (family.2 i) (family.2 j) hxi hxj)
    · change Quiver.Path (N.source k)
        (N.sink ((family.1 * Equiv.swap i j) k))
      exact N.castSinkPath (N.swapOtherSinkEq family i j k hki hkj)
        (family.2 k)

@[simp] theorem swapSignedFamilyAt_perm [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) :
    (N.swapSignedFamilyAt family i j hij x hxi hxj).1 =
      family.1 * Equiv.swap i j :=
  rfl

theorem swapSignedFamilyAt_path_left [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) :
    (N.swapSignedFamilyAt family i j hij x hxi hxj).2 i =
      N.castSinkPath (N.swapLeftSinkEq family i j)
        (N.swapFirstAt (family.2 i) (family.2 j) hxi hxj) := by
  simp only [swapSignedFamilyAt, dite_true, id_eq]

theorem swapSignedFamilyAt_path_right [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) :
    (N.swapSignedFamilyAt family i j hij x hxi hxj).2 j =
      N.castSinkPath (N.swapRightSinkEq family i j)
        (N.swapSecondAt (family.2 i) (family.2 j) hxi hxj) := by
  simp only [swapSignedFamilyAt, dif_neg hij.symm, dite_true, id_eq]

theorem swapSignedFamilyAt_path_of_ne [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j k : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices)
    (hki : k ≠ i) (hkj : k ≠ j) :
    (N.swapSignedFamilyAt family i j hij x hxi hxj).2 k =
      N.castSinkPath (N.swapOtherSinkEq family i j k hki hkj)
        (family.2 k) := by
  simp only [swapSignedFamilyAt, dif_neg hki, dif_neg hkj, id_eq]

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

/-- Swapping the two paths produced by a family tail swap restores the first
path, up to its required sink-label cast. -/
theorem swapFirstAt_swapSignedFamilyAt [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) :
    N.swapFirstAt
        ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 i)
        ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 j)
        (N.mem_swapSignedFamilyAt_left family i j hij x hxi hxj)
        (N.mem_swapSignedFamilyAt_right family i j hij x hxi hxj) =
      N.castSinkPath (N.swapRightSinkEq family i j)
        (N.swapFirstAt
          (N.swapFirstAt (family.2 i) (family.2 j) hxi hxj)
          (N.swapSecondAt (family.2 i) (family.2 j) hxi hxj)
          (N.mem_swapFirstAt_vertices (family.2 i) (family.2 j) hxi hxj)
          (N.mem_swapSecondAt_vertices (family.2 i) (family.2 j) hxi hxj)) := by
  simpa only [swapSignedFamilyAt, dite_true, dif_neg hij.symm, id_eq] using
    N.swapFirstAt_castSinkPaths
      (N.swapLeftSinkEq family i j) (N.swapRightSinkEq family i j)
      (N.swapFirstAt (family.2 i) (family.2 j) hxi hxj)
      (N.swapSecondAt (family.2 i) (family.2 j) hxi hxj)
      (N.mem_swapFirstAt_vertices (family.2 i) (family.2 j) hxi hxj)
      (N.mem_swapSecondAt_vertices (family.2 i) (family.2 j) hxi hxj)
      _ _

/-- Swapping the two paths produced by a family tail swap restores the second
path, up to its required sink-label cast. -/
theorem swapSecondAt_swapSignedFamilyAt [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) :
    N.swapSecondAt
        ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 i)
        ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 j)
        (N.mem_swapSignedFamilyAt_left family i j hij x hxi hxj)
        (N.mem_swapSignedFamilyAt_right family i j hij x hxi hxj) =
      N.castSinkPath (N.swapLeftSinkEq family i j)
        (N.swapSecondAt
          (N.swapFirstAt (family.2 i) (family.2 j) hxi hxj)
          (N.swapSecondAt (family.2 i) (family.2 j) hxi hxj)
          (N.mem_swapFirstAt_vertices (family.2 i) (family.2 j) hxi hxj)
          (N.mem_swapSecondAt_vertices (family.2 i) (family.2 j) hxi hxj)) := by
  simpa only [swapSignedFamilyAt, dite_true, dif_neg hij.symm, id_eq] using
    N.swapSecondAt_castSinkPaths
      (N.swapLeftSinkEq family i j) (N.swapRightSinkEq family i j)
      (N.swapFirstAt (family.2 i) (family.2 j) hxi hxj)
      (N.swapSecondAt (family.2 i) (family.2 j) hxi hxj)
      (N.mem_swapFirstAt_vertices (family.2 i) (family.2 j) hxi hxj)
      (N.mem_swapSecondAt_vertices (family.2 i) (family.2 j) hxi hxj)
      _ _

/-- Swapping the same two family tails twice at the same vertex restores the
original signed path family. -/
theorem swapSignedFamilyAt_twice [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) :
    let swapped := N.swapSignedFamilyAt family i j hij x hxi hxj
    N.swapSignedFamilyAt swapped i j hij x
      (N.mem_swapSignedFamilyAt_left family i j hij x hxi hxj)
      (N.mem_swapSignedFamilyAt_right family i j hij x hxi hxj) = family := by
  let swapped := N.swapSignedFamilyAt family i j hij x hxi hxj
  let hxi' := N.mem_swapSignedFamilyAt_left family i j hij x hxi hxj
  let hxj' := N.mem_swapSignedFamilyAt_right family i j hij x hxi hxj
  let twice := N.swapSignedFamilyAt swapped i j hij x hxi' hxj'
  change twice = family
  rw [Sigma.ext_iff]
  constructor
  · simp [twice, swapped, mul_assoc]
  · refine Function.hfunext rfl ?_
    intro k k' hkk
    have hk : k = k' := eq_of_heq hkk
    subst k'
    by_cases hki : k = i
    · subst k
      rw [N.swapSignedFamilyAt_path_left swapped i j hij x hxi' hxj']
      apply HEq.trans (N.castSinkPath_heq _ _)
      rw [N.swapFirstAt_swapSignedFamilyAt, N.swapFirstAt_twice]
      exact N.castSinkPath_heq _ _
    · by_cases hkj : k = j
      · subst k
        rw [N.swapSignedFamilyAt_path_right swapped i j hij x hxi' hxj']
        apply HEq.trans (N.castSinkPath_heq _ _)
        rw [N.swapSecondAt_swapSignedFamilyAt, N.swapSecondAt_twice]
        exact N.castSinkPath_heq _ _
      · rw [N.swapSignedFamilyAt_path_of_ne swapped i j k hij x hxi' hxj' hki hkj,
            N.swapSignedFamilyAt_path_of_ne family i j k hij x hxi hxj hki hkj]
        exact (N.castSinkPath_heq _ _).trans (N.castSinkPath_heq _ _)

theorem vertices_swapSignedFamilyAt_of_ne [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j k : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices)
    (hki : k ≠ i) (hkj : k ≠ j) :
    ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 k).vertices =
      (family.2 k).vertices := by
  simp only [swapSignedFamilyAt, dif_neg hki, dif_neg hkj,
    id_eq, vertices_castSinkPath]

/-- A vertex above the swap rank in a swapped family path already belonged to
the corresponding original path. -/
theorem mem_original_of_mem_swapSignedFamilyAt_of_rank_lt [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j k : Fin n) (hij : i ≠ j) (x y : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices)
    (hy : y ∈ ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 k).vertices)
    (hxy : N.rank x < N.rank y) : y ∈ (family.2 k).vertices := by
  by_cases hki : k = i
  · subst k
    have hy' : y ∈ (N.swapFirstAt
        (family.2 i) (family.2 j) hxi hxj).vertices := by
      simpa only [swapSignedFamilyAt, if_pos rfl, dif_pos rfl,
        dite_true, dite_false, id_eq, vertices_castSinkPath] using hy
    exact N.mem_original_first_of_mem_swapFirstAt_of_rank_lt
      (family.2 i) (family.2 j) hxi hxj hy' hxy
  · by_cases hkj : k = j
    · subst k
      have hy' : y ∈ (N.swapSecondAt
          (family.2 i) (family.2 j) hxi hxj).vertices := by
        simpa only [swapSignedFamilyAt, if_neg hij.symm,
          dif_neg hij.symm, if_pos rfl, dif_pos rfl, dite_true,
          dite_false, id_eq, vertices_castSinkPath] using hy
      exact N.mem_original_second_of_mem_swapSecondAt_of_rank_lt
        (family.2 i) (family.2 j) hxi hxj hy' hxy
    · have hvertices := N.vertices_swapSignedFamilyAt_of_ne
        family i j k hij x hxi hxj hki hkj
      exact hvertices ▸ hy

/-- At the swap rank, membership in each indexed family path is unchanged. -/
theorem mem_swapSignedFamilyAt_iff_of_rank_eq [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j k : Fin n) (hij : i ≠ j) (x y : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices)
    (hrank : N.rank y = N.rank x) :
    y ∈ ((N.swapSignedFamilyAt family i j hij x hxi hxj).2 k).vertices ↔
      y ∈ (family.2 k).vertices := by
  by_cases hki : k = i
  · subst k
    constructor
    · intro hy
      have hx := N.mem_swapSignedFamilyAt_left family i j hij x hxi hxj
      have hxy := N.eq_of_mem_vertices_of_rank_eq _ hx hy hrank.symm
      simpa [hxy] using hxi
    · intro hy
      have hxy := N.eq_of_mem_vertices_of_rank_eq (family.2 i) hxi hy hrank.symm
      simpa [hxy] using
        N.mem_swapSignedFamilyAt_left family i j hij x hxi hxj
  · by_cases hkj : k = j
    · subst k
      constructor
      · intro hy
        have hx := N.mem_swapSignedFamilyAt_right family i j hij x hxi hxj
        have hxy := N.eq_of_mem_vertices_of_rank_eq _ hx hy hrank.symm
        simpa [hxy] using hxj
      · intro hy
        have hxy := N.eq_of_mem_vertices_of_rank_eq (family.2 j) hxj hy hrank.symm
        simpa [hxy] using
          N.mem_swapSignedFamilyAt_right family i j hij x hxi hxj
    · rw [N.vertices_swapSignedFamilyAt_of_ne family i j k hij x hxi hxj hki hkj]

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
