/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Resource.Family
import LGV.Resource.Swap

/-!
# Resource swaps in signed path families

This file lifts a certified local swap at an explicit shared-resource witness
to a signed path family. Collision selection remains a separate concern.
-/

namespace LGV

open scoped BigOperators

noncomputable section

universe u l

namespace ResourcePathNetwork

variable {R : Type u} {Resource : Type l} {n : ℕ}

/-- Change only the sink index of a path along an equality. -/
def castSinkPath (N : ResourcePathNetwork R (Fin n) Resource)
    {s t t' : Fin n} (h : t = t') (p : N.Path s t) : N.Path s t' :=
  h ▸ p

@[simp] theorem castSinkPath_rfl
    (N : ResourcePathNetwork R (Fin n) Resource)
    {s t : Fin n} (p : N.Path s t) :
    N.castSinkPath rfl p = p :=
  rfl

theorem castSinkPath_heq
    (N : ResourcePathNetwork R (Fin n) Resource)
    {s t t' : Fin n} (h : t = t') (p : N.Path s t) :
    N.castSinkPath h p ≍ p := by
  subst t'
  rfl

@[simp] theorem weight_castSinkPath
    (N : ResourcePathNetwork R (Fin n) Resource)
    {s t t' : Fin n} (h : t = t') (p : N.Path s t) :
    N.weight (N.castSinkPath h p) = N.weight p := by
  subst t'
  rfl

@[simp] theorem resources_castSinkPath
    (N : ResourcePathNetwork R (Fin n) Resource)
    {s t t' : Fin n} (h : t = t') (p : N.Path s t) :
    N.resources (N.castSinkPath h p) = N.resources p := by
  subst t'
  rfl

@[simp] theorem uses_castSinkPath
    [DecidableEq Resource]
    (N : ResourcePathNetwork R (Fin n) Resource)
    {s t t' : Fin n} (h : t = t') (p : N.Path s t)
    (resource : Resource) :
    N.Uses (N.castSinkPath h p) resource ↔ N.Uses p resource := by
  simp [Uses]

/-- The sink equality used at the left swapped source. -/
def swapLeftSinkEq (N : ResourcePathNetwork R (Fin n) Resource)
    (family : N.toFinitePathNetwork.SignedPathFamily) (i j : Fin n) :
    family.1 j = (family.1 * Equiv.swap i j) i := by
  simp [Equiv.Perm.mul_apply]

/-- The sink equality used at the right swapped source. -/
def swapRightSinkEq (N : ResourcePathNetwork R (Fin n) Resource)
    (family : N.toFinitePathNetwork.SignedPathFamily) (i j : Fin n) :
    family.1 i = (family.1 * Equiv.swap i j) j := by
  simp [Equiv.Perm.mul_apply]

/-- Away from the swapped sources, the sink index is unchanged. -/
def swapOtherSinkEq (N : ResourcePathNetwork R (Fin n) Resource)
    (family : N.toFinitePathNetwork.SignedPathFamily) (i j k : Fin n)
    (hki : k ≠ i) (hkj : k ≠ j) :
    family.1 k = (family.1 * Equiv.swap i j) k := by
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]

section CommMonoid

variable [CommMonoid R] [DecidableEq Resource]

/-- The local two-path result selected by a shared-resource witness. -/
def ResourceSwapCertificate.localSwapAt
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    {family : N.toFinitePathNetwork.SignedPathFamily}
    (w : SharedResourceWitness N family) :
    ResourceSwapResult N (family.2 w.left) (family.2 w.right) w.resource :=
  C.swap (family.2 w.left) (family.2 w.right) w.resource
    w.left_uses w.right_uses

/-- Local swapping commutes with casts of the two input sink indices. -/
theorem ResourceSwapCertificate.swap_first_castSinkPaths
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    {s t t' u v v' : Fin n} (ht : t = t') (hv : v = v')
    (p : N.Path s t) (q : N.Path u v) (resource : Resource)
    (hp : N.Uses p resource) (hq : N.Uses q resource)
    (hp' : N.Uses (N.castSinkPath ht p) resource)
    (hq' : N.Uses (N.castSinkPath hv q) resource) :
    (C.swap (N.castSinkPath ht p) (N.castSinkPath hv q) resource hp' hq').first =
      N.castSinkPath hv (C.swap p q resource hp hq).first := by
  subst t'
  subst v'
  rfl

/-- The second output of local swapping likewise commutes with sink casts. -/
theorem ResourceSwapCertificate.swap_second_castSinkPaths
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    {s t t' u v v' : Fin n} (ht : t = t') (hv : v = v')
    (p : N.Path s t) (q : N.Path u v) (resource : Resource)
    (hp : N.Uses p resource) (hq : N.Uses q resource)
    (hp' : N.Uses (N.castSinkPath ht p) resource)
    (hq' : N.Uses (N.castSinkPath hv q) resource) :
    (C.swap (N.castSinkPath ht p) (N.castSinkPath hv q) resource hp' hq').second =
      N.castSinkPath ht (C.swap p q resource hp hq).second := by
  subst t'
  subst v'
  rfl

/-- Swap the two paths selected by an explicit shared-resource witness. -/
def ResourceSwapCertificate.swapSignedFamilyAt
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (w : SharedResourceWitness N family) :
    N.toFinitePathNetwork.SignedPathFamily := by
  classical
  refine ⟨family.1 * Equiv.swap w.left w.right, ?_⟩
  intro k
  by_cases hleft : k = w.left
  · subst k
    exact N.castSinkPath (N.swapLeftSinkEq family w.left w.right)
      (C.localSwapAt w).first
  · by_cases hright : k = w.right
    · subst k
      exact N.castSinkPath (N.swapRightSinkEq family w.left w.right)
        (C.localSwapAt w).second
    · exact N.castSinkPath
        (N.swapOtherSinkEq family w.left w.right k hleft hright)
        (family.2 k)

@[simp] theorem ResourceSwapCertificate.swapSignedFamilyAt_perm
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (w : SharedResourceWitness N family) :
    (C.swapSignedFamilyAt family w).1 =
      family.1 * Equiv.swap w.left w.right :=
  rfl

theorem ResourceSwapCertificate.swapSignedFamilyAt_path_left
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (w : SharedResourceWitness N family) :
    (C.swapSignedFamilyAt family w).2 w.left =
      N.castSinkPath (N.swapLeftSinkEq family w.left w.right)
        (C.localSwapAt w).first := by
  simp only [swapSignedFamilyAt, dite_true]

theorem ResourceSwapCertificate.swapSignedFamilyAt_path_right
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (w : SharedResourceWitness N family) :
    (C.swapSignedFamilyAt family w).2 w.right =
      N.castSinkPath (N.swapRightSinkEq family w.left w.right)
        (C.localSwapAt w).second := by
  simp only [swapSignedFamilyAt, dif_neg w.left_ne_right.symm,
    dite_true]

theorem ResourceSwapCertificate.swapSignedFamilyAt_path_of_ne
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (w : SharedResourceWitness N family) (k : Fin n)
    (hkleft : k ≠ w.left) (hkright : k ≠ w.right) :
    (C.swapSignedFamilyAt family w).2 k =
      N.castSinkPath
        (N.swapOtherSinkEq family w.left w.right k hkleft hkright)
        (family.2 k) := by
  simp only [swapSignedFamilyAt, dif_neg hkleft, dif_neg hkright]

@[simp] theorem ResourceSwapCertificate.swapSignedFamilyAt_weight_left
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (w : SharedResourceWitness N family) :
    N.weight ((C.swapSignedFamilyAt family w).2 w.left) =
      N.weight (C.localSwapAt w).first := by
  simp [swapSignedFamilyAt]

@[simp] theorem ResourceSwapCertificate.swapSignedFamilyAt_weight_right
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (w : SharedResourceWitness N family) :
    N.weight ((C.swapSignedFamilyAt family w).2 w.right) =
      N.weight (C.localSwapAt w).second := by
  simp [swapSignedFamilyAt, w.left_ne_right.symm]

theorem ResourceSwapCertificate.swapSignedFamilyAt_weight_of_ne
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (w : SharedResourceWitness N family) (k : Fin n)
    (hkleft : k ≠ w.left) (hkright : k ≠ w.right) :
    N.weight ((C.swapSignedFamilyAt family w).2 k) =
      N.weight (family.2 k) := by
  simp [swapSignedFamilyAt, hkleft, hkright]

/-- The selected resource remains shared by the two swapped family paths. -/
abbrev SharedResourceWitness.afterSwap
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    {family : N.toFinitePathNetwork.SignedPathFamily}
    (w : SharedResourceWitness N family) :
    SharedResourceWitness N (C.swapSignedFamilyAt family w) where
  left := w.left
  right := w.right
  left_ne_right := w.left_ne_right
  resource := w.resource
  left_uses := by
    rw [C.swapSignedFamilyAt_path_left family w]
    exact (N.uses_castSinkPath _ _ _).mpr (C.localSwapAt w).first_uses
  right_uses := by
    rw [C.swapSignedFamilyAt_path_right family w]
    exact (N.uses_castSinkPath _ _ _).mpr (C.localSwapAt w).second_uses

@[simp] theorem SharedResourceWitness.afterSwap_left
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    {family : N.toFinitePathNetwork.SignedPathFamily}
    (w : SharedResourceWitness N family) :
    (w.afterSwap C).left = w.left :=
  rfl

@[simp] theorem SharedResourceWitness.afterSwap_right
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    {family : N.toFinitePathNetwork.SignedPathFamily}
    (w : SharedResourceWitness N family) :
    (w.afterSwap C).right = w.right :=
  rfl

@[simp] theorem SharedResourceWitness.afterSwap_resource
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    {family : N.toFinitePathNetwork.SignedPathFamily}
    (w : SharedResourceWitness N family) :
    (w.afterSwap C).resource = w.resource :=
  rfl

/-- An explicit-witness family swap preserves unsigned family weight. -/
theorem ResourceSwapCertificate.familyWeight_swapSignedFamilyAt
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (w : SharedResourceWitness N family) :
    N.toFinitePathNetwork.familyWeight (C.swapSignedFamilyAt family w).2 =
      N.toFinitePathNetwork.familyWeight family.2 := by
  let rest : Finset (Fin n) := (Finset.univ.erase w.left).erase w.right
  have hrightMem : w.right ∈ (Finset.univ : Finset (Fin n)).erase w.left := by
    simp [w.left_ne_right.symm]
  let f : Fin n → R := fun k =>
    N.weight ((C.swapSignedFamilyAt family w).2 k)
  let g : Fin n → R := fun k => N.weight (family.2 k)
  have hrest (k : Fin n) (hk : k ∈ rest) : f k = g k := by
    have hkleft : k ≠ w.left :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkright : k ≠ w.right := (Finset.mem_erase.mp hk).1
    exact C.swapSignedFamilyAt_weight_of_ne family w k hkleft hkright
  have hpair : f w.left * f w.right = g w.left * g w.right := by
    dsimp only [f, g]
    rw [C.swapSignedFamilyAt_weight_left family w,
      C.swapSignedFamilyAt_weight_right family w]
    exact (C.localSwapAt w).weight_mul
  change (∏ k : Fin n, f k) = ∏ k : Fin n, g k
  calc
    (∏ k : Fin n, f k) =
        f w.left * ∏ k ∈ Finset.univ.erase w.left, f k := by
      simpa using (Finset.mul_prod_erase Finset.univ f
        (Finset.mem_univ w.left)).symm
    _ = f w.left * (f w.right * ∏ k ∈ rest, f k) := by
      congr 1
      simpa [rest] using (Finset.mul_prod_erase
        (Finset.univ.erase w.left) f hrightMem).symm
    _ = g w.left * (g w.right * ∏ k ∈ rest, g k) := by
      rw [← mul_assoc, hpair, mul_assoc]
      congr 2
      exact Finset.prod_congr rfl hrest
    _ = g w.left * ∏ k ∈ Finset.univ.erase w.left, g k := by
      congr 1
      simpa [rest] using Finset.mul_prod_erase
        (Finset.univ.erase w.left) g hrightMem
    _ = ∏ k : Fin n, g k := by
      simpa using Finset.mul_prod_erase Finset.univ g
        (Finset.mem_univ w.left)

end CommMonoid

section CommRing

variable [CommRing R] [DecidableEq Resource]

/-- An explicit-witness family swap negates the signed family weight. -/
theorem ResourceSwapCertificate.signedFamilyWeight_swapSignedFamilyAt
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (w : SharedResourceWitness N family) :
    N.toFinitePathNetwork.signedFamilyWeight (C.swapSignedFamilyAt family w) =
      -N.toFinitePathNetwork.signedFamilyWeight family := by
  apply N.toFinitePathNetwork.signedFamilyWeight_eq_neg_of_right_swap
    w.left_ne_right
  · exact C.swapSignedFamilyAt_perm family w
  · exact C.familyWeight_swapSignedFamilyAt family w

end CommRing

end ResourcePathNetwork

end

end LGV
