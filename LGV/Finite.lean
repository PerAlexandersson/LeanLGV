/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Finite LGV algebra

This file starts the reusable Lindstrom-Gessel-Viennot layer. The network
interface is deliberately finite: for each source/sink pair we assume a finite
type of paths and a path weight.

The main results are the path-matrix determinant expansion and the abstract
cancellation form used by a first-intersection involution. Concrete backends
can instantiate `Good` as the nonintersecting families and provide the
sign-reversing involution on its complement.
-/

namespace LGV

open scoped BigOperators

noncomputable section

universe u v w

/--
Abstract sign-reversing cancellation lemma.

This is the algebraic heart of the first-intersection involution: if the bad
objects are paired by a fixed-point-free involution and paired weights add to
zero, then their total contribution is zero.
-/
theorem sum_eq_zero_of_sign_reversing_involution {Bad A : Type*}
    [Fintype Bad] [AddCommMonoid A]
    (weight : Bad → A) (swap : Bad → Bad)
    (hcancel : ∀ b : Bad, weight b + weight (swap b) = 0)
    (hfixed : ∀ b : Bad, weight b ≠ 0 → swap b ≠ b)
    (hinvol : ∀ b : Bad, swap (swap b) = b) :
    (∑ b : Bad, weight b) = 0 := by
  classical
  exact Finset.sum_ninvolution (s := Finset.univ) (f := weight) swap
    hcancel hfixed (by simp) hinvol

/--
A finite weighted path network between a common finite source/sink index type.

`Path s t` is the finite type of directed paths from source `s` to sink `t`.
The path matrix has `(s,t)` entry equal to the sum of weights of all such
paths, following the conventional source-row, sink-column orientation.
-/
structure FinitePathNetwork (R : Type u) (ι : Type v) where
  Path : ι → ι → Type w
  instFintypePath : ∀ s t : ι, Fintype (Path s t)
  weight : ∀ {s t : ι}, Path s t → R

namespace FinitePathNetwork

attribute [instance] instFintypePath

variable {R : Type u} {ι : Type v}
variable [Fintype ι] [DecidableEq ι]

/-- A path family realizing the sink permutation `σ`. -/
abbrev PathFamily (N : FinitePathNetwork R ι) (σ : Equiv.Perm ι) :=
  ∀ i : ι, N.Path i (σ i)

instance instFintypePathFamily (N : FinitePathNetwork R ι) (σ : Equiv.Perm ι) :
    Fintype (N.PathFamily σ) := by
  dsimp [PathFamily]
  infer_instance

/-- A path family together with the permutation it realizes. -/
abbrev SignedPathFamily (N : FinitePathNetwork R ι) :=
  Σ σ : Equiv.Perm ι, N.PathFamily σ

instance instFintypeSignedPathFamily (N : FinitePathNetwork R ι) :
    Fintype N.SignedPathFamily := by
  dsimp [SignedPathFamily]
  infer_instance

/-- The path matrix of a finite weighted path network. -/
def matrix [AddCommMonoid R] (N : FinitePathNetwork R ι) : Matrix ι ι R :=
  fun s t => ∑ p : N.Path s t, N.weight p

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem matrix_apply [AddCommMonoid R] (N : FinitePathNetwork R ι)
    (s t : ι) :
    N.matrix s t = ∑ p : N.Path s t, N.weight p :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- A nonzero path-matrix entry has at least one path with nonzero weight. -/
theorem exists_weight_ne_zero_of_matrix_ne_zero [AddCommMonoid R]
    (N : FinitePathNetwork R ι) {s t : ι}
    (hentry : N.matrix s t ≠ 0) :
    ∃ p : N.Path s t, N.weight p ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  exact hentry (by simp [matrix, hnone])

omit [Fintype ι] [DecidableEq ι] in
/-- A nonzero path-matrix entry has a path realizing that entry. -/
theorem nonempty_path_of_matrix_ne_zero [AddCommMonoid R]
    (N : FinitePathNetwork R ι) {s t : ι}
    (hentry : N.matrix s t ≠ 0) :
    Nonempty (N.Path s t) := by
  rcases N.exists_weight_ne_zero_of_matrix_ne_zero hentry with ⟨p, _hp⟩
  exact ⟨p⟩

/-- Multiplicative weight of a path family. -/
def familyWeight [CommMonoid R] (N : FinitePathNetwork R ι)
    {σ : Equiv.Perm ι} (family : N.PathFamily σ) : R :=
  ∏ i : ι, N.weight (family i)

omit [DecidableEq ι] in
@[simp] theorem familyWeight_apply [CommMonoid R] (N : FinitePathNetwork R ι)
    {σ : Equiv.Perm ι} (family : N.PathFamily σ) :
    N.familyWeight family = ∏ i : ι, N.weight (family i) :=
  rfl

omit [DecidableEq ι] in
/-- A nonzero family product is exactly pointwise nonzero path weight. -/
theorem familyWeight_ne_zero_iff
    [CommMonoidWithZero R] [Nontrivial R] [NoZeroDivisors R]
    (N : FinitePathNetwork R ι) {σ : Equiv.Perm ι}
    (family : N.PathFamily σ) :
    N.familyWeight family ≠ 0 ↔ ∀ i : ι, N.weight (family i) ≠ 0 := by
  simpa [familyWeight] using
    (Finset.prod_ne_zero_iff
      (s := (Finset.univ : Finset ι))
      (f := fun i : ι => N.weight (family i)))

omit [DecidableEq ι] in
/-- A nonzero family product gives nonzero weight for every path in it. -/
theorem weight_ne_zero_of_familyWeight_ne_zero
    [CommMonoidWithZero R] [Nontrivial R] [NoZeroDivisors R]
    (N : FinitePathNetwork R ι) {σ : Equiv.Perm ι}
    (family : N.PathFamily σ)
    (hfamily : N.familyWeight family ≠ 0) (i : ι) :
    N.weight (family i) ≠ 0 :=
  (N.familyWeight_ne_zero_iff family).mp hfamily i

omit [DecidableEq ι] in
/--
Pointwise nonzero path choices can be assembled into a path family with
nonzero product weight.
-/
theorem exists_pathFamily_familyWeight_ne_zero_of_forall_exists_weight_ne_zero
    [CommMonoidWithZero R] [Nontrivial R] [NoZeroDivisors R]
    (N : FinitePathNetwork R ι) {σ : Equiv.Perm ι}
    (hpath : ∀ i : ι, ∃ p : N.Path i (σ i), N.weight p ≠ 0) :
    ∃ family : N.PathFamily σ, N.familyWeight family ≠ 0 := by
  classical
  choose family hfamily using hpath
  refine ⟨family, ?_⟩
  exact (N.familyWeight_ne_zero_iff family).mpr hfamily

omit [DecidableEq ι] in
/-- Pointwise equality of path weights gives equality of family weights. -/
theorem familyWeight_eq_of_weight_eq [CommMonoid R]
    (N : FinitePathNetwork R ι) {σ τ : Equiv.Perm ι}
    (family : N.PathFamily σ) (swapped : N.PathFamily τ)
    (hweight : ∀ i : ι, N.weight (swapped i) = N.weight (family i)) :
    N.familyWeight swapped = N.familyWeight family := by
  simp [familyWeight, hweight]

omit [DecidableEq ι] in
/--
Family weight is unchanged if the transformed path weights agree with the
original path weights after a permutation of the source indices.
-/
theorem familyWeight_eq_of_weight_perm [CommMonoid R]
    (N : FinitePathNetwork R ι) {σ τ : Equiv.Perm ι}
    (family : N.PathFamily σ) (swapped : N.PathFamily τ)
    (π : Equiv.Perm ι)
    (hweight : ∀ i : ι, N.weight (swapped i) = N.weight (family (π i))) :
    N.familyWeight swapped = N.familyWeight family := by
  calc
    N.familyWeight swapped = ∏ i : ι, N.weight (family (π i)) := by
      simp [familyWeight, hweight]
    _ = N.familyWeight family := by
      simpa [familyWeight] using
        (Equiv.prod_comp π (fun i : ι => N.weight (family i)))

/-- Signed multiplicative weight of a path family carrying its permutation. -/
def signedFamilyWeight [CommRing R] (N : FinitePathNetwork R ι)
    (family : N.SignedPathFamily) : R :=
  Equiv.Perm.sign family.1 • N.familyWeight family.2

@[simp] theorem signedFamilyWeight_apply [CommRing R] (N : FinitePathNetwork R ι)
    (family : N.SignedPathFamily) :
    N.signedFamilyWeight family =
      Equiv.Perm.sign family.1 • N.familyWeight family.2 :=
  rfl

/-- A path family with nonzero product has nonzero signed family weight. -/
theorem signedFamilyWeight_ne_zero_of_familyWeight_ne_zero [CommRing R]
    (N : FinitePathNetwork R ι) {σ : Equiv.Perm ι}
    (family : N.PathFamily σ)
    (hfamily : N.familyWeight family ≠ 0) :
    N.signedFamilyWeight ⟨σ, family⟩ ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hsign | hsign
  · simpa [signedFamilyWeight, hsign] using hfamily
  · simpa [signedFamilyWeight, hsign] using hfamily

/-- A nonzero signed family weight has nonzero underlying family product. -/
theorem familyWeight_ne_zero_of_signedFamilyWeight_ne_zero [CommRing R]
    (N : FinitePathNetwork R ι) (family : N.SignedPathFamily)
    (hfamily : N.signedFamilyWeight family ≠ 0) :
    N.familyWeight family.2 ≠ 0 :=
  right_ne_zero_of_smul (by simpa using hfamily)

/-- A nonzero signed family weight gives nonzero weight for each path. -/
theorem weight_ne_zero_of_signedFamilyWeight_ne_zero
    [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (N : FinitePathNetwork R ι) (family : N.SignedPathFamily)
    (hfamily : N.signedFamilyWeight family ≠ 0) (i : ι) :
    N.weight (family.2 i) ≠ 0 :=
  N.weight_ne_zero_of_familyWeight_ne_zero family.2
    (N.familyWeight_ne_zero_of_signedFamilyWeight_ne_zero family hfamily) i

/--
Pointwise nonzero path choices can be assembled into a signed path family with
the prescribed permutation and nonzero signed weight.
-/
theorem exists_signedPathFamily_signedFamilyWeight_ne_zero_of_forall_exists_weight_ne_zero
    [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (N : FinitePathNetwork R ι) {σ : Equiv.Perm ι}
    (hpath : ∀ i : ι, ∃ p : N.Path i (σ i), N.weight p ≠ 0) :
    ∃ family : N.SignedPathFamily,
      family.1 = σ ∧ N.signedFamilyWeight family ≠ 0 := by
  rcases N.exists_pathFamily_familyWeight_ne_zero_of_forall_exists_weight_ne_zero
      hpath with ⟨family, hfamily⟩
  refine ⟨⟨σ, family⟩, rfl, ?_⟩
  exact N.signedFamilyWeight_ne_zero_of_familyWeight_ne_zero family hfamily

/--
If a transformation preserves the unsigned family product and negates the
permutation sign, then it negates the signed LGV family weight.
-/
theorem signedFamilyWeight_eq_neg_of_sign_eq_neg [CommRing R]
    (N : FinitePathNetwork R ι) {family swapped : N.SignedPathFamily}
    (hsign : Equiv.Perm.sign swapped.1 = -Equiv.Perm.sign family.1)
    (hweight : N.familyWeight swapped.2 = N.familyWeight family.2) :
    N.signedFamilyWeight swapped = -N.signedFamilyWeight family := by
  rw [signedFamilyWeight, signedFamilyWeight, hsign, hweight]
  simp

/--
Signed-weight negation when the swapped family has permutation obtained by a
left transposition and the unsigned product is unchanged.
-/
theorem signedFamilyWeight_eq_neg_of_left_swap [CommRing R]
    (N : FinitePathNetwork R ι) {family swapped : N.SignedPathFamily}
    {i j : ι} (hij : i ≠ j)
    (hperm : swapped.1 = Equiv.swap i j * family.1)
    (hweight : N.familyWeight swapped.2 = N.familyWeight family.2) :
    N.signedFamilyWeight swapped = -N.signedFamilyWeight family := by
  apply signedFamilyWeight_eq_neg_of_sign_eq_neg N
  · rw [hperm, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
    simp
  · exact hweight

/--
Signed-weight negation when the swapped family has permutation obtained by a
right transposition and the unsigned product is unchanged.

This is the form used by the usual first-intersection tail swap: the sources
are fixed and the two realized sinks are exchanged.
-/
theorem signedFamilyWeight_eq_neg_of_right_swap [CommRing R]
    (N : FinitePathNetwork R ι) {family swapped : N.SignedPathFamily}
    {i j : ι} (hij : i ≠ j)
    (hperm : swapped.1 = family.1 * Equiv.swap i j)
    (hweight : N.familyWeight swapped.2 = N.familyWeight family.2) :
    N.signedFamilyWeight swapped = -N.signedFamilyWeight family := by
  apply signedFamilyWeight_eq_neg_of_sign_eq_neg N
  · rw [hperm, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
    simp
  · exact hweight

/--
Convenience form of the sign-reversing cancellation obligation.

Concrete first-intersection tail-swap proofs usually show that the swapped
signed family weight is the negative of the original one.  This lemma turns
that statement into the `w + w' = 0` field expected by the bundled LGV
cancellation certificate.
-/
theorem signedFamilyWeight_add_eq_zero_of_swap_eq_neg [CommRing R]
    (N : FinitePathNetwork R ι) {family swapped : N.SignedPathFamily}
    (hweight : N.signedFamilyWeight swapped = -N.signedFamilyWeight family) :
    N.signedFamilyWeight family + N.signedFamilyWeight swapped = 0 := by
  rw [hweight, add_neg_cancel]

/--
For a fixed permutation, the product of the corresponding path-matrix entries
expands as the sum of weights of all path families realizing that permutation.
-/
theorem prod_matrix_apply_eq_sum_familyWeight [CommSemiring R]
    (N : FinitePathNetwork R ι) (σ : Equiv.Perm ι) :
    (∏ i : ι, N.matrix i (σ i)) =
      ∑ family : N.PathFamily σ, N.familyWeight family := by
  change (∏ i : ι, ∑ p : N.Path i (σ i), N.weight p) =
      ∑ family : (∀ i : ι, N.Path i (σ i)), ∏ i : ι, N.weight (family i)
  exact Fintype.prod_sum (fun i (p : N.Path i (σ i)) => N.weight p)

/--
The determinant of the path matrix as a signed sum over permutations and path
families.
-/
theorem det_matrix_eq_sum_pathFamilies [CommRing R]
    (N : FinitePathNetwork R ι) :
    Matrix.det N.matrix =
      ∑ σ : Equiv.Perm ι,
        Equiv.Perm.sign σ •
          (∑ family : N.PathFamily σ, N.familyWeight family) := by
  calc
    Matrix.det N.matrix = Matrix.det N.matrix.transpose :=
      (Matrix.det_transpose N.matrix).symm
    _ = ∑ σ : Equiv.Perm ι,
        Equiv.Perm.sign σ •
          (∑ family : N.PathFamily σ, N.familyWeight family) := by
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl ?_
      intro σ _hσ
      simp only [Matrix.transpose_apply]
      rw [prod_matrix_apply_eq_sum_familyWeight N σ]

/--
The determinant of the path matrix as a single signed sum over all path
families with their realized permutation.
-/
theorem det_matrix_eq_sum_signedPathFamilies [CommRing R]
    (N : FinitePathNetwork R ι) :
    Matrix.det N.matrix =
      ∑ family : N.SignedPathFamily, N.signedFamilyWeight family := by
  rw [det_matrix_eq_sum_pathFamilies]
  simp_rw [Finset.smul_sum]
  change (∑ σ : Equiv.Perm ι, ∑ family : N.PathFamily σ,
      Equiv.Perm.sign σ • N.familyWeight family) =
    ∑ family : (Σ σ : Equiv.Perm ι, N.PathFamily σ), N.signedFamilyWeight family
  exact (Fintype.sum_sigma'
    (fun σ (family : N.PathFamily σ) =>
      Equiv.Perm.sign σ • N.familyWeight family)).symm

/--
LGV cancellation form.

If the complement of `Good` has a sign-reversing involution, then the
determinant is the signed sum over the good path families only.  In the
classical theorem, `Good` will be the vertex-disjoint path families, and the
involution is the first-intersection tail swap.
-/
theorem det_matrix_eq_sum_goodFamilies_of_bad_involution [CommRing R]
    (N : FinitePathNetwork R ι) (Good : N.SignedPathFamily → Prop)
    [DecidablePred Good]
    (swap : {family : N.SignedPathFamily // ¬ Good family} →
      {family : N.SignedPathFamily // ¬ Good family})
    (hcancel : ∀ b, N.signedFamilyWeight b.1 +
      N.signedFamilyWeight (swap b).1 = 0)
    (hfixed : ∀ b, N.signedFamilyWeight b.1 ≠ 0 → swap b ≠ b)
    (hinvol : ∀ b, swap (swap b) = b) :
    Matrix.det N.matrix =
      ∑ family : {family : N.SignedPathFamily // Good family},
        N.signedFamilyWeight family.1 := by
  rw [det_matrix_eq_sum_signedPathFamilies]
  have hbad : (∑ family : {family : N.SignedPathFamily // ¬ Good family},
      N.signedFamilyWeight family.1) = 0 := by
    exact sum_eq_zero_of_sign_reversing_involution
      (fun family : {family : N.SignedPathFamily // ¬ Good family} =>
        N.signedFamilyWeight family.1)
      swap hcancel hfixed hinvol
  have hsplit := Fintype.sum_subtype_add_sum_subtype Good
    (fun family : N.SignedPathFamily => N.signedFamilyWeight family)
  rw [← hsplit, hbad, add_zero]

/--
Planar-order LGV endgame.

After the bad families cancel, if every surviving good family realizes the
identity permutation, then the signs disappear and the determinant is the
ordinary sum of weights of the good identity families.
-/
theorem det_matrix_eq_sum_goodFamilies_of_bad_involution_of_identity [CommRing R]
    (N : FinitePathNetwork R ι) (Good : N.SignedPathFamily → Prop)
    [DecidablePred Good]
    (swap : {family : N.SignedPathFamily // ¬ Good family} →
      {family : N.SignedPathFamily // ¬ Good family})
    (hcancel : ∀ b, N.signedFamilyWeight b.1 +
      N.signedFamilyWeight (swap b).1 = 0)
    (hfixed : ∀ b, N.signedFamilyWeight b.1 ≠ 0 → swap b ≠ b)
    (hinvol : ∀ b, swap (swap b) = b)
    (hidentity : ∀ family : N.SignedPathFamily, Good family → family.1 = 1) :
    Matrix.det N.matrix =
      ∑ family : {family : N.SignedPathFamily // Good family},
        N.familyWeight family.1.2 := by
  rw [det_matrix_eq_sum_goodFamilies_of_bad_involution
    N Good swap hcancel hfixed hinvol]
  refine Finset.sum_congr rfl ?_
  intro family _hfamily
  simp [signedFamilyWeight, hidentity family.1 family.2]

end FinitePathNetwork

end

end LGV
