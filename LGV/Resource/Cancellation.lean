/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Resource.FamilySwap

/-!
# Cancellation from coherent resource selection

This file separates selection of a shared resource in each bad family from the
already checked explicit-witness family swap. A concrete model supplies the
selector and its coherence laws; the resulting bad-family involution is then
generic.
-/

namespace LGV

noncomputable section

universe u l

namespace ResourcePathNetwork

variable {R : Type u} {Resource : Type l} {n : ℕ}

section CommMonoid

variable [CommMonoid R] [DecidableEq Resource]

omit [CommMonoid R] in
/-- Shared-resource witnesses are determined by their data fields. -/
@[ext] theorem SharedResourceWitness.ext
    {N : ResourcePathNetwork R (Fin n) Resource}
    {family : N.toFinitePathNetwork.SignedPathFamily}
    {w₁ w₂ : SharedResourceWitness N family}
    (hleft : w₁.left = w₂.left)
    (hright : w₁.right = w₂.right)
    (hresource : w₁.resource = w₂.resource) : w₁ = w₂ := by
  cases w₁ with
  | mk left₁ right₁ hne₁ resource₁ hleft₁ hright₁ =>
    cases w₂ with
    | mk left₂ right₂ hne₂ resource₂ hleft₂ hright₂ =>
      dsimp only at hleft hright hresource
      subst left₂
      subst right₂
      subst resource₂
      rfl

/--
A coherent choice of shared-resource witness in every non-disjoint family.

The three coherence fields state that applying the selected swap preserves the
selected path indices and resource. Concrete path models must supply this data;
it is not asserted for arbitrary resource networks.
-/
structure ResourceCollisionSelector
    (N : ResourcePathNetwork R (Fin n) Resource)
    (C : ResourceSwapCertificate N) where
  select : ∀ (family : N.toFinitePathNetwork.SignedPathFamily),
    ¬ N.SignedPairwiseResourceDisjoint family →
      SharedResourceWitness N family
  left_after_swap : ∀ (family : N.toFinitePathNetwork.SignedPathFamily)
      (hbad : ¬ N.SignedPairwiseResourceDisjoint family),
    let w := select family hbad
    let swapped := C.swapSignedFamilyAt family w
    let hbad' := (w.afterSwap C).not_signedPairwiseResourceDisjoint
    (select swapped hbad').left = w.left
  right_after_swap : ∀ (family : N.toFinitePathNetwork.SignedPathFamily)
      (hbad : ¬ N.SignedPairwiseResourceDisjoint family),
    let w := select family hbad
    let swapped := C.swapSignedFamilyAt family w
    let hbad' := (w.afterSwap C).not_signedPairwiseResourceDisjoint
    (select swapped hbad').right = w.right
  resource_after_swap : ∀ (family : N.toFinitePathNetwork.SignedPathFamily)
      (hbad : ¬ N.SignedPairwiseResourceDisjoint family),
    let w := select family hbad
    let swapped := C.swapSignedFamilyAt family w
    let hbad' := (w.afterSwap C).not_signedPairwiseResourceDisjoint
    (select swapped hbad').resource = w.resource

/-- A signed path family with a shared resource between two distinct paths. -/
abbrev BadSignedPathFamily (N : ResourcePathNetwork R (Fin n) Resource) :=
  {family : N.toFinitePathNetwork.SignedPathFamily //
    ¬ N.SignedPairwiseResourceDisjoint family}

/-- Swapping at a shared-resource witness changes the signed family. -/
theorem ResourceSwapCertificate.swapSignedFamilyAt_ne
    {N : ResourcePathNetwork R (Fin n) Resource}
    (C : ResourceSwapCertificate N)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (w : SharedResourceWitness N family) :
    C.swapSignedFamilyAt family w ≠ family := by
  intro heq
  have hperm := congrArg (fun f => f.1 w.left) heq
  have hright_left : w.right = w.left := family.1.injective (by
    simpa [Equiv.Perm.mul_apply] using hperm)
  exact w.left_ne_right hright_left.symm

namespace ResourceCollisionSelector

variable {N : ResourcePathNetwork R (Fin n) Resource}
    {C : ResourceSwapCertificate N}

/-- Apply the local swap at the witness selected for a bad family. -/
def swapFamily (S : ResourceCollisionSelector N C)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬ N.SignedPairwiseResourceDisjoint family) :
    N.toFinitePathNetwork.SignedPathFamily :=
  C.swapSignedFamilyAt family (S.select family hbad)

/-- The family selected for swapping remains non-resource-disjoint. -/
theorem not_disjoint_swapFamily (S : ResourceCollisionSelector N C)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬ N.SignedPairwiseResourceDisjoint family) :
    ¬ N.SignedPairwiseResourceDisjoint (S.swapFamily family hbad) :=
  ((S.select family hbad).afterSwap C).not_signedPairwiseResourceDisjoint

/-- The selected witness after swapping is the transported original witness. -/
theorem select_swapFamily (S : ResourceCollisionSelector N C)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬ N.SignedPairwiseResourceDisjoint family) :
    S.select (S.swapFamily family hbad)
        (S.not_disjoint_swapFamily family hbad) =
      (S.select family hbad).afterSwap C := by
  apply SharedResourceWitness.ext
  · exact S.left_after_swap family hbad
  · exact S.right_after_swap family hbad
  · exact S.resource_after_swap family hbad

/-- The coherent selected swap restores the original signed family. -/
theorem swapFamily_twice (S : ResourceCollisionSelector N C)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬ N.SignedPairwiseResourceDisjoint family) :
    S.swapFamily (S.swapFamily family hbad)
        (S.not_disjoint_swapFamily family hbad) = family := by
  rw [swapFamily, S.select_swapFamily family hbad]
  exact C.swapSignedFamilyAt_twice family (S.select family hbad)

/-- The selected swap on bad families. -/
def badFamilySwap (S : ResourceCollisionSelector N C) :
    BadSignedPathFamily N → BadSignedPathFamily N :=
  fun family => ⟨S.swapFamily family.1 family.2,
    S.not_disjoint_swapFamily family.1 family.2⟩

@[simp] theorem badFamilySwap_val (S : ResourceCollisionSelector N C)
    (family : BadSignedPathFamily N) :
    (S.badFamilySwap family).1 = S.swapFamily family.1 family.2 :=
  rfl

/-- The selected bad-family swap has no fixed point. -/
theorem badFamilySwap_ne (S : ResourceCollisionSelector N C)
    (family : BadSignedPathFamily N) :
    S.badFamilySwap family ≠ family := by
  intro heq
  apply C.swapSignedFamilyAt_ne family.1 (S.select family.1 family.2)
  exact congrArg Subtype.val heq

/-- The selected swap is an involution on bad signed families. -/
theorem badFamilySwap_involutive (S : ResourceCollisionSelector N C)
    (family : BadSignedPathFamily N) :
    S.badFamilySwap (S.badFamilySwap family) = family := by
  apply Subtype.ext
  exact S.swapFamily_twice family.1 family.2

end ResourceCollisionSelector

end CommMonoid

section CommRing

variable [CommRing R] [DecidableEq Resource]

/-- The cancellation data on non-resource-disjoint signed path families. -/
structure ResourceFamilyCancellationCertificate
    (N : ResourcePathNetwork R (Fin n) Resource) where
  swap : BadSignedPathFamily N → BadSignedPathFamily N
  weight_swap : ∀ family,
    N.toFinitePathNetwork.signedFamilyWeight (swap family).1 =
      -N.toFinitePathNetwork.signedFamilyWeight family.1
  ne_fixed_of_weight_ne_zero : ∀ family,
    N.toFinitePathNetwork.signedFamilyWeight family.1 ≠ 0 →
      swap family ≠ family
  involutive : ∀ family, swap (swap family) = family

namespace ResourceCollisionSelector

variable {N : ResourcePathNetwork R (Fin n) Resource}
    {C : ResourceSwapCertificate N}

/-- The selected bad-family swap negates signed family weight. -/
theorem signedFamilyWeight_badFamilySwap
    (S : ResourceCollisionSelector N C) (family : BadSignedPathFamily N) :
    N.toFinitePathNetwork.signedFamilyWeight (S.badFamilySwap family).1 =
      -N.toFinitePathNetwork.signedFamilyWeight family.1 :=
  C.signedFamilyWeight_swapSignedFamilyAt family.1
    (S.select family.1 family.2)

/-- Package a coherent selector as reusable bad-family cancellation data. -/
def cancellationCertificate (S : ResourceCollisionSelector N C) :
    ResourceFamilyCancellationCertificate N where
  swap := S.badFamilySwap
  weight_swap := S.signedFamilyWeight_badFamilySwap
  ne_fixed_of_weight_ne_zero := fun family _ => S.badFamilySwap_ne family
  involutive := S.badFamilySwap_involutive

end ResourceCollisionSelector

end CommRing

end ResourcePathNetwork

end

end LGV
