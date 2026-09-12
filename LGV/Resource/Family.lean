/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Ordered
import LGV.Resource.Disjoint

/-!
# Resource-disjoint path families

This file lifts resource-disjointness from two paths to signed finite path
families and connects it to the abstract predicate used by `LGV.Ordered`.
-/

namespace LGV

noncomputable section

universe u l

namespace ResourcePathNetwork

variable {R : Type u} {Resource : Type l} {n : ℕ}

/-- Every two differently indexed paths in the family have disjoint resources. -/
def SignedPairwiseResourceDisjoint [DecidableEq Resource]
    (N : ResourcePathNetwork R (Fin n) Resource)
    (family : N.toFinitePathNetwork.SignedPathFamily) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    N.ResourceDisjoint (family.2 i) (family.2 j)

/--
Resource-disjointness is the specialization of the abstract signed-family
predicate to disjoint finite resource supports.
-/
theorem signedPairwiseResourceDisjoint_iff [DecidableEq Resource]
    (N : ResourcePathNetwork R (Fin n) Resource)
    (family : N.toFinitePathNetwork.SignedPathFamily) :
    N.SignedPairwiseResourceDisjoint family ↔
      FinitePathNetwork.SignedPairwiseDisjoint
        N.toFinitePathNetwork N.ResourceDisjoint family :=
  Iff.rfl

/-- Supply the abstract ordered-LGV predicate from resource support data. -/
theorem toSignedPairwiseDisjoint [DecidableEq Resource]
    (N : ResourcePathNetwork R (Fin n) Resource)
    {family : N.toFinitePathNetwork.SignedPathFamily}
    (hfamily : N.SignedPairwiseResourceDisjoint family) :
    FinitePathNetwork.SignedPairwiseDisjoint
      N.toFinitePathNetwork N.ResourceDisjoint family :=
  (N.signedPairwiseResourceDisjoint_iff family).mp hfamily

/-- Resource pairwise-disjointness of signed families is decidable. -/
instance instDecidablePredSignedPairwiseResourceDisjoint
    [DecidableEq Resource] (N : ResourcePathNetwork R (Fin n) Resource) :
    DecidablePred N.SignedPairwiseResourceDisjoint := by
  intro family
  unfold SignedPairwiseResourceDisjoint ResourceDisjoint
  infer_instance

/-- A concrete shared resource between two differently indexed family paths. -/
structure SharedResourceWitness [DecidableEq Resource]
    (N : ResourcePathNetwork R (Fin n) Resource)
    (family : N.toFinitePathNetwork.SignedPathFamily) where
  left : Fin n
  right : Fin n
  left_ne_right : left ≠ right
  resource : Resource
  left_uses : N.Uses (family.2 left) resource
  right_uses : N.Uses (family.2 right) resource

namespace SharedResourceWitness

variable [DecidableEq Resource]
    {N : ResourcePathNetwork R (Fin n) Resource}
    {family : N.toFinitePathNetwork.SignedPathFamily}

/-- Reverse the two indexed paths in a shared-resource witness. -/
def symm (w : SharedResourceWitness N family) :
    SharedResourceWitness N family where
  left := w.right
  right := w.left
  left_ne_right := w.left_ne_right.symm
  resource := w.resource
  left_uses := w.right_uses
  right_uses := w.left_uses

@[simp] theorem symm_left (w : SharedResourceWitness N family) :
    w.symm.left = w.right :=
  rfl

@[simp] theorem symm_right (w : SharedResourceWitness N family) :
    w.symm.right = w.left :=
  rfl

@[simp] theorem symm_resource (w : SharedResourceWitness N family) :
    w.symm.resource = w.resource :=
  rfl

/-- A shared-resource witness proves failure of resource pairwise-disjointness. -/
theorem not_signedPairwiseResourceDisjoint
    (w : SharedResourceWitness N family) :
    ¬ N.SignedPairwiseResourceDisjoint family := by
  intro hfamily
  exact N.not_resourceDisjoint_of_shared w.left_uses w.right_uses
    (hfamily w.left w.right w.left_ne_right)

end SharedResourceWitness

/-- Every bad signed family has a concrete shared-resource witness. -/
theorem nonempty_sharedResourceWitness_of_not_signedPairwiseResourceDisjoint
    [DecidableEq Resource] (N : ResourcePathNetwork R (Fin n) Resource)
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬ N.SignedPairwiseResourceDisjoint family) :
    Nonempty (SharedResourceWitness N family) := by
  classical
  unfold SignedPairwiseResourceDisjoint at hbad
  push Not at hbad
  rcases hbad with ⟨left, right, hne, hdisjoint⟩
  rcases N.exists_shared_of_not_resourceDisjoint
      (family.2 left) (family.2 right) hdisjoint with
    ⟨resource, hleft, hright⟩
  exact ⟨⟨left, right, hne, resource, hleft, hright⟩⟩

/-- A signed family is bad exactly when it has a shared-resource witness. -/
theorem not_signedPairwiseResourceDisjoint_iff_nonempty_witness
    [DecidableEq Resource] (N : ResourcePathNetwork R (Fin n) Resource)
    (family : N.toFinitePathNetwork.SignedPathFamily) :
    ¬ N.SignedPairwiseResourceDisjoint family ↔
      Nonempty (SharedResourceWitness N family) := by
  constructor
  · exact N.nonempty_sharedResourceWitness_of_not_signedPairwiseResourceDisjoint
      family
  · rintro ⟨witness⟩
    exact witness.not_signedPairwiseResourceDisjoint

end ResourcePathNetwork

end

end LGV
