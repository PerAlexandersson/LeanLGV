/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Resource.Basic

/-!
# Resource-disjoint paths

This file characterizes disjoint finite resource supports by the absence of a
shared resource. The results apply to paths with arbitrary endpoints.
-/

namespace LGV

noncomputable section

universe u v l

namespace ResourcePathNetwork

variable {R : Type u} {ι : Type v} {Resource : Type l}

/-- Two paths are resource-disjoint when their finite supports are disjoint. -/
def ResourceDisjoint [DecidableEq Resource]
    (N : ResourcePathNetwork R ι Resource) {s₁ t₁ s₂ t₂ : ι}
    (p : N.Path s₁ t₁) (q : N.Path s₂ t₂) : Prop :=
  Disjoint (N.resources p) (N.resources q)

@[simp] theorem resourceDisjoint_iff [DecidableEq Resource]
    (N : ResourcePathNetwork R ι Resource) {s₁ t₁ s₂ t₂ : ι}
    (p : N.Path s₁ t₁) (q : N.Path s₂ t₂) :
    N.ResourceDisjoint p q ↔ Disjoint (N.resources p) (N.resources q) :=
  Iff.rfl

/-- A shared resource contradicts resource-disjointness. -/
theorem not_resourceDisjoint_of_shared [DecidableEq Resource]
    (N : ResourcePathNetwork R ι Resource) {s₁ t₁ s₂ t₂ : ι}
    {p : N.Path s₁ t₁} {q : N.Path s₂ t₂} {resource : Resource}
    (hp : N.Uses p resource) (hq : N.Uses q resource) :
    ¬ N.ResourceDisjoint p q := by
  rw [ResourceDisjoint, Finset.not_disjoint_iff_nonempty_inter]
  exact ⟨resource, Finset.mem_inter.mpr ⟨hp, hq⟩⟩

/-- Failure of resource-disjointness supplies a shared resource. -/
theorem exists_shared_of_not_resourceDisjoint [DecidableEq Resource]
    (N : ResourcePathNetwork R ι Resource) {s₁ t₁ s₂ t₂ : ι}
    (p : N.Path s₁ t₁) (q : N.Path s₂ t₂)
    (hbad : ¬ N.ResourceDisjoint p q) :
    ∃ resource : Resource, N.Uses p resource ∧ N.Uses q resource := by
  rw [ResourceDisjoint, Finset.not_disjoint_iff_nonempty_inter] at hbad
  rcases hbad with ⟨resource, hresource⟩
  exact ⟨resource, Finset.mem_inter.mp hresource⟩

/-- Non-disjointness is exactly the existence of a shared resource. -/
theorem not_resourceDisjoint_iff_exists_shared [DecidableEq Resource]
    (N : ResourcePathNetwork R ι Resource) {s₁ t₁ s₂ t₂ : ι}
    (p : N.Path s₁ t₁) (q : N.Path s₂ t₂) :
    ¬ N.ResourceDisjoint p q ↔
      ∃ resource : Resource, N.Uses p resource ∧ N.Uses q resource := by
  constructor
  · exact N.exists_shared_of_not_resourceDisjoint p q
  · rintro ⟨resource, hp, hq⟩
    exact N.not_resourceDisjoint_of_shared hp hq

/--
Resource-disjointness can equivalently be proved by excluding every possible
shared resource.
-/
theorem resourceDisjoint_iff_forall_not_shared [DecidableEq Resource]
    (N : ResourcePathNetwork R ι Resource) {s₁ t₁ s₂ t₂ : ι}
    (p : N.Path s₁ t₁) (q : N.Path s₂ t₂) :
    N.ResourceDisjoint p q ↔
      ∀ resource : Resource,
        N.Uses p resource → N.Uses q resource → False := by
  constructor
  · intro hdisjoint resource hp hq
    exact N.not_resourceDisjoint_of_shared hp hq hdisjoint
  · intro hnotShared
    by_contra hbad
    rcases N.exists_shared_of_not_resourceDisjoint p q hbad with
      ⟨resource, hp, hq⟩
    exact hnotShared resource hp hq

/-- Resource-disjointness is symmetric. -/
theorem resourceDisjoint_comm [DecidableEq Resource]
    (N : ResourcePathNetwork R ι Resource) {s₁ t₁ s₂ t₂ : ι}
    {p : N.Path s₁ t₁} {q : N.Path s₂ t₂} :
    N.ResourceDisjoint p q ↔ N.ResourceDisjoint q p := by
  simp only [ResourceDisjoint, disjoint_comm]

end ResourcePathNetwork

end

end LGV
