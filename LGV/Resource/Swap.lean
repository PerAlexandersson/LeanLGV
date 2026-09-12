/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Resource.Disjoint

/-!
# Local swaps at shared resources

This file specifies the local operation required by resource-based LGV
cancellation. A swap exchanges the two path endpoints at a chosen common
resource, preserves that common resource and the product of path weights, and
is involutive when repeated at the same resource.

The certificate is an input interface for concrete path models. It does not
assert that every resource network admits such a swap.
-/

namespace LGV

noncomputable section

universe u v l

namespace ResourcePathNetwork

variable {R : Type u} {ι : Type v} {Resource : Type l}
variable [CommMonoid R] [DecidableEq Resource]

/-- The output and local laws of swapping two paths at a shared resource. -/
structure ResourceSwapResult (N : ResourcePathNetwork R ι Resource)
    {s₁ t₁ s₂ t₂ : ι} (p : N.Path s₁ t₁) (q : N.Path s₂ t₂)
    (resource : Resource) where
  first : N.Path s₁ t₂
  second : N.Path s₂ t₁
  first_uses : N.Uses first resource
  second_uses : N.Uses second resource
  weight_mul : N.weight first * N.weight second = N.weight p * N.weight q

/--
A coherent local tail-swap operation for every pair of paths sharing a
resource.
-/
structure ResourceSwapCertificate (N : ResourcePathNetwork R ι Resource) where
  swap : ∀ {s₁ t₁ s₂ t₂ : ι}
      (p : N.Path s₁ t₁) (q : N.Path s₂ t₂) (resource : Resource),
    N.Uses p resource → N.Uses q resource →
      ResourceSwapResult N p q resource
  first_twice : ∀ {s₁ t₁ s₂ t₂ : ι}
      (p : N.Path s₁ t₁) (q : N.Path s₂ t₂) (resource : Resource)
      (hp : N.Uses p resource) (hq : N.Uses q resource),
    let swapped := swap p q resource hp hq
    let restored := swap swapped.first swapped.second resource
      swapped.first_uses swapped.second_uses
    restored.first = p
  second_twice : ∀ {s₁ t₁ s₂ t₂ : ι}
      (p : N.Path s₁ t₁) (q : N.Path s₂ t₂) (resource : Resource)
      (hp : N.Uses p resource) (hq : N.Uses q resource),
    let swapped := swap p q resource hp hq
    let restored := swap swapped.first swapped.second resource
      swapped.first_uses swapped.second_uses
    restored.second = q

namespace ResourceSwapCertificate

variable {N : ResourcePathNetwork R ι Resource}

/-- The selected resource remains shared after a certified local swap. -/
theorem uses_after_swap (C : ResourceSwapCertificate N)
    {s₁ t₁ s₂ t₂ : ι} (p : N.Path s₁ t₁) (q : N.Path s₂ t₂)
    (resource : Resource) (hp : N.Uses p resource)
    (hq : N.Uses q resource) :
    N.Uses (C.swap p q resource hp hq).first resource ∧
      N.Uses (C.swap p q resource hp hq).second resource :=
  ⟨(C.swap p q resource hp hq).first_uses,
    (C.swap p q resource hp hq).second_uses⟩

/-- A certified local swap preserves the product of the two path weights. -/
theorem weight_mul_swap (C : ResourceSwapCertificate N)
    {s₁ t₁ s₂ t₂ : ι} (p : N.Path s₁ t₁) (q : N.Path s₂ t₂)
    (resource : Resource) (hp : N.Uses p resource)
    (hq : N.Uses q resource) :
    N.weight (C.swap p q resource hp hq).first *
        N.weight (C.swap p q resource hp hq).second =
      N.weight p * N.weight q :=
  (C.swap p q resource hp hq).weight_mul

end ResourceSwapCertificate

end ResourcePathNetwork

end

end LGV
