/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Finite

/-!
# Finite resource-labelled path networks

This file adds finite resource support to the abstract path networks from
`LGV.Finite`. It deliberately contains no disjointness or cancellation API:
those consequences belong in later resource modules.
-/

namespace LGV

noncomputable section

universe u v w l x

/--
A finite weighted path network together with the finite set of resources used
by each path.

The underlying network remains the source of the path types and weights. The
resource type is otherwise unconstrained, so a concrete model may use vertices,
edges, cells, or application-specific labels.
-/
structure ResourcePathNetwork (R : Type u) (ι : Type v) (Resource : Type l)
    extends FinitePathNetwork.{u, v, w} R ι where
  resources : ∀ {s t : ι}, Path s t → Finset Resource

namespace ResourcePathNetwork

variable {R : Type u} {ι : Type v} {Resource : Type l}

@[simp] theorem toFinitePathNetwork_path
    (N : ResourcePathNetwork R ι Resource) (s t : ι) :
    N.toFinitePathNetwork.Path s t = N.Path s t :=
  rfl

@[simp] theorem toFinitePathNetwork_weight
    (N : ResourcePathNetwork R ι Resource) {s t : ι}
    (p : N.Path s t) :
    N.toFinitePathNetwork.weight p = N.weight p :=
  rfl

/-- Whether a path uses a given resource. -/
def Uses [DecidableEq Resource] (N : ResourcePathNetwork R ι Resource)
    {s t : ι} (p : N.Path s t) (resource : Resource) : Prop :=
  resource ∈ N.resources p

@[simp] theorem uses_iff [DecidableEq Resource]
    (N : ResourcePathNetwork R ι Resource) {s t : ι}
    (p : N.Path s t) (resource : Resource) :
    N.Uses p resource ↔ resource ∈ N.resources p :=
  Iff.rfl

/-- The resources used by a path form a finite set. -/
theorem finite_setOf_uses [DecidableEq Resource]
    (N : ResourcePathNetwork R ι Resource) {s t : ι}
    (p : N.Path s t) :
    Set.Finite {resource : Resource | N.Uses p resource} := by
  exact (N.resources p).finite_toSet

/-- Resource supports agree exactly when they have the same members. -/
theorem resources_eq_iff [DecidableEq Resource]
    (N : ResourcePathNetwork R ι Resource)
    {s₁ t₁ s₂ t₂ : ι} (p : N.Path s₁ t₁) (q : N.Path s₂ t₂) :
    N.resources p = N.resources q ↔
      ∀ resource : Resource,
        N.Uses p resource ↔ N.Uses q resource := by
  simp only [Uses, Finset.ext_iff]

/-- Restrict or reindex the source and sink labels of a resource network. -/
def reindex {κ : Type x} (N : ResourcePathNetwork R ι Resource)
    (source sink : κ → ι) : ResourcePathNetwork R κ Resource where
  toFinitePathNetwork := N.toFinitePathNetwork.reindex source sink
  resources := N.resources

@[simp] theorem reindex_toFinitePathNetwork {κ : Type x}
    (N : ResourcePathNetwork R ι Resource) (source sink : κ → ι) :
    (N.reindex source sink).toFinitePathNetwork =
      N.toFinitePathNetwork.reindex source sink :=
  rfl

@[simp] theorem reindex_weight {κ : Type x}
    (N : ResourcePathNetwork R ι Resource) (source sink : κ → ι)
    {i j : κ} (p : (N.reindex source sink).Path i j) :
    (N.reindex source sink).weight p = N.weight p :=
  rfl

@[simp] theorem reindex_resources {κ : Type x}
    (N : ResourcePathNetwork R ι Resource) (source sink : κ → ι)
    {i j : κ} (p : (N.reindex source sink).Path i j) :
    (N.reindex source sink).resources p = N.resources p :=
  rfl

end ResourcePathNetwork

end

end LGV
