/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Ordered
import LGV.Quiver.Path
import Mathlib.Combinatorics.Quiver.Path.Vertices
import Mathlib.Combinatorics.Quiver.Path.Weight

/-!
# Finite ranked quiver networks

This file turns a finite quiver with a strictly decreasing vertex rank into the
abstract finite path network used by `LGV.Finite`. It also defines the standard
vertex-disjointness relation and records the path-weight algebra used by a
tail swap.
-/

namespace LGV

open Quiver

noncomputable section

universe u v w

/-- A finite weighted quiver whose arrows strictly decrease a natural-valued
rank, with designated sources and sinks. -/
structure RankedQuiverNetwork (R : Type u) (V : Type v) (ι : Type w)
    [Quiver V] where
  source : ι → V
  sink : ι → V
  rank : V → ℕ
  rank_decreases : ∀ {a b : V}, (a ⟶ b) → rank b < rank a
  edgeWeight : ∀ {a b : V}, (a ⟶ b) → R

namespace RankedQuiverNetwork

variable {R : Type u} {V : Type v} {ι : Type w}
variable [Quiver V]

/-- Forget the quiver presentation and retain the finite path-network data. -/
def toFinitePathNetwork [Monoid R] [Fintype V]
    [∀ a b : V, Fintype (a ⟶ b)]
    (N : RankedQuiverNetwork R V ι) :
    FinitePathNetwork R ι where
  Path i j := Quiver.Path (N.source i) (N.sink j)
  instFintypePath i j :=
    Quiver.Path.fintypeOfRank N.rank N.rank_decreases (N.source i) (N.sink j)
  weight := Quiver.Path.weight N.edgeWeight

@[simp] theorem toFinitePathNetwork_weight
    [Monoid R] [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (N : RankedQuiverNetwork R V ι) {i j : ι}
    (p : Quiver.Path (N.source i) (N.sink j)) :
    N.toFinitePathNetwork.weight p = Quiver.Path.weight N.edgeWeight p :=
  rfl

/-- The total weight of all paths between two designated endpoints. -/
def pathSum [Semiring R] [Fintype V]
    [∀ a b : V, Fintype (a ⟶ b)]
    (N : RankedQuiverNetwork R V ι) (i j : ι) : R := by
  letI := Quiver.Path.fintypeOfRank N.rank N.rank_decreases
    (N.source i) (N.sink j)
  exact ∑ p : Quiver.Path (N.source i) (N.sink j),
    Quiver.Path.weight N.edgeWeight p

/-- The weighted path matrix of a ranked quiver network. -/
def pathMatrix [Semiring R] [Fintype V]
    [∀ a b : V, Fintype (a ⟶ b)]
    (N : RankedQuiverNetwork R V ι) :
    Matrix ι ι R :=
  N.toFinitePathNetwork.matrix

@[simp] theorem pathMatrix_apply [Semiring R] [Fintype V]
    [∀ a b : V, Fintype (a ⟶ b)]
    (N : RankedQuiverNetwork R V ι) (i j : ι) :
    N.pathMatrix i j = N.pathSum i j :=
  rfl

/-- The finite set of vertices visited by a quiver path, including endpoints. -/
def vertexFinset [DecidableEq V] {a b : V}
    (p : Quiver.Path a b) : Finset V :=
  p.vertices.toFinset

@[simp] theorem mem_vertexFinset [DecidableEq V]
    {a b : V} (p : Quiver.Path a b) (x : V) :
    x ∈ vertexFinset p ↔ x ∈ p.vertices := by
  simp [vertexFinset]

/-- Two paths are vertex-disjoint when their complete vertex sets are disjoint. -/
def VertexDisjoint [DecidableEq V] {a b c d : V}
    (p : Quiver.Path a b) (q : Quiver.Path c d) : Prop :=
  Disjoint (vertexFinset p) (vertexFinset q)

theorem vertexDisjoint_comm [DecidableEq V] {a b c d : V}
    (p : Quiver.Path a b) (q : Quiver.Path c d) :
    VertexDisjoint p q ↔ VertexDisjoint q p := by
  exact disjoint_comm

@[simp] theorem not_vertexDisjoint_iff [DecidableEq V] {a b c d : V}
    (p : Quiver.Path a b) (q : Quiver.Path c d) :
    ¬ VertexDisjoint p q ↔ ∃ x : V, x ∈ p.vertices ∧ x ∈ q.vertices := by
  simp only [VertexDisjoint, Finset.not_disjoint_iff]
  simp [vertexFinset]

/-- Pairwise vertex-disjointness, expressed through the abstract ordered LGV API. -/
def SignedVertexDisjoint [Monoid R] [Fintype V] [DecidableEq V]
    [∀ a b : V, Fintype (a ⟶ b)]
    {n : ℕ} (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily) : Prop :=
  FinitePathNetwork.SignedPairwiseDisjoint N.toFinitePathNetwork
    (fun p q => VertexDisjoint p q) family

instance instDecidablePredSignedVertexDisjoint [Monoid R]
    [Fintype V] [DecidableEq V] [∀ a b : V, Fintype (a ⟶ b)] {n : ℕ}
    (N : RankedQuiverNetwork R V (Fin n)) :
    DecidablePred N.SignedVertexDisjoint := by
  intro family
  unfold SignedVertexDisjoint FinitePathNetwork.SignedPairwiseDisjoint
    FinitePathNetwork.PairwiseDisjoint VertexDisjoint vertexFinset
  infer_instance

/-- Swapping the two tails of paths meeting at `x` preserves their combined
multiplicative weight. -/
theorem weight_comp_mul_weight_comp_eq_swap [CommMonoid R]
    (N : RankedQuiverNetwork R V ι) {a b c d x : V}
    (p₁ : Quiver.Path a x) (p₂ : Quiver.Path x b)
    (q₁ : Quiver.Path c x) (q₂ : Quiver.Path x d) :
    Quiver.Path.weight N.edgeWeight (p₁.comp p₂) *
        Quiver.Path.weight N.edgeWeight (q₁.comp q₂) =
      Quiver.Path.weight N.edgeWeight (p₁.comp q₂) *
        Quiver.Path.weight N.edgeWeight (q₁.comp p₂) := by
  simp only [Quiver.Path.weight_comp]
  ac_rfl

/-- Nonnegative edge weights give nonnegative weights to all paths. -/
theorem pathWeight_nonneg [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [Fintype V] [∀ a b : V, Fintype (a ⟶ b)]
    (N : RankedQuiverNetwork R V ι)
    (hweight : ∀ {a b : V} (e : a ⟶ b), 0 ≤ N.edgeWeight e)
    {i j : ι} (p : N.toFinitePathNetwork.Path i j) :
    0 ≤ N.toFinitePathNetwork.weight p := by
  simpa only [toFinitePathNetwork_weight] using
    Quiver.Path.weight_nonneg hweight p

end RankedQuiverNetwork

end

end LGV
