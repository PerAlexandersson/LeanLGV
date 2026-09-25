/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Quiver.LGV
import Mathlib.Data.Fintype.OfMap

/-!
# A tiny ranked-quiver consumer

This file is a deliberately small end-to-end example. Two sources feed one
middle vertex, which feeds two sinks. The middle vertex certifies the ordered
two-path obstruction, and the final theorem invokes ranked-quiver LGV
nonnegativity with unit edge weights.
-/

namespace LGV

open Quiver

noncomputable section

namespace RankedQuiverExample

inductive Vertex where
  | sourceZero
  | sourceOne
  | middle
  | sinkZero
  | sinkOne
  deriving DecidableEq

instance : Fintype Vertex :=
  Fintype.ofList
    [Vertex.sourceZero, Vertex.sourceOne, Vertex.middle,
      Vertex.sinkZero, Vertex.sinkOne]
    (by
      intro x
      cases x <;> simp)

inductive Edge where
  | sourceZeroMiddle
  | sourceOneMiddle
  | middleSinkZero
  | middleSinkOne
  deriving DecidableEq

instance : Fintype Edge :=
  Fintype.ofList
    [Edge.sourceZeroMiddle, Edge.sourceOneMiddle,
      Edge.middleSinkZero, Edge.middleSinkOne]
    (by
      intro e
      cases e <;> simp)

def edgeSource : Edge → Vertex
  | .sourceZeroMiddle => .sourceZero
  | .sourceOneMiddle => .sourceOne
  | .middleSinkZero => .middle
  | .middleSinkOne => .middle

def edgeTarget : Edge → Vertex
  | .sourceZeroMiddle => .middle
  | .sourceOneMiddle => .middle
  | .middleSinkZero => .sinkZero
  | .middleSinkOne => .sinkOne

instance : Quiver Vertex where
  Hom a b := {e : Edge // edgeSource e = a ∧ edgeTarget e = b}

instance (a b : Vertex) : Fintype (a ⟶ b) := by
  change Fintype {e : Edge // edgeSource e = a ∧ edgeTarget e = b}
  infer_instance

def source : Fin 2 → Vertex
  | 0 => .sourceZero
  | 1 => .sourceOne

def sink : Fin 2 → Vertex
  | 0 => .sinkZero
  | 1 => .sinkOne

def rank : Vertex → ℕ
  | .sourceZero => 2
  | .sourceOne => 2
  | .middle => 1
  | .sinkZero => 0
  | .sinkOne => 0

def network : RankedQuiverNetwork ℤ Vertex (Fin 2) where
  source := source
  sink := sink
  rank := rank
  rank_decreases := by
    intro a b e
    rcases e with ⟨e, hsource, htarget⟩
    subst a
    subst b
    cases e <;> decide
  edgeWeight := fun _ => 1

theorem edge_weights_nonneg :
    ∀ {a b : Vertex} (e : a ⟶ b), 0 ≤ network.edgeWeight e := by
  intro a b e
  simp [network]

theorem middle_mem_sourceZero_sinkOne
    {p : network.toFinitePathNetwork.Path 0 1} :
    Vertex.middle ∈ p.vertices := by
  have hlength : p.length ≠ 0 := by
    intro hzero
    have h_eq := p.eq_of_length_zero hzero
    cases h_eq
  obtain ⟨c, e, q, hp, _⟩ := p.length_ne_zero_iff_eq_comp.mp hlength
  have hq : c ∈ q.vertices := q.start_mem_vertices
  rcases e with ⟨e, hsource, htarget⟩
  change edgeSource e = Vertex.sourceZero at hsource
  cases e <;> simp [edgeSource] at hsource
  change Vertex.middle = c at htarget
  subst c
  rw [hp, Quiver.Path.vertices_comp]
  simp [hq]

theorem middle_mem_sourceOne_sinkZero
    {p : network.toFinitePathNetwork.Path 1 0} :
    Vertex.middle ∈ p.vertices := by
  have hlength : p.length ≠ 0 := by
    intro hzero
    have h_eq := p.eq_of_length_zero hzero
    cases h_eq
  obtain ⟨c, e, q, hp, _⟩ := p.length_ne_zero_iff_eq_comp.mp hlength
  have hq : c ∈ q.vertices := q.start_mem_vertices
  rcases e with ⟨e, hsource, htarget⟩
  change edgeSource e = Vertex.sourceOne at hsource
  cases e <;> simp [edgeSource] at hsource
  change Vertex.middle = c at htarget
  subst c
  rw [hp, Quiver.Path.vertices_comp]
  simp [hq]

def indexRank : Fin 2 → ℕ := fun i => i.1

theorem indexRank_strictMono : StrictMono indexRank := by
  intro i j hij
  exact hij

theorem disjoint_order :
    ∀ {s₁ t₁ s₂ t₂ : Fin 2}
      (p : network.toFinitePathNetwork.Path s₁ t₁)
      (q : network.toFinitePathNetwork.Path s₂ t₂),
      RankedQuiverNetwork.VertexDisjoint p q →
        indexRank s₁ < indexRank s₂ →
        indexRank t₁ ≤ indexRank t₂ := by
  intro s₁ t₁ s₂ t₂ p q hdisj hsource
  have hs₁ : s₁ = 0 := by
    apply Fin.ext
    change s₁.val = 0
    have hs₁lt := s₁.isLt
    have hs₂lt := s₂.isLt
    change s₁.val < s₂.val at hsource
    lia
  subst s₁
  have hs₂ : s₂ = 1 := by
    apply Fin.ext
    change s₂.val = 1
    have hs₂lt := s₂.isLt
    change 0 < s₂.val at hsource
    lia
  subst s₂
  by_contra hnot
  have hreverse : t₂ < t₁ := lt_of_not_ge hnot
  have ht₁ : t₁ = 1 := by
    apply Fin.ext
    change t₁.val = 1
    have ht₁lt := t₁.isLt
    change t₂.val < t₁.val at hreverse
    lia
  subst t₁
  have ht₂ : t₂ = 0 := by
    apply Fin.ext
    change t₂.val = 0
    have ht₂lt := t₂.isLt
    change t₂.val < (1 : Fin 2).val at hreverse
    norm_num at hreverse
    lia
  subst t₂
  exact (RankedQuiverNetwork.not_vertexDisjoint_iff p q).mpr
    ⟨Vertex.middle, middle_mem_sourceZero_sinkOne,
      middle_mem_sourceOne_sinkZero⟩ hdisj

theorem two_path_obstruction :
    FinitePathNetwork.HasTwoPathObstruction
      network.toFinitePathNetwork
        (fun p q => RankedQuiverNetwork.VertexDisjoint p q) := by
  apply FinitePathNetwork.hasTwoPathObstruction_of_rankOrder
    network.toFinitePathNetwork
      (fun p q => RankedQuiverNetwork.VertexDisjoint p q)
    indexRank indexRank indexRank_strictMono indexRank_strictMono
  exact disjoint_order

theorem determinant_nonneg : 0 ≤ Matrix.det network.pathMatrix := by
  exact network.det_pathMatrix_nonneg two_path_obstruction edge_weights_nonneg

end RankedQuiverExample

end

end LGV
