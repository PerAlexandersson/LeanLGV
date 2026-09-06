/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma

/-!
# Finite paths in ranked quivers

This file supplies the finite-enumeration layer needed by a graph-level LGV
theorem. Mathlib already defines bounded quiver paths and their decidable
equality; here we enumerate exact-length and bounded paths, then use a strictly
decreasing vertex rank to enumerate all paths between two vertices.
-/

open Quiver

universe u v

namespace Quiver.Path

variable {V : Type u} [Quiver.{v} V]

/-- Paths of exactly `n` edges from `a` to `b`. -/
abbrev ExactLength (a b : V) (n : ℕ) :=
  {p : Path a b // p.length = n}

/-- A positive-length path is uniquely a shorter path followed by its last edge. -/
def exactLengthSuccEquiv (a b : V) (n : ℕ) :
    ExactLength a b (n + 1) ≃ Σ c : V, ExactLength a c n × (c ⟶ b) where
  toFun p := by
    rcases p with ⟨p, hp⟩
    cases p with
    | nil => simp at hp
    | @cons c _ p e =>
        exact ⟨c, ⟨⟨p, Nat.add_right_cancel hp⟩, e⟩⟩
  invFun q := ⟨q.2.1.1.cons q.2.2, by simp [q.2.1.2]⟩
  left_inv p := by
    rcases p with ⟨p, hp⟩
    cases p with
    | nil => simp at hp
    | cons p e => rfl
  right_inv q := by
    rcases q with ⟨c, ⟨⟨p, hp⟩, e⟩⟩
    rfl

/-- Exact-length paths are finite when vertices and edge types are finite. -/
theorem finite_exactLength [Finite V] [∀ a b : V, Finite (a ⟶ b)]
    (n : ℕ) (a b : V) : Finite (ExactLength a b n) := by
  induction n generalizing a b with
  | zero =>
      letI : Subsingleton (ExactLength a b 0) := ⟨by
        rintro ⟨p, hp⟩ ⟨q, hq⟩
        apply Subtype.ext
        cases p with
        | nil =>
            cases q with
            | nil => rfl
            | cons q e => simp at hq
        | cons p e => simp at hp⟩
      exact Finite.of_injective (fun _ => PUnit.unit) fun _ _ _ =>
        Subsingleton.elim _ _
  | succ n ih =>
      letI (c : V) : Finite (ExactLength a c n) := ih a c
      exact Finite.of_equiv (Σ c : V, ExactLength a c n × (c ⟶ b))
        (exactLengthSuccEquiv a b n).symm

/-- A canonical noncomputable enumeration of exact-length paths. -/
noncomputable instance instFintypeExactLength [Fintype V]
    [∀ a b : V, Fintype (a ⟶ b)]
    (a b : V) (n : ℕ) : Fintype (ExactLength a b n) := by
  letI := finite_exactLength n a b
  exact Fintype.ofFinite _

/-- Uniformly bounded paths are indexed by their exact length. -/
def boundedPathsEquivSigma (a b : V) (n : ℕ) :
    BoundedPaths a b n ≃ Σ m : Fin (n + 1), ExactLength a b m where
  toFun p := ⟨⟨p.1.length, Nat.lt_succ_iff.mpr p.2⟩, ⟨p.1, rfl⟩⟩
  invFun p := ⟨p.2.1, by
    rw [p.2.2]
    exact Nat.le_of_lt_succ p.1.2⟩
  left_inv _ := rfl
  right_inv p := by
    rcases p with ⟨⟨m, hm⟩, ⟨p, hp⟩⟩
    cases hp
    rfl

/-- Uniformly bounded paths form a finite type. -/
noncomputable instance instFintypeBoundedPaths [Fintype V]
    [∀ a b : V, Fintype (a ⟶ b)] (a b : V) (n : ℕ) :
    Fintype (BoundedPaths a b n) := by
  exact Fintype.ofEquiv (Σ m : Fin (n + 1), ExactLength a b m)
    (boundedPathsEquivSigma a b n).symm

/-- Along a path in a strictly rank-decreasing quiver, length plus final rank
is at most initial rank. -/
theorem length_add_rank_le (rank : V → ℕ)
    (hdecrease : ∀ {a b : V}, (a ⟶ b) → rank b < rank a)
    {a b : V} (p : Path a b) : p.length + rank b ≤ rank a := by
  induction p with
  | nil => simp
  | @cons b c p e ih =>
      rw [length_cons]
      have he := hdecrease e
      lia

/-- In a strictly rank-decreasing quiver, every path has the source-rank bound. -/
def equivBoundedPathsOfRank (rank : V → ℕ)
    (hdecrease : ∀ {a b : V}, (a ⟶ b) → rank b < rank a)
    (a b : V) : Path a b ≃ BoundedPaths a b (rank a) where
  toFun p := ⟨p, by
    have hp := length_add_rank_le rank hdecrease p
    lia⟩
  invFun p := p.1
  left_inv _ := rfl
  right_inv _ := rfl

/-- A canonical noncomputable enumeration of all paths in a strictly
rank-decreasing finite quiver. -/
@[implicit_reducible]
noncomputable def fintypeOfRank [Fintype V]
    [∀ a b : V, Fintype (a ⟶ b)]
    (rank : V → ℕ)
    (hdecrease : ∀ {a b : V}, (a ⟶ b) → rank b < rank a)
    (a b : V) : Fintype (Path a b) := by
  exact Fintype.ofEquiv (BoundedPaths a b (rank a))
    (equivBoundedPathsOfRank rank hdecrease a b).symm

end Quiver.Path
