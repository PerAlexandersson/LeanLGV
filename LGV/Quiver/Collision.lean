/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Quiver.Family

/-!
# Canonical collisions in ranked quiver path families

For an intersecting family we select the largest collision rank, then the
least pair of path indices meeting at that rank. A ranked path has at most one
vertex of each rank, so the vertex witnessing the selected rank and pair is
unique. This avoids imposing an artificial order on the vertex type.
-/

namespace LGV

open Quiver

noncomputable section

universe u v

namespace RankedQuiverNetwork

variable {R : Type u} {V : Type v} {n : ℕ}
variable [Quiver V] [Fintype V] [DecidableEq V]
variable [∀ a b : V, Fintype (a ⟶ b)]

/-- A vertex used by two paths of a signed family. -/
def IsCollisionVertex [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily) (x : V) : Prop :=
  ∃ i j : Fin n, i < j ∧ x ∈ (family.2 i).vertices ∧
    x ∈ (family.2 j).vertices

instance instDecidableIsCollisionVertex [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily) :
    DecidablePred (N.IsCollisionVertex family) := by
  intro x
  unfold IsCollisionVertex
  infer_instance

/-- The finite set of vertices at which a path family intersects. -/
def collisionVertices [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily) : Finset V :=
  Finset.univ.filter (N.IsCollisionVertex family)

@[simp] theorem mem_collisionVertices [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily) (x : V) :
    x ∈ N.collisionVertices family ↔ N.IsCollisionVertex family x := by
  simp [collisionVertices]

/-- A family is non-disjoint exactly when it has a collision vertex. -/
theorem exists_collisionVertex_iff_not_signedVertexDisjoint [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily) :
    (∃ x : V, N.IsCollisionVertex family x) ↔
      ¬N.SignedVertexDisjoint family := by
  constructor
  · rintro ⟨x, i, j, hij, hxi, hxj⟩ hdisjoint
    have hpq : VertexDisjoint (family.2 i) (family.2 j) :=
      hdisjoint i j hij.ne
    exact (not_vertexDisjoint_iff _ _).mpr ⟨x, hxi, hxj⟩ hpq
  · intro hbad
    simp only [SignedVertexDisjoint,
      FinitePathNetwork.SignedPairwiseDisjoint,
      FinitePathNetwork.PairwiseDisjoint] at hbad
    push Not at hbad
    obtain ⟨i, j, hij, hpq⟩ := hbad
    obtain ⟨x, hxi, hxj⟩ := (not_vertexDisjoint_iff _ _).mp hpq
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact ⟨x, i, j, hij, hxi, hxj⟩
    · exact ⟨x, j, i, hji, hxj, hxi⟩

theorem collisionVertices_nonempty_of_not_signedVertexDisjoint [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    (N.collisionVertices family).Nonempty := by
  obtain ⟨x, hx⟩ :=
    (N.exists_collisionVertex_iff_not_signedVertexDisjoint family).mpr hbad
  exact ⟨x, (N.mem_collisionVertices family x).mpr hx⟩

/-- Ranks at which two paths in the family meet. -/
def collisionRanks [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily) : Finset ℕ :=
  (N.collisionVertices family).image N.rank

theorem collisionRanks_nonempty_of_not_signedVertexDisjoint [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    (N.collisionRanks family).Nonempty := by
  rw [collisionRanks, Finset.image_nonempty]
  exact N.collisionVertices_nonempty_of_not_signedVertexDisjoint family hbad

/-- The largest rank at which two paths meet. -/
def firstCollisionRank [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) : ℕ :=
  (N.collisionRanks family).max'
    (N.collisionRanks_nonempty_of_not_signedVertexDisjoint family hbad)

theorem firstCollisionRank_mem [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.firstCollisionRank family hbad ∈ N.collisionRanks family := by
  exact Finset.max'_mem _ _

/-- Every collision rank is at most the first collision rank. -/
theorem collisionRank_le_firstCollisionRank [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) {x : V}
    (hx : N.IsCollisionVertex family x) :
    N.rank x ≤ N.firstCollisionRank family hbad := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr
    ⟨x, (N.mem_collisionVertices family x).mpr hx, rfl⟩

/-- Paths `i < j` meet at a vertex of rank `r`. -/
def HasCollisionAtRank [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (r : ℕ) (i j : Fin n) : Prop :=
  i < j ∧ ∃ x : V, N.rank x = r ∧
    x ∈ (family.2 i).vertices ∧ x ∈ (family.2 j).vertices

instance instDecidableHasCollisionAtRank [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily) (r : ℕ) :
    Decidable (N.HasCollisionAtRank family r i j) := by
  unfold HasCollisionAtRank
  infer_instance

/-- Left indices participating in a collision at rank `r`. -/
def leftIndicesAtRank [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily) (r : ℕ) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ j, N.HasCollisionAtRank family r i j

/-- Right indices meeting `i` at rank `r`. -/
def rightIndicesAtRank [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily) (r : ℕ) (i : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun j => N.HasCollisionAtRank family r i j

theorem exists_collision_at_firstRank [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    ∃ i j, N.HasCollisionAtRank family
      (N.firstCollisionRank family hbad) i j := by
  obtain ⟨x, hx, hrank⟩ := Finset.mem_image.mp
    (N.firstCollisionRank_mem family hbad)
  obtain ⟨i, j, hij, hxi, hxj⟩ :=
    (N.mem_collisionVertices family x).mp hx
  exact ⟨i, j, hij, x, hrank, hxi, hxj⟩

theorem leftIndicesAtFirstRank_nonempty [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    (N.leftIndicesAtRank family
      (N.firstCollisionRank family hbad)).Nonempty := by
  obtain ⟨i, j, hij⟩ := N.exists_collision_at_firstRank family hbad
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩⟩
  exact ⟨j, hij⟩

/-- The least left index in a collision of maximum rank. -/
def firstCollisionLeft [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) : Fin n :=
  (N.leftIndicesAtRank family (N.firstCollisionRank family hbad)).min'
    (N.leftIndicesAtFirstRank_nonempty family hbad)

theorem firstCollisionLeft_mem [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.firstCollisionLeft family hbad ∈ N.leftIndicesAtRank family
      (N.firstCollisionRank family hbad) := by
  exact Finset.min'_mem _ _

theorem rightIndicesAtFirstRank_nonempty [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    (N.rightIndicesAtRank family (N.firstCollisionRank family hbad)
      (N.firstCollisionLeft family hbad)).Nonempty := by
  obtain ⟨_hi, j, hj⟩ := Finset.mem_filter.mp
    (N.firstCollisionLeft_mem family hbad)
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩

/-- The least right index meeting the selected left path at maximum rank. -/
def firstCollisionRight [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) : Fin n :=
  (N.rightIndicesAtRank family (N.firstCollisionRank family hbad)
    (N.firstCollisionLeft family hbad)).min'
      (N.rightIndicesAtFirstRank_nonempty family hbad)

theorem firstCollisionRight_mem [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.firstCollisionRight family hbad ∈
      N.rightIndicesAtRank family (N.firstCollisionRank family hbad)
        (N.firstCollisionLeft family hbad) := by
  exact Finset.min'_mem _ _

theorem firstCollision_hasCollisionAtRank [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.HasCollisionAtRank family (N.firstCollisionRank family hbad)
      (N.firstCollisionLeft family hbad)
      (N.firstCollisionRight family hbad) := by
  simpa [rightIndicesAtRank] using N.firstCollisionRight_mem family hbad

/-- The unique vertex at the selected rank on the selected two paths. -/
def firstCollisionVertex [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) : V :=
  (N.firstCollision_hasCollisionAtRank family hbad).2.choose

theorem firstCollisionLeft_lt_right [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.firstCollisionLeft family hbad < N.firstCollisionRight family hbad :=
  (N.firstCollision_hasCollisionAtRank family hbad).1

theorem firstCollisionVertex_spec [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.rank (N.firstCollisionVertex family hbad) =
        N.firstCollisionRank family hbad ∧
      N.firstCollisionVertex family hbad ∈
        (family.2 (N.firstCollisionLeft family hbad)).vertices ∧
      N.firstCollisionVertex family hbad ∈
        (family.2 (N.firstCollisionRight family hbad)).vertices :=
  (N.firstCollision_hasCollisionAtRank family hbad).2.choose_spec

omit [DecidableEq V] in
/-- Swapping at a collision of rank `r` preserves every collision predicate at
that same rank. -/
theorem hasCollisionAtRank_swapSignedFamilyAt_iff [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) (r : ℕ)
    (hxrank : N.rank x = r) (a b : Fin n) :
    N.HasCollisionAtRank
        (N.swapSignedFamilyAt family i j hij x hxi hxj) r a b ↔
      N.HasCollisionAtRank family r a b := by
  constructor
  · rintro ⟨hab, y, hyrank, hya, hyb⟩
    refine ⟨hab, y, hyrank, ?_, ?_⟩
    · exact (N.mem_swapSignedFamilyAt_iff_of_rank_eq
        family i j a hij x y hxi hxj (hyrank.trans hxrank.symm)).mp hya
    · exact (N.mem_swapSignedFamilyAt_iff_of_rank_eq
        family i j b hij x y hxi hxj (hyrank.trans hxrank.symm)).mp hyb
  · rintro ⟨hab, y, hyrank, hya, hyb⟩
    refine ⟨hab, y, hyrank, ?_, ?_⟩
    · exact (N.mem_swapSignedFamilyAt_iff_of_rank_eq
        family i j a hij x y hxi hxj (hyrank.trans hxrank.symm)).mpr hya
    · exact (N.mem_swapSignedFamilyAt_iff_of_rank_eq
        family i j b hij x y hxi hxj (hyrank.trans hxrank.symm)).mpr hyb

theorem leftIndicesAtRank_swapSignedFamilyAt [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) (r : ℕ)
    (hxrank : N.rank x = r) :
    N.leftIndicesAtRank
        (N.swapSignedFamilyAt family i j hij x hxi hxj) r =
      N.leftIndicesAtRank family r := by
  ext a
  simp only [leftIndicesAtRank, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨b, hab⟩
    exact ⟨b, (N.hasCollisionAtRank_swapSignedFamilyAt_iff
      family i j hij x hxi hxj r hxrank a b).mp hab⟩
  · rintro ⟨b, hab⟩
    exact ⟨b, (N.hasCollisionAtRank_swapSignedFamilyAt_iff
      family i j hij x hxi hxj r hxrank a b).mpr hab⟩

theorem rightIndicesAtRank_swapSignedFamilyAt [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices) (r : ℕ)
    (hxrank : N.rank x = r) (a : Fin n) :
    N.rightIndicesAtRank
        (N.swapSignedFamilyAt family i j hij x hxi hxj) r a =
      N.rightIndicesAtRank family r a := by
  ext b
  simp only [rightIndicesAtRank, Finset.mem_filter, Finset.mem_univ,
    true_and]
  exact N.hasCollisionAtRank_swapSignedFamilyAt_iff
    family i j hij x hxi hxj r hxrank a b

omit [DecidableEq V] in
/-- A swap at a collision of maximal rank creates no collision of larger
rank. -/
theorem collisionRank_le_of_swapSignedFamilyAt [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (i j : Fin n) (hij : i ≠ j) (x : V)
    (hxi : x ∈ (family.2 i).vertices)
    (hxj : x ∈ (family.2 j).vertices)
    (hmax : ∀ {y : V}, N.IsCollisionVertex family y →
      N.rank y ≤ N.rank x) {y : V}
    (hy : N.IsCollisionVertex
      (N.swapSignedFamilyAt family i j hij x hxi hxj) y) :
    N.rank y ≤ N.rank x := by
  by_contra hle
  have hxy : N.rank x < N.rank y := Nat.lt_of_not_ge hle
  obtain ⟨a, b, hab, hya, hyb⟩ := hy
  have hya' := N.mem_original_of_mem_swapSignedFamilyAt_of_rank_lt
    family i j a hij x y hxi hxj hya hxy
  have hyb' := N.mem_original_of_mem_swapSignedFamilyAt_of_rank_lt
    family i j b hij x y hxi hxj hyb hxy
  exact (not_lt_of_ge (hmax ⟨a, b, hab, hya', hyb'⟩)) hxy

@[simp] theorem firstCollisionVertex_rank [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.rank (N.firstCollisionVertex family hbad) =
      N.firstCollisionRank family hbad :=
  (N.firstCollisionVertex_spec family hbad).1

theorem firstCollisionVertex_mem_left [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.firstCollisionVertex family hbad ∈
      (family.2 (N.firstCollisionLeft family hbad)).vertices :=
  (N.firstCollisionVertex_spec family hbad).2.1

theorem firstCollisionVertex_mem_right [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.firstCollisionVertex family hbad ∈
      (family.2 (N.firstCollisionRight family hbad)).vertices :=
  (N.firstCollisionVertex_spec family hbad).2.2

/-- Swap the two tails at the canonical first collision. -/
def swapAtFirstCollision [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.toFinitePathNetwork.SignedPathFamily :=
  N.swapSignedFamilyAt family
    (N.firstCollisionLeft family hbad)
    (N.firstCollisionRight family hbad)
    (N.firstCollisionLeft_lt_right family hbad).ne
    (N.firstCollisionVertex family hbad)
    (N.firstCollisionVertex_mem_left family hbad)
    (N.firstCollisionVertex_mem_right family hbad)

theorem swapAtFirstCollision_not_signedVertexDisjoint [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    ¬N.SignedVertexDisjoint (N.swapAtFirstCollision family hbad) := by
  exact N.not_signedVertexDisjoint_swapSignedFamilyAt family
    (N.firstCollisionLeft family hbad)
    (N.firstCollisionRight family hbad)
    (N.firstCollisionLeft_lt_right family hbad).ne
    (N.firstCollisionVertex family hbad)
    (N.firstCollisionVertex_mem_left family hbad)
    (N.firstCollisionVertex_mem_right family hbad)

/-- The canonical tail swap preserves the maximum collision rank. -/
theorem firstCollisionRank_swapAtFirstCollision [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.firstCollisionRank (N.swapAtFirstCollision family hbad)
        (N.swapAtFirstCollision_not_signedVertexDisjoint family hbad) =
      N.firstCollisionRank family hbad := by
  let i := N.firstCollisionLeft family hbad
  let j := N.firstCollisionRight family hbad
  let x := N.firstCollisionVertex family hbad
  have hij : i ≠ j := (N.firstCollisionLeft_lt_right family hbad).ne
  have hxi : x ∈ (family.2 i).vertices :=
    N.firstCollisionVertex_mem_left family hbad
  have hxj : x ∈ (family.2 j).vertices :=
    N.firstCollisionVertex_mem_right family hbad
  have hxrank : N.rank x = N.firstCollisionRank family hbad :=
    N.firstCollisionVertex_rank family hbad
  let swapped := N.swapSignedFamilyAt family i j hij x hxi hxj
  have hbad' : ¬N.SignedVertexDisjoint swapped :=
    N.not_signedVertexDisjoint_swapSignedFamilyAt family i j hij x hxi hxj
  change N.firstCollisionRank swapped hbad' =
    N.firstCollisionRank family hbad
  apply le_antisymm
  · obtain ⟨a, b, hab, y, hyrank, hya, hyb⟩ :=
      N.exists_collision_at_firstRank swapped hbad'
    have hymax : N.rank y ≤ N.rank x :=
      N.collisionRank_le_of_swapSignedFamilyAt family i j hij x hxi hxj
        (fun {z} hz => by
          rw [hxrank]
          exact N.collisionRank_le_firstCollisionRank family hbad hz)
        ⟨a, b, hab, hya, hyb⟩
    rw [← hyrank, ← hxrank]
    exact hymax
  · have hxcollision : N.IsCollisionVertex swapped x :=
      ⟨i, j, N.firstCollisionLeft_lt_right family hbad,
        N.mem_swapSignedFamilyAt_left family i j hij x hxi hxj,
        N.mem_swapSignedFamilyAt_right family i j hij x hxi hxj⟩
    rw [← hxrank]
    exact N.collisionRank_le_firstCollisionRank swapped hbad' hxcollision

private theorem min'_eq_of_finset_eq {α : Type*} [LinearOrder α]
    {s t : Finset α} (hs : s.Nonempty) (ht : t.Nonempty) (hst : s = t) :
    s.min' hs = t.min' ht := by
  subst t
  rfl

/-- The canonical tail swap preserves the selected left path index. -/
theorem firstCollisionLeft_swapAtFirstCollision [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.firstCollisionLeft (N.swapAtFirstCollision family hbad)
        (N.swapAtFirstCollision_not_signedVertexDisjoint family hbad) =
      N.firstCollisionLeft family hbad := by
  let swapped := N.swapAtFirstCollision family hbad
  let hbad' := N.swapAtFirstCollision_not_signedVertexDisjoint family hbad
  have hrank : N.firstCollisionRank swapped hbad' =
      N.firstCollisionRank family hbad :=
    N.firstCollisionRank_swapAtFirstCollision family hbad
  have hsets : N.leftIndicesAtRank swapped
        (N.firstCollisionRank swapped hbad') =
      N.leftIndicesAtRank family (N.firstCollisionRank family hbad) := by
    calc
      _ = N.leftIndicesAtRank swapped
          (N.firstCollisionRank family hbad) :=
        congrArg (N.leftIndicesAtRank swapped) hrank
      _ = _ := by
        simpa [swapped, swapAtFirstCollision] using
          N.leftIndicesAtRank_swapSignedFamilyAt family
            (N.firstCollisionLeft family hbad)
            (N.firstCollisionRight family hbad)
            (N.firstCollisionLeft_lt_right family hbad).ne
            (N.firstCollisionVertex family hbad)
            (N.firstCollisionVertex_mem_left family hbad)
            (N.firstCollisionVertex_mem_right family hbad)
            (N.firstCollisionRank family hbad)
            (N.firstCollisionVertex_rank family hbad)
  exact min'_eq_of_finset_eq
    (N.leftIndicesAtFirstRank_nonempty swapped hbad')
    (N.leftIndicesAtFirstRank_nonempty family hbad) hsets

/-- The canonical tail swap preserves the selected right path index. -/
theorem firstCollisionRight_swapAtFirstCollision [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.firstCollisionRight (N.swapAtFirstCollision family hbad)
        (N.swapAtFirstCollision_not_signedVertexDisjoint family hbad) =
      N.firstCollisionRight family hbad := by
  let swapped := N.swapAtFirstCollision family hbad
  let hbad' := N.swapAtFirstCollision_not_signedVertexDisjoint family hbad
  have hrank : N.firstCollisionRank swapped hbad' =
      N.firstCollisionRank family hbad :=
    N.firstCollisionRank_swapAtFirstCollision family hbad
  have hleft : N.firstCollisionLeft swapped hbad' =
      N.firstCollisionLeft family hbad :=
    N.firstCollisionLeft_swapAtFirstCollision family hbad
  have hsets : N.rightIndicesAtRank swapped
        (N.firstCollisionRank swapped hbad')
        (N.firstCollisionLeft swapped hbad') =
      N.rightIndicesAtRank family (N.firstCollisionRank family hbad)
        (N.firstCollisionLeft family hbad) := by
    calc
      _ = N.rightIndicesAtRank swapped
          (N.firstCollisionRank family hbad)
          (N.firstCollisionLeft family hbad) :=
        congrArg₂ (N.rightIndicesAtRank swapped) hrank hleft
      _ = _ := by
        simpa [swapped, swapAtFirstCollision] using
          N.rightIndicesAtRank_swapSignedFamilyAt family
            (N.firstCollisionLeft family hbad)
            (N.firstCollisionRight family hbad)
            (N.firstCollisionLeft_lt_right family hbad).ne
            (N.firstCollisionVertex family hbad)
            (N.firstCollisionVertex_mem_left family hbad)
            (N.firstCollisionVertex_mem_right family hbad)
            (N.firstCollisionRank family hbad)
            (N.firstCollisionVertex_rank family hbad)
            (N.firstCollisionLeft family hbad)
  exact min'_eq_of_finset_eq
    (N.rightIndicesAtFirstRank_nonempty swapped hbad')
    (N.rightIndicesAtFirstRank_nonempty family hbad) hsets

/-- The canonical tail swap preserves the selected collision vertex. -/
theorem firstCollisionVertex_swapAtFirstCollision [Monoid R]
    (N : RankedQuiverNetwork R V (Fin n))
    (family : N.toFinitePathNetwork.SignedPathFamily)
    (hbad : ¬N.SignedVertexDisjoint family) :
    N.firstCollisionVertex (N.swapAtFirstCollision family hbad)
        (N.swapAtFirstCollision_not_signedVertexDisjoint family hbad) =
      N.firstCollisionVertex family hbad := by
  let swapped := N.swapAtFirstCollision family hbad
  let hbad' := N.swapAtFirstCollision_not_signedVertexDisjoint family hbad
  let i := N.firstCollisionLeft family hbad
  let j := N.firstCollisionRight family hbad
  let x := N.firstCollisionVertex family hbad
  let x' := N.firstCollisionVertex swapped hbad'
  have hij : i ≠ j := (N.firstCollisionLeft_lt_right family hbad).ne
  have hxi : x ∈ (family.2 i).vertices :=
    N.firstCollisionVertex_mem_left family hbad
  have hxj : x ∈ (family.2 j).vertices :=
    N.firstCollisionVertex_mem_right family hbad
  have hrank : N.firstCollisionRank swapped hbad' =
      N.firstCollisionRank family hbad :=
    N.firstCollisionRank_swapAtFirstCollision family hbad
  have hleft : N.firstCollisionLeft swapped hbad' = i :=
    N.firstCollisionLeft_swapAtFirstCollision family hbad
  have hxx' : N.rank x' = N.rank x := by
    calc
      N.rank x' = N.firstCollisionRank swapped hbad' :=
        N.firstCollisionVertex_rank swapped hbad'
      _ = N.firstCollisionRank family hbad := hrank
      _ = N.rank x := (N.firstCollisionVertex_rank family hbad).symm
  have hx'mem : x' ∈ (swapped.2 i).vertices := by
    have hx'mem' := N.firstCollisionVertex_mem_left swapped hbad'
    have hvertices := congrArg (fun k => (swapped.2 k).vertices) hleft
    exact hvertices ▸ hx'mem'
  have hx'original : x' ∈ (family.2 i).vertices := by
    have hiff := N.mem_swapSignedFamilyAt_iff_of_rank_eq family i j i
      hij x x' hxi hxj hxx'
    simpa [swapped, swapAtFirstCollision] using hiff.mp hx'mem
  exact (N.eq_of_mem_vertices_of_rank_eq
    (family.2 i) hxi hx'original hxx'.symm).symm

end RankedQuiverNetwork

end

end LGV
