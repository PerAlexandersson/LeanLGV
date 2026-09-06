/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Quiver.Network

/-!
# Splitting and swapping ranked quiver paths

Strict rank decrease prevents a directed path from visiting a vertex twice.
Consequently, a path which visits `x` has a unique decomposition into a prefix
ending at `x` and a suffix starting at `x`.  This file packages that split and
the elementary tail swap used by the LGV involution.
-/

namespace LGV

open Quiver

noncomputable section

universe u v w

namespace RankedQuiverNetwork

variable {R : Type u} {V : Type v} {ι : Type w}
variable [Quiver V]

/-- The vertices of a composite path are the union of the vertices of its two
parts. The joining vertex is present in the right-hand part. -/
theorem mem_vertices_comp_iff {a b c x : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    x ∈ (p.comp q).vertices ↔ x ∈ p.vertices ∨ x ∈ q.vertices := by
  constructor
  · rw [Quiver.Path.vertices_comp]
    intro hx
    rcases List.mem_append.mp hx with hx | hx
    · exact Or.inl (List.mem_of_mem_dropLast hx)
    · exact Or.inr hx
  · rintro (hx | hx)
    · by_cases hxb : x = b
      · subst x
        rw [Quiver.Path.vertices_comp]
        exact List.mem_append_right _ (Quiver.Path.start_mem_vertices q)
      · rw [Quiver.Path.vertices_comp]
        apply List.mem_append_left
        apply List.mem_dropLast_of_mem_of_ne_getLast hx
        simpa using hxb
    · rw [Quiver.Path.vertices_comp]
      exact List.mem_append_right _ hx

/-- A path in a strictly ranked quiver visits each vertex at most once. -/
theorem vertices_nodup (N : RankedQuiverNetwork R V ι)
    {a b : V} (p : Quiver.Path a b) : p.vertices.Nodup := by
  induction p with
  | nil => simp
  | @cons b c p e ih =>
      rw [Quiver.Path.vertices_cons, List.nodup_concat]
      refine ⟨?_, ih⟩
      intro hc
      obtain ⟨p₁, p₂, hp⟩ := p.exists_eq_comp_of_mem_vertices hc
      have hrank := Quiver.Path.length_add_rank_le N.rank N.rank_decreases p₂
      have hedge := N.rank_decreases e
      lia

/-- The rank of the endpoint of a path is at most the rank of every vertex
visited by that path. -/
theorem rank_end_le_of_mem_vertices (N : RankedQuiverNetwork R V ι)
    {a b x : V} (p : Quiver.Path a b) (hx : x ∈ p.vertices) :
    N.rank b ≤ N.rank x := by
  obtain ⟨p₁, p₂, _hp⟩ := p.exists_eq_comp_of_mem_vertices hx
  have hrank := Quiver.Path.length_add_rank_le N.rank N.rank_decreases p₂
  lia

/-- The rank of every vertex visited by a path is at most its initial rank. -/
theorem rank_mem_le_start (N : RankedQuiverNetwork R V ι)
    {a b x : V} (p : Quiver.Path a b) (hx : x ∈ p.vertices) :
    N.rank x ≤ N.rank a := by
  obtain ⟨p₁, p₂, _hp⟩ := p.exists_eq_comp_of_mem_vertices hx
  have hrank := Quiver.Path.length_add_rank_le N.rank N.rank_decreases p₁
  lia

/-- A vertex of the same rank as the start of a ranked path is that start. -/
theorem eq_start_of_mem_vertices_of_rank_eq
    (N : RankedQuiverNetwork R V ι)
    {a b x : V} (p : Quiver.Path a b) (hx : x ∈ p.vertices)
    (hrank : N.rank x = N.rank a) : x = a := by
  obtain ⟨p₁, p₂, _hp⟩ := p.exists_eq_comp_of_mem_vertices hx
  have hle := Quiver.Path.length_add_rank_le N.rank N.rank_decreases p₁
  have hlength : p₁.length = 0 := by lia
  exact (Quiver.Path.eq_of_length_zero p₁ hlength).symm

/-- A vertex of the same rank as the end of a ranked path is that end. -/
theorem eq_end_of_mem_vertices_of_rank_eq
    (N : RankedQuiverNetwork R V ι)
    {a b x : V} (p : Quiver.Path a b) (hx : x ∈ p.vertices)
    (hrank : N.rank x = N.rank b) : x = b := by
  obtain ⟨p₁, p₂, _hp⟩ := p.exists_eq_comp_of_mem_vertices hx
  have hle := Quiver.Path.length_add_rank_le N.rank N.rank_decreases p₂
  have hlength : p₂.length = 0 := by lia
  exact Quiver.Path.eq_of_length_zero p₂ hlength

/-- A ranked path contains at most one vertex of each rank. -/
theorem eq_of_mem_vertices_of_rank_eq
    (N : RankedQuiverNetwork R V ι)
    {a b x y : V} (p : Quiver.Path a b)
    (hx : x ∈ p.vertices) (hy : y ∈ p.vertices)
    (hrank : N.rank x = N.rank y) : x = y := by
  obtain ⟨p₁, p₂, hp⟩ := p.exists_eq_comp_of_mem_vertices hx
  have hy' : y ∈ (p₁.comp p₂).vertices := by
    exact congrArg Quiver.Path.vertices hp ▸ hy
  rcases (mem_vertices_comp_iff p₁ p₂).mp hy' with hyLeft | hyRight
  · exact (N.eq_end_of_mem_vertices_of_rank_eq p₁ hyLeft hrank.symm).symm
  · exact (N.eq_start_of_mem_vertices_of_rank_eq p₂ hyRight hrank.symm).symm

/-- Above the joining vertex, every vertex of a composite path belongs to its
left part. -/
theorem mem_left_of_mem_comp_of_rank_lt (N : RankedQuiverNetwork R V ι)
    {a b c y : V} (p : Quiver.Path a b) (q : Quiver.Path b c)
    (hy : y ∈ (p.comp q).vertices) (hby : N.rank b < N.rank y) :
    y ∈ p.vertices := by
  rcases (mem_vertices_comp_iff p q).mp hy with hy | hy
  · exact hy
  · have := N.rank_mem_le_start q hy
    lia

/-- A decomposition of `p` at a specified vertex `x`. -/
structure PathSplit {a b : V} (p : Quiver.Path a b) (x : V) where
  left : Quiver.Path a x
  right : Quiver.Path x b
  comp_eq : left.comp right = p

/-- A path split exists at every visited vertex. -/
def splitAtVertex (_N : RankedQuiverNetwork R V ι)
    {a b x : V} (p : Quiver.Path a b) (hx : x ∈ p.vertices) :
    PathSplit p x :=
  let hsplit := p.exists_eq_comp_of_mem_vertices hx
  let p₁ := hsplit.choose
  let p₂ := hsplit.choose_spec.choose
  ⟨p₁, p₂, hsplit.choose_spec.choose_spec.symm⟩

@[simp] theorem splitAtVertex_comp (N : RankedQuiverNetwork R V ι)
    {a b x : V} (p : Quiver.Path a b) (hx : x ∈ p.vertices) :
    (N.splitAtVertex p hx).left.comp (N.splitAtVertex p hx).right = p :=
  (N.splitAtVertex p hx).comp_eq

/-- In a strictly ranked quiver, a decomposition at a fixed vertex is unique. -/
private theorem get_split_vertex
    {a b x : V} {p : Quiver.Path a b}
    (p₁ : Quiver.Path a x) (p₂ : Quiver.Path x b)
    (hp : p₁.comp p₂ = p) :
    p.vertices.get ⟨p₁.length, by rw [← hp]; simp⟩ = x := by
  subst p
  exact Quiver.Path.vertices_comp_get_length_eq p₁ p₂

theorem pathSplit_unique (N : RankedQuiverNetwork R V ι)
    {a b x : V} {p : Quiver.Path a b}
    (p₁ q₁ : Quiver.Path a x) (p₂ q₂ : Quiver.Path x b)
    (hp : p₁.comp p₂ = p) (hq : q₁.comp q₂ = p) :
    p₁ = q₁ ∧ p₂ = q₂ := by
  have hi : p₁.length < p.vertices.length := by
    rw [← hp]
    simp
  have hj : q₁.length < p.vertices.length := by
    rw [← hq]
    simp
  let i : Fin p.vertices.length := ⟨p₁.length, hi⟩
  let j : Fin p.vertices.length := ⟨q₁.length, hj⟩
  have hgeti : p.vertices.get i = x := get_split_vertex p₁ p₂ hp
  have hgetj : p.vertices.get j = x := get_split_vertex q₁ q₂ hq
  have hij : i = j := (N.vertices_nodup p).injective_get
    (hgeti.trans hgetj.symm)
  have hlength : p₁.length = q₁.length := congrArg Fin.val hij
  exact (Quiver.Path.comp_inj' hlength).mp (hp.trans hq.symm)

/-- Any two bundled splits of a ranked path at the same vertex are equal. -/
@[ext] theorem PathSplit.ext (N : RankedQuiverNetwork R V ι)
    {a b x : V} {p : Quiver.Path a b} {s t : PathSplit p x}
    (hleft : s.left = t.left) : s = t := by
  have hright : s.right = t.right :=
    (N.pathSplit_unique s.left t.left s.right t.right
      s.comp_eq t.comp_eq).2
  cases s
  cases t
  simp_all

/-- The canonical split agrees with any displayed decomposition at `x`. -/
theorem splitAtVertex_eq (N : RankedQuiverNetwork R V ι)
    {a b x : V} {p : Quiver.Path a b} (hx : x ∈ p.vertices)
    (p₁ : Quiver.Path a x) (p₂ : Quiver.Path x b)
    (hp : p₁.comp p₂ = p) :
    N.splitAtVertex p hx = ⟨p₁, p₂, hp⟩ := by
  apply PathSplit.ext N
  exact (N.pathSplit_unique _ _ _ _
    (N.splitAtVertex p hx).comp_eq hp).1

theorem splitAtVertex_eq_of_comp (N : RankedQuiverNetwork R V ι)
    {a b x : V} (p₁ : Quiver.Path a x) (p₂ : Quiver.Path x b)
    (hx : x ∈ (p₁.comp p₂).vertices) :
    N.splitAtVertex (p₁.comp p₂) hx = ⟨p₁, p₂, rfl⟩ :=
  N.splitAtVertex_eq hx p₁ p₂ rfl

/-- The first path obtained by exchanging the tails of `p` and `q` at `x`. -/
def swapFirstAt (N : RankedQuiverNetwork R V ι)
    {a b c d x : V} (p : Quiver.Path a b) (q : Quiver.Path c d)
    (hp : x ∈ p.vertices) (hq : x ∈ q.vertices) : Quiver.Path a d :=
  (N.splitAtVertex p hp).left.comp (N.splitAtVertex q hq).right

/-- The second path obtained by exchanging the tails of `p` and `q` at `x`. -/
def swapSecondAt (N : RankedQuiverNetwork R V ι)
    {a b c d x : V} (p : Quiver.Path a b) (q : Quiver.Path c d)
    (hp : x ∈ p.vertices) (hq : x ∈ q.vertices) : Quiver.Path c b :=
  (N.splitAtVertex q hq).left.comp (N.splitAtVertex p hp).right

theorem mem_swapFirstAt_vertices (N : RankedQuiverNetwork R V ι)
    {a b c d x : V} (p : Quiver.Path a b) (q : Quiver.Path c d)
    (hp : x ∈ p.vertices) (hq : x ∈ q.vertices) :
    x ∈ (N.swapFirstAt p q hp hq).vertices := by
  change x ∈ ((N.splitAtVertex p hp).left.comp
    (N.splitAtVertex q hq).right).vertices
  rw [Quiver.Path.vertices_comp]
  exact List.mem_append_right _
    (Quiver.Path.start_mem_vertices (N.splitAtVertex q hq).right)

theorem mem_swapSecondAt_vertices (N : RankedQuiverNetwork R V ι)
    {a b c d x : V} (p : Quiver.Path a b) (q : Quiver.Path c d)
    (hp : x ∈ p.vertices) (hq : x ∈ q.vertices) :
    x ∈ (N.swapSecondAt p q hp hq).vertices := by
  change x ∈ ((N.splitAtVertex q hq).left.comp
    (N.splitAtVertex p hp).right).vertices
  rw [Quiver.Path.vertices_comp]
  exact List.mem_append_right _
    (Quiver.Path.start_mem_vertices (N.splitAtVertex p hp).right)

/-- Swapping the same two paths twice at the same vertex restores the first
path. -/
theorem swapFirstAt_twice (N : RankedQuiverNetwork R V ι)
    {a b c d x : V} (p : Quiver.Path a b) (q : Quiver.Path c d)
    (hp : x ∈ p.vertices) (hq : x ∈ q.vertices) :
    N.swapFirstAt (N.swapFirstAt p q hp hq)
        (N.swapSecondAt p q hp hq)
        (N.mem_swapFirstAt_vertices p q hp hq)
        (N.mem_swapSecondAt_vertices p q hp hq) = p := by
  unfold swapFirstAt swapSecondAt
  rw [N.splitAtVertex_eq_of_comp, N.splitAtVertex_eq_of_comp]
  exact (N.splitAtVertex p hp).comp_eq

/-- Swapping the same two paths twice at the same vertex restores the second
path. -/
theorem swapSecondAt_twice (N : RankedQuiverNetwork R V ι)
    {a b c d x : V} (p : Quiver.Path a b) (q : Quiver.Path c d)
    (hp : x ∈ p.vertices) (hq : x ∈ q.vertices) :
    N.swapSecondAt (N.swapFirstAt p q hp hq)
        (N.swapSecondAt p q hp hq)
        (N.mem_swapFirstAt_vertices p q hp hq)
        (N.mem_swapSecondAt_vertices p q hp hq) = q := by
  unfold swapFirstAt swapSecondAt
  rw [N.splitAtVertex_eq_of_comp, N.splitAtVertex_eq_of_comp]
  exact (N.splitAtVertex q hq).comp_eq

/-- The union of the two vertex sets is unchanged by a tail swap. -/
theorem vertexFinset_swap_union [DecidableEq V]
    (N : RankedQuiverNetwork R V ι)
    {a b c d x : V} (p : Quiver.Path a b) (q : Quiver.Path c d)
    (hp : x ∈ p.vertices) (hq : x ∈ q.vertices) :
    vertexFinset (N.swapFirstAt p q hp hq) ∪
        vertexFinset (N.swapSecondAt p q hp hq) =
      vertexFinset p ∪ vertexFinset q := by
  ext y
  simp only [Finset.mem_union, mem_vertexFinset]
  simp only [swapFirstAt, swapSecondAt, mem_vertices_comp_iff]
  have hpverts :
      ((N.splitAtVertex p hp).left.comp
        (N.splitAtVertex p hp).right).vertices = p.vertices :=
    congrArg Quiver.Path.vertices (N.splitAtVertex p hp).comp_eq
  have hpiff : y ∈ p.vertices ↔
      y ∈ (N.splitAtVertex p hp).left.vertices ∨
        y ∈ (N.splitAtVertex p hp).right.vertices := by
    rw [← hpverts]
    exact mem_vertices_comp_iff _ _
  have hqverts :
      ((N.splitAtVertex q hq).left.comp
        (N.splitAtVertex q hq).right).vertices = q.vertices :=
    congrArg Quiver.Path.vertices (N.splitAtVertex q hq).comp_eq
  have hqiff : y ∈ q.vertices ↔
      y ∈ (N.splitAtVertex q hq).left.vertices ∨
        y ∈ (N.splitAtVertex q hq).right.vertices := by
    rw [← hqverts]
    exact mem_vertices_comp_iff _ _
  tauto

/-- A vertex above the swap vertex in the first swapped path was already in
the first original path. -/
theorem mem_original_first_of_mem_swapFirstAt_of_rank_lt
    (N : RankedQuiverNetwork R V ι)
    {a b c d x y : V} (p : Quiver.Path a b) (q : Quiver.Path c d)
    (hp : x ∈ p.vertices) (hq : x ∈ q.vertices)
    (hy : y ∈ (N.swapFirstAt p q hp hq).vertices)
    (hxy : N.rank x < N.rank y) : y ∈ p.vertices := by
  have hleft : y ∈ (N.splitAtVertex p hp).left.vertices :=
    N.mem_left_of_mem_comp_of_rank_lt _ _ hy hxy
  have hcomp : y ∈ ((N.splitAtVertex p hp).left.comp
      (N.splitAtVertex p hp).right).vertices :=
    (mem_vertices_comp_iff _ _).mpr (Or.inl hleft)
  have hverts :
      ((N.splitAtVertex p hp).left.comp
        (N.splitAtVertex p hp).right).vertices = p.vertices :=
    congrArg Quiver.Path.vertices (N.splitAtVertex p hp).comp_eq
  exact hverts ▸ hcomp

/-- A vertex above the swap vertex in the second swapped path was already in
the second original path. -/
theorem mem_original_second_of_mem_swapSecondAt_of_rank_lt
    (N : RankedQuiverNetwork R V ι)
    {a b c d x y : V} (p : Quiver.Path a b) (q : Quiver.Path c d)
    (hp : x ∈ p.vertices) (hq : x ∈ q.vertices)
    (hy : y ∈ (N.swapSecondAt p q hp hq).vertices)
    (hxy : N.rank x < N.rank y) : y ∈ q.vertices := by
  have hleft : y ∈ (N.splitAtVertex q hq).left.vertices :=
    N.mem_left_of_mem_comp_of_rank_lt _ _ hy hxy
  have hcomp : y ∈ ((N.splitAtVertex q hq).left.comp
      (N.splitAtVertex q hq).right).vertices :=
    (mem_vertices_comp_iff _ _).mpr (Or.inl hleft)
  have hverts :
      ((N.splitAtVertex q hq).left.comp
        (N.splitAtVertex q hq).right).vertices = q.vertices :=
    congrArg Quiver.Path.vertices (N.splitAtVertex q hq).comp_eq
  exact hverts ▸ hcomp

/-- Tail swapping preserves the product of the two path weights. -/
theorem weight_swapFirstAt_mul_weight_swapSecondAt [CommMonoid R]
    (N : RankedQuiverNetwork R V ι)
    {a b c d x : V} (p : Quiver.Path a b) (q : Quiver.Path c d)
    (hp : x ∈ p.vertices) (hq : x ∈ q.vertices) :
    Quiver.Path.weight N.edgeWeight (N.swapFirstAt p q hp hq) *
        Quiver.Path.weight N.edgeWeight (N.swapSecondAt p q hp hq) =
      Quiver.Path.weight N.edgeWeight p * Quiver.Path.weight N.edgeWeight q := by
  calc
    _ = Quiver.Path.weight N.edgeWeight
          ((N.splitAtVertex p hp).left.comp (N.splitAtVertex p hp).right) *
        Quiver.Path.weight N.edgeWeight
          ((N.splitAtVertex q hq).left.comp (N.splitAtVertex q hq).right) :=
      N.weight_comp_mul_weight_comp_eq_swap _ _ _ _
    _ = _ := by rw [(N.splitAtVertex p hp).comp_eq,
      (N.splitAtVertex q hq).comp_eq]

end RankedQuiverNetwork

end

end LGV
