/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Finite
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Ordered-boundary LGV consequences

This module adds the ordered-endpoint hypothesis that removes all nonidentity
permutations from the finite LGV expansion. It deliberately treats disjointness
and the sign-reversing swap abstractly: graph topology and first-intersection
constructions belong in backend modules.
-/

namespace LGV

open scoped BigOperators

noncomputable section

universe u w

namespace FinitePathNetwork

variable {R : Type u} {n : ℕ}

/-- Pairwise disjointness for a path family realizing a fixed permutation. -/
def PairwiseDisjoint (N : FinitePathNetwork R (Fin n))
    (Disjoint : ∀ {s₁ t₁ s₂ t₂ : Fin n},
      N.Path s₁ t₁ → N.Path s₂ t₂ → Prop)
    {σ : Equiv.Perm (Fin n)} (family : N.PathFamily σ) : Prop :=
  ∀ i j : Fin n, i ≠ j → Disjoint (family i) (family j)

/-- Pairwise disjointness for a signed path family. -/
def SignedPairwiseDisjoint (N : FinitePathNetwork R (Fin n))
    (Disjoint : ∀ {s₁ t₁ s₂ t₂ : Fin n},
      N.Path s₁ t₁ → N.Path s₂ t₂ → Prop)
    (family : N.SignedPathFamily) : Prop :=
  PairwiseDisjoint N Disjoint family.2

/--
An ordered two-path obstruction: paths whose source and sink orders are
opposite cannot be disjoint.
-/
def HasTwoPathObstruction (N : FinitePathNetwork R (Fin n))
    (Disjoint : ∀ {s₁ t₁ s₂ t₂ : Fin n},
      N.Path s₁ t₁ → N.Path s₂ t₂ → Prop) : Prop :=
  ∀ {s₁ t₁ s₂ t₂ : Fin n}
    (p : N.Path s₁ t₁) (q : N.Path s₂ t₂),
      s₁ < s₂ → t₂ < t₁ → ¬ Disjoint p q

/--
A rank-order criterion for the ordered two-path obstruction.

This is often easier to prove than the obstruction directly: disjoint paths
preserve weak sink-rank order, while both endpoint rank maps are strict.
-/
theorem hasTwoPathObstruction_of_rankOrder (N : FinitePathNetwork R (Fin n))
    (Disjoint : ∀ {s₁ t₁ s₂ t₂ : Fin n},
      N.Path s₁ t₁ → N.Path s₂ t₂ → Prop)
    (sourceRank sinkRank : Fin n → ℕ)
    (hsourceRank : StrictMono sourceRank)
    (hsinkRank : StrictMono sinkRank)
    (horder :
      ∀ {s₁ t₁ s₂ t₂ : Fin n}
        (p : N.Path s₁ t₁) (q : N.Path s₂ t₂),
          Disjoint p q → sourceRank s₁ < sourceRank s₂ →
            sinkRank t₁ ≤ sinkRank t₂) :
    HasTwoPathObstruction N Disjoint := by
  intro s₁ t₁ s₂ t₂ p q hsource hsink hdisj
  have hsource' : sourceRank s₁ < sourceRank s₂ := hsourceRank hsource
  have hsink_le : sinkRank t₁ ≤ sinkRank t₂ := horder p q hdisj hsource'
  have hsink_lt : sinkRank t₂ < sinkRank t₁ := hsinkRank hsink
  exact (not_lt_of_ge hsink_le) hsink_lt

/-- A nonidentity permutation of a finite line has an inversion. -/
theorem exists_inversion_of_ne_one (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) :
    ∃ i j : Fin n, i < j ∧ σ j < σ i := by
  classical
  by_contra hno
  have hmono : Monotone σ := by
    intro i j hij
    rcases lt_or_eq_of_le hij with hij_lt | rfl
    · exact le_of_not_gt fun hlt => hno ⟨i, j, hij_lt, hlt⟩
    · rfl
  exact hσ ((Equiv.Perm.monotone_iff σ).mp hmono)

/-- Pairwise-disjoint families in an ordered network realize the identity. -/
theorem signedPairwiseDisjoint_perm_eq_one
    (N : FinitePathNetwork R (Fin n))
    (Disjoint : ∀ {s₁ t₁ s₂ t₂ : Fin n},
      N.Path s₁ t₁ → N.Path s₂ t₂ → Prop)
    (hcross : HasTwoPathObstruction N Disjoint)
    {family : N.SignedPathFamily}
    (hfamily : SignedPairwiseDisjoint N Disjoint family) :
    family.1 = 1 := by
  by_contra hperm
  rcases exists_inversion_of_ne_one family.1 hperm with ⟨i, j, hij, hinv⟩
  exact hcross (family.2 i) (family.2 j) hij hinv
    (hfamily i j hij.ne)

/--
Ordered LGV after cancellation of intersecting families.

The concrete backend supplies a fixed-point-free, sign-reversing involution on
the non-disjoint signed families. The ordered obstruction makes every survivor
an identity family, so the determinant is an unsigned sum.
-/
theorem det_matrix_eq_sum_pairwiseDisjoint_of_bad_involution [CommRing R]
    (N : FinitePathNetwork R (Fin n))
    (Disjoint : ∀ {s₁ t₁ s₂ t₂ : Fin n},
      N.Path s₁ t₁ → N.Path s₂ t₂ → Prop)
    [DecidablePred (SignedPairwiseDisjoint N Disjoint)]
    (hcross : HasTwoPathObstruction N Disjoint)
    (swap : {family : N.SignedPathFamily //
        ¬ SignedPairwiseDisjoint N Disjoint family} →
      {family : N.SignedPathFamily //
        ¬ SignedPairwiseDisjoint N Disjoint family})
    (hswap : ∀ b, N.signedFamilyWeight (swap b).1 =
      -N.signedFamilyWeight b.1)
    (hfixed : ∀ b, N.signedFamilyWeight b.1 ≠ 0 → swap b ≠ b)
    (hinvol : ∀ b, swap (swap b) = b) :
    Matrix.det N.matrix =
      ∑ family : {family : N.SignedPathFamily //
          SignedPairwiseDisjoint N Disjoint family},
        N.familyWeight family.1.2 := by
  refine det_matrix_eq_sum_goodFamilies_of_bad_involution_of_identity
    N (SignedPairwiseDisjoint N Disjoint) swap ?_ hfixed hinvol ?_
  · intro b
    exact signedFamilyWeight_add_eq_zero_of_swap_eq_neg N (hswap b)
  · intro family hfamily
    exact signedPairwiseDisjoint_perm_eq_one N Disjoint hcross hfamily

/--
The data needed to use ordered LGV with an abstract finite path model.

`swap` is normally the first-intersection tail swap. Storing the natural
negative-weight equation keeps concrete backends independent of the additive
cancellation implementation in `LGV.Finite`.
-/
structure OrderedCancellationCertificate [CommRing R]
    (N : FinitePathNetwork R (Fin n)) where
  Disjoint : ∀ {s₁ t₁ s₂ t₂ : Fin n},
    N.Path s₁ t₁ → N.Path s₂ t₂ → Prop
  decidable : DecidablePred (SignedPairwiseDisjoint N Disjoint)
  hcross : HasTwoPathObstruction N Disjoint
  swap : {family : N.SignedPathFamily //
      ¬ SignedPairwiseDisjoint N Disjoint family} →
    {family : N.SignedPathFamily //
      ¬ SignedPairwiseDisjoint N Disjoint family}
  weight_swap : ∀ b, N.signedFamilyWeight (swap b).1 =
    -N.signedFamilyWeight b.1
  ne_fixed_of_weight_ne_zero :
    ∀ b, N.signedFamilyWeight b.1 ≠ 0 → swap b ≠ b
  involutive : ∀ b, swap (swap b) = b

namespace OrderedCancellationCertificate

instance instDecidablePredSignedPairwiseDisjoint [CommRing R]
    {N : FinitePathNetwork R (Fin n)}
    (C : OrderedCancellationCertificate N) :
    DecidablePred (SignedPairwiseDisjoint N C.Disjoint) :=
  C.decidable

/-- Build a certificate from a rank-order argument and a tail swap. -/
def ofRankOrder [CommRing R]
    {N : FinitePathNetwork R (Fin n)}
    (Disjoint : ∀ {s₁ t₁ s₂ t₂ : Fin n},
      N.Path s₁ t₁ → N.Path s₂ t₂ → Prop)
    (decidable : DecidablePred (SignedPairwiseDisjoint N Disjoint))
    (sourceRank sinkRank : Fin n → ℕ)
    (hsourceRank : StrictMono sourceRank)
    (hsinkRank : StrictMono sinkRank)
    (horder :
      ∀ {s₁ t₁ s₂ t₂ : Fin n}
        (p : N.Path s₁ t₁) (q : N.Path s₂ t₂),
          Disjoint p q → sourceRank s₁ < sourceRank s₂ →
            sinkRank t₁ ≤ sinkRank t₂)
    (swap : {family : N.SignedPathFamily //
        ¬ SignedPairwiseDisjoint N Disjoint family} →
      {family : N.SignedPathFamily //
        ¬ SignedPairwiseDisjoint N Disjoint family})
    (weight_swap : ∀ b, N.signedFamilyWeight (swap b).1 =
      -N.signedFamilyWeight b.1)
    (ne_fixed_of_weight_ne_zero :
      ∀ b, N.signedFamilyWeight b.1 ≠ 0 → swap b ≠ b)
    (involutive : ∀ b, swap (swap b) = b) :
    OrderedCancellationCertificate N where
  Disjoint := Disjoint
  decidable := decidable
  hcross := hasTwoPathObstruction_of_rankOrder
    N Disjoint sourceRank sinkRank hsourceRank hsinkRank horder
  swap := swap
  weight_swap := weight_swap
  ne_fixed_of_weight_ne_zero := ne_fixed_of_weight_ne_zero
  involutive := involutive

/-- A certificate gives the unsigned sum over disjoint path families. -/
theorem det_eq_sum_pairwiseDisjoint [CommRing R]
    {N : FinitePathNetwork R (Fin n)}
    (C : OrderedCancellationCertificate N) :
    Matrix.det N.matrix =
      ∑ family : {family : N.SignedPathFamily //
          SignedPairwiseDisjoint N C.Disjoint family},
        N.familyWeight family.1.2 := by
  exact det_matrix_eq_sum_pairwiseDisjoint_of_bad_involution
    N C.Disjoint C.hcross C.swap C.weight_swap
      C.ne_fixed_of_weight_ne_zero C.involutive

/-- Nonnegative path weights give a nonnegative path-matrix determinant. -/
theorem det_nonneg [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {N : FinitePathNetwork R (Fin n)}
    (C : OrderedCancellationCertificate N)
    (hweight : ∀ {s t : Fin n} (p : N.Path s t), 0 ≤ N.weight p) :
    0 ≤ Matrix.det N.matrix := by
  rw [C.det_eq_sum_pairwiseDisjoint]
  exact Finset.sum_nonneg fun family _hfamily =>
    Finset.prod_nonneg fun i _hi => hweight (family.1.2 i)

end OrderedCancellationCertificate

end FinitePathNetwork

end

end LGV
