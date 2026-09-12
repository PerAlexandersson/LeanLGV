/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import LGV.Resource.Cancellation

/-!
# Ordered LGV from resource cancellation

This file combines generic resource cancellation data with the existing
ordered two-path obstruction. It is the determinant endpoint of the standalone
resource layer.
-/

namespace LGV

open scoped BigOperators

noncomputable section

universe u l

namespace ResourcePathNetwork

variable {R : Type u} {Resource : Type l} {n : ℕ}
variable [DecidableEq Resource]

namespace ResourceFamilyCancellationCertificate

variable {N : ResourcePathNetwork R (Fin n) Resource}

/-- Add an ordered two-path obstruction to resource cancellation data. -/
def toOrderedCancellationCertificate [CommRing R]
    (C : ResourceFamilyCancellationCertificate N)
    (hcross : FinitePathNetwork.HasTwoPathObstruction
      N.toFinitePathNetwork (fun p q => N.ResourceDisjoint p q)) :
    FinitePathNetwork.OrderedCancellationCertificate N.toFinitePathNetwork :=
  { Disjoint := fun p q => N.ResourceDisjoint p q
    decidable := N.instDecidablePredSignedPairwiseResourceDisjoint
    hcross := hcross
    swap := C.swap
    weight_swap := C.weight_swap
    ne_fixed_of_weight_ne_zero := C.ne_fixed_of_weight_ne_zero
    involutive := C.involutive }

/-- The ordered path-matrix determinant is the unsigned resource-disjoint sum. -/
theorem det_matrix_eq_sum_resourceDisjoint [CommRing R]
    (C : ResourceFamilyCancellationCertificate N)
    (hcross : FinitePathNetwork.HasTwoPathObstruction
      N.toFinitePathNetwork (fun p q => N.ResourceDisjoint p q)) :
    Matrix.det N.toFinitePathNetwork.matrix =
      ∑ family : {family : N.toFinitePathNetwork.SignedPathFamily //
          N.SignedPairwiseResourceDisjoint family},
        N.toFinitePathNetwork.familyWeight family.1.2 := by
  exact (C.toOrderedCancellationCertificate hcross).det_eq_sum_pairwiseDisjoint

/-- Nonnegative path weights give a nonnegative ordered path determinant. -/
theorem det_matrix_nonneg [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R]
    (C : ResourceFamilyCancellationCertificate N)
    (hcross : FinitePathNetwork.HasTwoPathObstruction
      N.toFinitePathNetwork (fun p q => N.ResourceDisjoint p q))
    (hweight : ∀ {s t : Fin n} (p : N.Path s t), 0 ≤ N.weight p) :
    0 ≤ Matrix.det N.toFinitePathNetwork.matrix :=
  (C.toOrderedCancellationCertificate hcross).det_nonneg hweight

end ResourceFamilyCancellationCertificate

namespace ResourceCollisionSelector

variable {N : ResourcePathNetwork R (Fin n) Resource}

/-- A coherent selector and ordered obstruction give ordered cancellation. -/
def toOrderedCancellationCertificate [CommRing R]
    {C : ResourceSwapCertificate N}
    (S : ResourceCollisionSelector N C)
    (hcross : FinitePathNetwork.HasTwoPathObstruction
      N.toFinitePathNetwork (fun p q => N.ResourceDisjoint p q)) :
    FinitePathNetwork.OrderedCancellationCertificate N.toFinitePathNetwork :=
  S.cancellationCertificate.toOrderedCancellationCertificate hcross

end ResourceCollisionSelector

end ResourcePathNetwork

end

end LGV
