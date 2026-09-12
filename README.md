# LeanLGV

LeanLGV is a small Lean 4 interface for the algebraic and ordered-boundary parts
of the Lindström--Gessel--Viennot method.

The package deliberately separates two concerns:

- `LGV.Finite` expands the determinant of a finite path matrix and exposes an
  abstract sign-reversing-cancellation theorem. Its `FinitePathNetwork.reindex`
  constructor produces the source/sink restrictions used for matrix minors.
- `LGV.Ordered` turns an ordered two-path obstruction and a cancellation
  certificate into an unsigned sum over pairwise-disjoint path families, with a
  nonnegative-determinant corollary for nonnegative weights.
- `LGV.Quiver` supplies a concrete finite ranked-quiver backend: finite path
  enumeration, canonical first-intersection tail swapping, the resulting
  sign-reversing involution, and weighted ordered LGV.

The core does not prescribe a graph representation. A concrete development may
use graph paths and a first-intersection tail swap, lattice paths, or any other
finite path type. This keeps graph topology and application-specific encodings
out of the determinant API.

## Related formalization

Fabian Gloecke et al.'s public
[`algebraic-combinatorics`](https://github.com/faabian/algebraic-combinatorics)
repository contains a complete weighted LGV theorem for path-finite acyclic
digraphs, including a formal first-intersection tail-swap involution:
`LGV.lgv_weighted_digraph` in
[`LGV2.lean`](https://github.com/faabian/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Determinants/LGV2.lean).
That graph backend is substantially larger and currently bundled with lattice,
Dyck-path, and Catalan applications. LeanLGV's abstract core is complementary:
it is intended as a compact interface for consumers that already have a finite
path model or a cancellation certificate.

## Status

The reusable algebraic core was extracted from the private `NonNestingRooks`
development. The standalone ranked-quiver landmark is now complete: the main
endpoints are
`RankedQuiverNetwork.det_pathMatrix_eq_sum_signedVertexDisjoint`,
`RankedQuiverNetwork.det_pathMatrix_eq_sum_vertexDisjoint`, and
`RankedQuiverNetwork.det_pathMatrix_nonneg`. Local verification and API
stabilization are tracked in `HANDOFF.md`.
