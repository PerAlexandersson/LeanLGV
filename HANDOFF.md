# LeanLGV handoff

Last updated: 2026-09-12.

## Resource foundation

- Issue PerAlexandersson/RealRooted#618 adds `ResourcePathNetwork`, extending
  the existing finite weighted network with a finite resource support for each
  path. It also supplies the `Uses` membership predicate, finite-set and
  support-extensionality witnesses, and resource-preserving source/sink
  reindexing.
- The new API stores supports directly as `Finset`s. The frozen predecessor
  stored lists but used only membership; serial path order is therefore not
  imposed on the generic package.
- `/root` remains the sole integration and serialized Lake-build owner. The
  focused resource build passed with 1,390 jobs; umbrella and full builds pass
  with 1,411 jobs. Representative axiom audits contain only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Issue PerAlexandersson/RealRooted#619 adds the two-path disjointness layer.
  Its checked witnesses identify non-disjointness with a concrete shared
  resource, characterize disjointness by excluding shared resources, and prove
  symmetry. The focused build passes with 1,391 jobs; combined umbrella and
  full builds pass with 1,412 jobs. Representative axiom audits again contain
  only `propext`, `Classical.choice`, and `Quot.sound`.

## Landmark finalization audit

- The standalone package is the canonical home for the independent LGV
  landmark. The old `NonNestingRooks` checkout remains on ice and is not an
  integration target.
- The ranked-quiver backend is complete through the canonical first-collision
  involution, signed cancellation, ordered unsigned determinant identity, and
  nonnegative determinant theorem. The principal final witnesses are
  `RankedQuiverNetwork.firstCollisionSwap_involutive`,
  `RankedQuiverNetwork.det_pathMatrix_eq_sum_vertexDisjoint`, and
  `RankedQuiverNetwork.det_pathMatrix_nonneg`. The concrete landmark
  regression is `RankedQuiverExample.determinant_nonneg` in
  `LGV/Quiver/Examples.lean`.
- Fresh `lake-workspace build LGV` and full `lake-workspace build` checks
  passed on 2026-09-12 with 1,410 jobs.
  Direct axiom audits of the abstract determinant expansion, ordered
  cancellation certificate, quiver involution, signed and unsigned quiver
  identities, and nonnegativity theorem report exactly `propext`,
  `Classical.choice`, and `Quot.sound`. Static scans find no `sorry`, `admit`,
  source `axiom`, prohibited tactic, option override, or overlong source line.
- Local `main` is fast-forwarded through the completed quiver checkpoint,
  matrix reindexing theorem, and concrete five-vertex ranked-quiver example.
  The repository has no configured remote or upstream branch, and
  `PerAlexandersson/LeanLGV` does not currently exist on GitHub. Remote
  publication, remote synchronization, and CI therefore remain a separately
  authorized repository-administration task; do not invent or add a remote.
- Next independent increments are resource-disjointness foundations and then
  resource cancellation. The RealRooted Toeplitz/PF adapter belongs in a later,
  separately owned layer.

## Finite-network foundation checkpoint

- Issue PerAlexandersson/RealRooted#613 adds the checked matrix-level equality
  `FinitePathNetwork.reindex_matrix` between network reindexing and
  `Matrix.submatrix`, with the canonical source-row/sink-column orientation.
  The focused `LGV.Finite` build passed with 1,389 jobs, the `LGV` umbrella
  build passed with 1,407 jobs, and its axiom audit reports only `propext` and
  `Quot.sound`.
- Local branch `feat/finite-reindex-submatrix` is merged into local `main` at
  its verified checkpoint. No remote is configured, so it cannot be pushed
  until #612 is explicitly authorized.

## Concrete landmark regression

- Issue PerAlexandersson/RealRooted#614 adds a checked five-vertex ranked
  quiver with two sources, a forced common middle vertex, and two sinks.
  `RankedQuiverExample.two_path_obstruction` proves the ordered crossing
  obstruction, and `RankedQuiverExample.determinant_nonneg` invokes the full
  ranked-quiver LGV endpoint with unit nonnegative edge weights.
- The focused example build passed with 1,408 jobs, and umbrella/full builds
  passed with 1,410 jobs. Direct axiom audits of both path-intersection lemmas,
  the obstruction, and determinant nonnegativity report exactly `propext`,
  `Classical.choice`, and `Quot.sound`.

## Active graph backend

- `/root` owns the clean-room Mathlib-quiver backend requested on 2026-09-06:
  finite/path-finite ranked networks, vertex-disjoint path families, the
  canonical first-intersection tail swap, and the resulting weighted LGV and
  ordered nonnegativity theorems. The CC BY-NC implementation in
  `faabian/algebraic-combinatorics` is architecture-only background; no source
  or proof expression will be copied or translated into this Apache-2.0
  package.
- The two Codex read-only local-API and mathematical audits are complete.
  Direct Claude process `13215` owns a long read-only Lean/Mathlib architecture
  review. Aristotle receives only small isolated theorem
  obligations after the public graph API is fixed; all suggestions remain
  advisory and require a local warning-free rebuild.
- Claude process `13215` reached the session quota after roughly 50 minutes
  and returned no report; no files or proofs were imported from it. The local
  implementation and serialized Lake builds remain authoritative.
- The dependent family involution blocker is now closed in `LGV/Quiver/Family.lean`:
  sink-label casts, cast-compatible two-path swaps, exact path accessors, and
  `swapSignedFamilyAt_twice` all compile without warnings. `LGV/Quiver/LGV.lean`
  now begins the canonical bad-family cancellation package with
  `firstCollisionSwap`, signed-weight negation, and
  `swapAtFirstCollision_twice`; its focused build is warning-free.
- `LGV/Quiver/LGV.lean` now also provides the weighted determinant sum over
  vertex-disjoint signed families, an ordered-cancellation certificate, the
  unsigned ordered determinant identity, and determinant nonnegativity from
  nonnegative edge weights. Focused `LGV.Quiver.LGV` and umbrella `LGV` builds
  both pass warning-free.
- Branch `feat/quiver-lindstrom-gessel-viennot` owns new generic graph-backend
  modules and their umbrella import. `/root` acquired the sole serialized
  Lean/Lake batch-build slot at 16:10 UTC after confirming that only unrelated
  long-lived LSP workers were active. One delegated worker may use that slot
  for the initial isolated finite-path-enumeration scratch check; `/root` will
  not run Lean concurrently. That warning-free scratch check completed and
  released the slot: `/tmp/LeanLGVFinitePaths.lean` proves finite exact-length,
  bounded, and strictly ranked path enumeration. `/root` reacquired the free
  slot at 16:16 UTC to integrate and verify the reviewed candidate.
- Checkpoint `2485c2b` defines the finite ranked quiver network, path matrix,
  vertex-disjointness predicate, tail-swap weight identity, and nonnegative
  path weights. `LGV/Quiver/Split.lean` now proves no-repeat ranked paths,
  unique canonical splitting, the two-path tail-swap involution, product-weight
  and vertex-union preservation, and preservation of vertices above the swap
  rank. Its focused warning-free build passed (1401 jobs). The next increment
  is the bad-family collision selector and signed family involution.
- Checkpoint `472e402` lifts the two-path swap to signed families, proves
  unsigned family-weight preservation and signed-weight negation, and keeps
  the swapped family intersecting. The current warning-free selector increment
  chooses maximum collision rank, then least left/right indices, then the
  unique common vertex at that rank; all four coordinates are invariant under
  the canonical swap. The remaining backend obligation is exact equality after
  swapping the dependent signed family twice.
- Aristotle advisory project `603cd1b2-3b84-4479-a10c-e7c7b95ab4d1`, task
  `4987f6a2-b5eb-45f3-b514-58d370f3a4fd` (owner label
  `root-leanlgv-20260906`), was scoped only to the isolated two-path tail-swap
  weight identity. It failed remotely after about two minutes without a
  diagnostic; Aristotle had warned that its Lean 4.28 preference does not
  match this package's Lean 4.31.0-rc2 pin. No generated source was adopted.
- Aristotle retry project `e0b2e15e-0449-4799-bd0b-eebac2925765`, task
  `469fb1b7-4895-4ea3-91ed-66b005aec0b7`, was given only the exact dependent
  family double-swap equality from clean detached checkpoint `472e402`. It also
  failed without a diagnostic under the same version warning. No generated
  source was adopted.

## Active extraction

- This is a new standalone package for the reusable LGV kernel formerly embedded
  in `NonNestingRooks`. It must remain independent of `RealRooted`.
- The intended API is `LGV.Finite` plus a small `LGV.Ordered` module. Ferrers,
  corridor, Toeplitz, and real-rootedness code are out of scope.
- Online audit found a complete graph-level theorem at
  `faabian/algebraic-combinatorics`, declaration `LGV.lgv_weighted_digraph`.
  Its `LGV2.lean` is 7,298 lines, imports all of Mathlib, includes unrelated
  applications, and contains one later exercise `sorry`; do not copy it here.
- Serialized Lean/Lake slot was free when this extraction began. Record focused
  and package build results here before the first checkpoint commit.

## Build ownership

- `/root` acquired the sole serialized Lean/Lake batch-build slot at 13:48 UTC
  on 2026-09-03 after checking the A174266 handoff (released at 07:03 UTC) and
  confirming that no batch `lake-workspace`, `lake build`, `lake exe`, or
  command-line Lean process was running. Long-lived RealRooted LSP processes
  are unrelated. This package owns the slot until a release is recorded here.

## Verified checkpoint

- `lake-workspace build LGV.Finite` passed after changing the path matrix to the
  conventional source-row/sink-column orientation.
- `lake-workspace build LGV` passed with no warnings on Lean 4.31.0-rc2 and
  Mathlib revision `261b5e314a7e71cff47a151b610fa834b3e6a7ae`.
- Direct axiom audits of the determinant expansion, signed-family expansion,
  abstract cancellation theorem, ordered LGV theorem, and nonnegative
  determinant corollary report exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- No `sorry`, `admit`, or source `axiom` occurs in the package.
- The serialized Lean/Lake slot was released by `/root` at 13:53 UTC after
  these checks. No further batch command is authorized under this acquisition.
- `/root` reacquired the free slot at 13:54 UTC solely to verify removal of two
  local linter-suppression options; no batch process was running at acquisition.
- The warning-free umbrella rebuild passed, and `/root` released the serialized
  slot again at 13:55 UTC. No further batch command is authorized under this
  acquisition.

## Aristotle ledger

- Exact owner label: `agent-real-rooted-a15715-p-2d7995a4`.
- Project `57162fe9-9b15-4c9d-bbf4-57789a508996`, task
  `9b1af9d7-403f-4ff2-90f2-0e718e8d51d0`: focused direct rank-order-to-
  determinant-nonnegativity convenience theorem. Final status: `FAILED` after
  2m38s, with no diagnostic event and no source change in the downloaded
  archive. Aristotle warned that the project used Lean 4.31.0-rc2 rather than
  its preferred 4.28.0 and that the temporary upload intentionally omitted the
  `.lake` dependency cache. The downloaded archive SHA-256 is
  `17229b7911cb69aafe0858a1516ec300fda48f725047ee930c52a35f8d482c84`.
  The upload was a clean archive of checkpoint `26dd2e9` in `/tmp`; no
  repository dependency cache or credentials were uploaded.
- This task is advisory. Adopt any result only in a separately verified
  follow-up commit. Do not manage Aristotle tasks owned by another session.

## Pending local follow-up

- Added `FinitePathNetwork.reindex` and its matrix-entry simp theorem so a
  consumer can represent arbitrary source/sink restrictions and matrix minors
  without rebuilding path types by hand. The warning-free umbrella rebuild
  passed.
- `/root` acquired the free serialized slot at 13:57 UTC to verify this isolated
  reindexing addition; no batch process was running at acquisition.
- `/root` released the serialized slot at 13:58 UTC after the successful build.
  No further batch command is authorized under this acquisition.
