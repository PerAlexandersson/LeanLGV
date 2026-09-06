# LeanLGV handoff

Last updated: 2026-09-06.

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
- Aristotle advisory project `603cd1b2-3b84-4479-a10c-e7c7b95ab4d1`, task
  `4987f6a2-b5eb-45f3-b514-58d370f3a4fd` (owner label
  `root-leanlgv-20260906`), was scoped only to the isolated two-path tail-swap
  weight identity. It failed remotely after about two minutes without a
  diagnostic; Aristotle had warned that its Lean 4.28 preference does not
  match this package's Lean 4.31.0-rc2 pin. No generated source was adopted.

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
