# LeanLGV agent guide

- Keep this package independent of `RealRooted` and application repositories.
- The public API is split into abstract finite-network algebra and ordered-endpoint
  consequences. Graph, lattice, Toeplitz, and total-positivity applications belong
  in separate modules and should not be imported by the core.
- Use `lake-workspace build <target>` from this directory. Never run `lake update`.
- Record build-slot ownership, verification, and blockers in `HANDOFF.md`.
- Do not add `sorry`, `admit`, source axioms, or broad `import Mathlib` imports.
