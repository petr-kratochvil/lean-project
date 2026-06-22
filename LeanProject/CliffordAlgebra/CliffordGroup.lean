import Mathlib
import LeanProject.CliffordAlgebra.Conjugate

open CliffordAlgebra

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
  [Module R M] {Q : QuadraticForm R M} (v : M)

local notation "Cl" => CliffordAlgebra Q
local notation "ι" => CliffordAlgebra.ι Q

/-
# Definition 3.2.10 CliffordGroup
Defined as the closure of invertible vectors
* In an Euclidean space, all non-zero vectors are invertible
* Generally,`Q v` being an invertible element of `[CommRing R]` is necessary
* If `R` is a field, the condition simplifies to `Q v ≠ 0`

-/
noncomputable def CliffordGroup : Subgroup Clˣ :=
  Subgroup.closure { u : Clˣ | ∃ m : M, (↑u : Cl) = ι m }
