import Mathlib
import LeanProject.CliffordAlgebra.Conjugate

namespace CliffordAlgebra

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
  Subgroup.closure { u : Clˣ | ∃ m : M, (↑u : Cl) = ι m ∧ IsUnit (Q m)}

/-!
## Squared norm for general Clifford group
**NOT FINISHED**

Can be defined, if we have
* `[IsCancelMulZero R]`
* `[Nontrivial Cl]`
* `[Module.IsTorsionFree R Cl]`

Specialization for Euclidean spaces can be found in
`LeanProject.CliffordAlgebra.Euclidean.CliffordGroup`

-/
lemma CliffordGroup.normSq_exists (u : Clˣ) (hu : u ∈ CliffordGroup) :
    ∃ r : R, (↑u : Cl) * conjugate (↑u : Cl) = r • 1 :=
  sorry

lemma CliffordGroup.normSq_unique [IsCancelMulZero R] [Nontrivial Cl] [Module.IsTorsionFree R Cl]
   (u : Clˣ) :
 ∀ r s : R, (↑u : Cl) * conjugate (↑u : Cl) = r • 1
    → (↑u : Cl) * conjugate (↑u : Cl) = s • 1
    → r = s := by
  intros r s hr hs
  rw [hr] at hs
  rw [smul_left_inj (one_ne_zero)] at hs
  exact hs

end CliffordAlgebra
