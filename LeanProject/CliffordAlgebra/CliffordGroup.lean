import Mathlib
import LeanProject.CliffordAlgebra.Conjugate

namespace CliffordAlgebra

/-
# Definition 3.2.10 CliffordGroup
Defined as the closure of invertible vectors
* In an Euclidean space, all non-zero vectors are invertible
* Generally,`Q v` being an invertible element of `[CommRing R]` is necessary
* If `R` is a field, the condition simplifies to `Q v ≠ 0`

-/

section CommRing_R

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
  [Module R M] {Q : QuadraticForm R M} (v : M)

local notation "Cl" => CliffordAlgebra Q
local notation "ι" => CliffordAlgebra.ι Q

noncomputable def CliffordGroup : Subgroup Clˣ :=
  Subgroup.closure { u : Clˣ | ∃ m : M, (↑u : Cl) = ι m ∧ IsUnit (Q m)}

/-!
## Helper lemmas for the squared norm
-/

protected
lemma helper_conj_ne_zero [Nontrivial Cl] (x : Clˣ) (r : R)
    (hr : (↑x : Cl) * conjugate (↑x : Cl) = r • 1) : r ≠ 0 := by
  have h_unit : IsUnit (r • (1 : Cl)) := by
    rw [← hr];
    exact x.isUnit.mul (isUnit_conjugate.mpr x.isUnit)
  intro hr0
  rw [hr0, zero_smul] at h_unit
  exact not_isUnit_zero h_unit

protected
lemma helper_conj_inv (x : Clˣ) (r : R) (hr : (↑x : Cl) * conjugate (↑x : Cl) = r • 1) :
    (↑x : Cl) = r • conjugate (↑x⁻¹ : Cl) := by
  have h := congr_arg (· * (↑(conjugate_unit x)⁻¹ : Cl)) hr
  rw [conjugate_unit_inv_coe, smul_mul_assoc, one_mul] at h
  rw [← h, mul_assoc, (s324_iii x).1, mul_one]

end CommRing_R

/-!
## Squared norm for general Clifford group
**NOT FINISHED**

Can be defined, if we have
* `[Field R]`
* `[Nontrivial Cl]`

Specialization for Euclidean spaces can be found in
`LeanProject.CliffordAlgebra.Euclidean.CliffordGroup`

-/
section Field_R
variable {R : Type*} [Field R] {M : Type*} [AddCommGroup M]
  [Module R M] {Q : QuadraticForm R M}

local notation "Cl" => CliffordAlgebra Q

theorem CliffordGroup.normSq_unique [Nontrivial Cl]
   (u : Clˣ) :
 ∀ r s : R, (↑u : Cl) * conjugate (↑u : Cl) = r • 1
    → (↑u : Cl) * conjugate (↑u : Cl) = s • 1
    → r = s := by
  intros r s hr hs
  rw [hr] at hs
  rw [smul_left_inj (one_ne_zero)] at hs
  exact hs

/-!
## Squared norm for fields

When `R` is a field, `normSq_exists` can be proved:
* `helper_conj_inv_2`
* `CliffordGroup.normSq_exists`
-/

protected
lemma helper_conj_inv_2 [Nontrivial Cl] (x : Clˣ) (r : R)
    (hr : (↑x : Cl) * conjugate (↑x : Cl) = r • 1) :
    (↑x⁻¹ : Cl) * conjugate (↑x⁻¹ : Cl) = r⁻¹ • (1 : Cl) := by
  have r_ne_zero : r ≠ 0 := CliffordAlgebra.helper_conj_ne_zero x r hr
  have : r • ((↑x⁻¹ : Cl) * conjugate (↑x⁻¹ : Cl)) = 1 := by
    rw [← mul_smul_comm, ← CliffordAlgebra.helper_conj_inv x r hr, Units.inv_mul]
  have := congr_arg (r⁻¹ • ·) this
  rw [smul_smul, inv_mul_cancel₀ r_ne_zero, one_smul] at this
  exact this

theorem CliffordGroup.normSq_exists [Nontrivial Cl]
    (u : Clˣ) (hu : u ∈ CliffordGroup) :
    ∃ r : R, (↑u : Cl) * conjugate (↑u : Cl) = r • 1 :=
  sorry

end Field_R

end CliffordAlgebra
