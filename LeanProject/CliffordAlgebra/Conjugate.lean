import LeanProject.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

open CliffordAlgebra
namespace CliffordAlgebra

/-!
# Notation, variables

-/
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
  [Module R M] {Q : QuadraticForm R M}

variable (v w : M) (a b : CliffordAlgebra Q) (unit : (CliffordAlgebra Q)ˣ)

local notation "Cl" => CliffordAlgebra Q
local notation "ι" => CliffordAlgebra.ι Q

/-!
# Definition 3.2.1: conjugate

The conjugation in a Clifford algebra, defined as the composition of `involute` and `reverse`.

Statements:
* `conjugate_apply`:
* `conjugate_ι`:
* `conjugate.map_one`:
* `conjugate.map_mul`:

-/
def conjugate : Cl →ₗ[R] Cl := reverse.comp involute.toLinearMap

theorem conjugate_apply (x : Cl) : conjugate x = reverse (involute x) := by
  simp only [conjugate, LinearMap.comp_apply, AlgHom.coe_toLinearMap]

@[simp]
theorem conjugate_ι :
    conjugate (ι v) = -(ι v) := by
  rw [conjugate_apply]
  rw [involute_ι, map_neg, reverse_ι]

@[simp]
protected theorem conjugate.map_one : conjugate (1 : Cl) = 1 := by
  rw [conjugate_apply]
  rw [map_one, reverse.map_one]

@[simp]
protected theorem conjugate.map_mul : conjugate (a * b) = conjugate b * conjugate a := by
  repeat rw [conjugate_apply]
  rw [map_mul, reverse.map_mul]

/-!
# Note 3.2.2.
For vectors, reverse does nothing and involute is the same as conjugate

-/
example : reverse (ι v) = ι v := reverse_ι v
example : involute (ι v) = - ι v := involute_ι v
lemma n322_i : conjugate (ι v) = involute (ι v) := (conjugate_ι v).trans (involute_ι v).symm
lemma n322_ii : conjugate (ι v) = - ι v := by rw [n322_i]; exact involute_ι v

/-!
# Statement 3.2.3

-/
theorem s323_i_a : involute (a + b) = involute a + involute b := map_add involute a b
theorem s323_i_b : involute (a * b) = involute a * involute b := map_mul involute a b
theorem s323_ii_a : reverse (a + b) = reverse a + reverse b := map_add reverse a b
theorem s323_ii_b : reverse (a * b) = reverse b * reverse a := reverse.map_mul a b
theorem s323_iii_a : conjugate (a + b) = conjugate a + conjugate b := map_add conjugate a b
theorem s323_iii_b : conjugate (a * b) = conjugate b * conjugate a := conjugate.map_mul a b

/-!
# Statement 3.2.4
`involute`, `reverse`, `conjugate` all commutate with units

* involute preserves units (maps units to units)
* (i) `involute (unit⁻¹)` is the inverse of `involute unit`
* (ii) `reverse (unit⁻¹)` is the inverse of `reverse unit`
* (ii) `reverse(unit⁻¹)` is the inverse of `reverse unit`

-/
theorem s324_i :
    involute (↑unit : Cl) * involute ↑unit⁻¹ = 1 ∧
    involute (↑unit⁻¹ : Cl) * involute ↑unit = 1 := by
  constructor
  · rw [← map_mul, Units.mul_inv, map_one]
  · rw [← map_mul, Units.inv_mul, map_one]

theorem s324_ii :
    reverse (↑unit : Cl) * reverse ↑unit⁻¹ = 1 ∧
    reverse (↑unit⁻¹ : Cl) * reverse ↑unit = 1 := by
  constructor
  · rw [← reverse.map_mul, Units.inv_mul, reverse.map_one]
  · rw [← reverse.map_mul, Units.mul_inv, reverse.map_one]

theorem s324_iii :
    conjugate (↑unit : Cl) * conjugate ↑unit⁻¹ = 1 ∧
    conjugate (↑unit⁻¹ : Cl) * conjugate ↑unit = 1 := by
  constructor
  · rw [← conjugate.map_mul, Units.inv_mul, conjugate.map_one]
  · rw [← conjugate.map_mul, Units.mul_inv, conjugate.map_one]

/- involute preserves units (maps units to units) -/
theorem isUnit_involute {a : Cl} : IsUnit (involute a) ↔ IsUnit a := by
  constructor
  · exact fun h_unit ↦ involute_involute a ▸ IsUnit.map involute.toMonoidHom h_unit
  · exact fun h_unit ↦ IsUnit.map involute.toMonoidHom h_unit

/-! # Statement 3.2.5
* (i) `v * conjugate v = -Q(v)` (which is ‖x‖² in Euclidean case)
* (ii) `v * conjugate w + w * conjugate v = - (Q(v+w) - Q(v) - Q(w))`

*Polarization identity:*
`Q.polarBilin v w = Q(v+w) - Q(v) - Q(w)`  (which is  2⟪v,w⟫ in Euclidean case)
-/
theorem s325_i :
    ι v * conjugate (ι v) = algebraMap R Cl (-Q v) := by
  rw [conjugate_ι, mul_neg, ι_sq_scalar, map_neg]

theorem s325_ii (w : M) : ι v * conjugate (ι w) + ι w * conjugate (ι v) =
    algebraMap R Cl (-Q.polarBilin v w) := by
  have helper1 := @s325_i R _ M _ _ Q (v + w)
  have helper2: ι (v + w) * conjugate (ι (v + w)) =
      ι (v + w) * (conjugate (ι v) + conjugate (ι w)) := by
    rw [map_add, s323_iii_a]
  have helper3: ι (v + w) * conjugate (ι (v + w)) =
      ι (v) * conjugate (ι v) + ι w * conjugate (ι w)
      + ι v * conjugate (ι w) + ι w * conjugate (ι v) := by
    rw [helper2, map_add]
    simp only [add_mul, mul_add]
    abel
  have helper4 : ι (v + w) * conjugate (ι (v + w)) =
      algebraMap R Cl (-Q v) + algebraMap R Cl (-Q w)
      + ι v * conjugate (ι w) + ι w * conjugate (ι v) := by
    rw [helper3, ← s325_i v, ← s325_i w]
  have helper5 : ι v * conjugate (ι w) + ι w * conjugate (ι v) =
      algebraMap R Cl (-Q (v + w)) - algebraMap R Cl (-Q v) - algebraMap R Cl (-Q w) := by
    rw [← helper1, helper4]
    abel
  rw [helper5]
  rw [← map_sub, ← map_sub]
  congr 1
  simp only [QuadraticMap.polarBilin, LinearMap.mk₂_apply, QuadraticMap.polar]
  ring

end CliffordAlgebra
