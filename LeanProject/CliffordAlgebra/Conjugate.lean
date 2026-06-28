import LeanProject.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

open CliffordAlgebra
namespace CliffordAlgebra

/-!
# Notation, variables

-/
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
  [Module R M] {Q : QuadraticForm R M}

variable (v w : M) (x a b : CliffordAlgebra Q) (unit : (CliffordAlgebra Q)ˣ)

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
* `conjugate_conjugate` :

-/
def conjugate : Cl →ₗ[R] Cl := reverse.comp involute.toLinearMap

theorem conjugate_apply : conjugate x = reverse (involute x) := by
  simp only [conjugate, LinearMap.comp_apply, AlgHom.coe_toLinearMap]

example : conjugate x = involute (reverse x) := by
  rw [conjugate_apply]
  exact reverse_involute x

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

@[simp]
theorem conjugate_conjugate : conjugate (conjugate x) = x := by
  simp only [conjugate_apply]
  rw [reverse_involute, reverse_reverse, involute_involute]

/-
`reverse` and `conjugate` are algebra anti-homomorphisms, which is defined as
an homomorphism to the opposite algebra

-/
def reverse_homOp : Cl →* Clᵐᵒᵖ where
  toFun x := MulOpposite.op (reverse x)
  map_one' := by simp only [reverse.map_one, MulOpposite.op_one]
  map_mul' x y := by simp only [reverse.map_mul, MulOpposite.op_mul]

def conjugate_homOp : Cl →* Clᵐᵒᵖ where
  toFun x := MulOpposite.op (conjugate x)
  map_one' := by simp only [conjugate.map_one, MulOpposite.op_one]
  map_mul' x y := by simp only [conjugate.map_mul, MulOpposite.op_mul]

/-!
# Note 3.2.2.

* For vectors, reverse does nothing and involute is the same as conjugate.
* The same is true for `[CommRing R]` members (we use `algebraMap` instead of `ι` here)

-/
example : reverse (ι v) = ι v := reverse_ι v

example : involute (ι v) = - ι v := involute_ι v

lemma n322_i : conjugate (ι v) = involute (ι v) :=
  (conjugate_ι v).trans (involute_ι v).symm

lemma n322_ii : conjugate (ι v) = - ι v := by
  rw [n322_i];
  exact involute_ι v

example (r : R) : involute (algebraMap R Cl r) = algebraMap R Cl r := by
  rw [involute.commutes]

example (r : R) : reverse (algebraMap R Cl r) = algebraMap R Cl r := by
  rw [reverse.commutes]

/-!
# Statement 3.2.3

-/
theorem s323_i_a : involute (a + b) = involute a + involute b := involute.map_add a b
theorem s323_i_b : involute (a * b) = involute a * involute b := involute.map_mul a b
theorem s323_ii_a : reverse (a + b) = reverse a + reverse b := reverse.map_add a b
theorem s323_ii_b : reverse (a * b) = reverse b * reverse a := reverse.map_mul a b
theorem s323_iii_a : conjugate (a + b) = conjugate a + conjugate b := map_add conjugate a b
theorem s323_iii_b : conjugate (a * b) = conjugate b * conjugate a := conjugate.map_mul a b

/-!
# Statement 3.2.4
`involute`, `reverse`, `conjugate` all commutate with inversion on units

* involute preserves units (maps units to units)
* (i) `involute (unit⁻¹)` is the inverse of `involute unit`
* (ii) `reverse (unit⁻¹)` is the inverse of `reverse unit`
* (iii) `conjugate (unit⁻¹)` is the inverse of `conjugate unit`

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

/-!
# Statement 3.2.5
* (i) `v * conjugate v = -Q(v)` (which is ‖x‖² in Euclidean case)
* (ii) `v * conjugate w + w * conjugate v = - (Q(v+w) - Q(v) - Q(w))`

*Polarization identity:*
`Q.polarBilin v w = Q(v+w) - Q(v) - Q(w)`  (which is  2⟪v,w⟫ in Euclidean case)
-/
theorem s325_i :
    ι v * conjugate (ι v) = algebraMap R Cl (-Q v) := by
  rw [conjugate_ι, mul_neg, ι_sq_scalar, map_neg]

theorem s325_i' :
    conjugate (ι v) * (ι v) = algebraMap R Cl (-Q v) := by
  rw [conjugate_ι, neg_mul, ι_sq_scalar, map_neg]

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
