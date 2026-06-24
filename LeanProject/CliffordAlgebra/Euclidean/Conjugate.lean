import LeanProject.CliffordAlgebra.Conjugate
import LeanProject.CliffordAlgebra.Euclidean.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped RealInnerProductSpace
namespace CliffordAlgebra.Euclidean

/-!
# Notation, variables

-/
variable (n : ℕ)

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Q" => Q_euclid_neg n
local notation "Cl" => CliffordAlgebra (Q_euclid_neg n)
local notation "ι" => CliffordAlgebra.ι (Q_euclid_neg n)

variable (v w : EuclideanSpace ℝ (Fin n)) (a b : CliffordAlgebra (Q_euclid_neg n))

/-!
# Examples

-/
example : ι v * ι v = algebraMap ℝ Cl (Q v) := ι_sq_scalar Q v
example : ι v * ι v = algebraMap ℝ Cl (Q v) := identity_example v
example : conjugate (ι v) = -(ι v) := conjugate_ι v
example : conjugate (1 : Cl) = 1 := conjugate.map_one
example : conjugate (a * b) = conjugate b * conjugate a := s323_iii_b a b
example : -(ι v) = ι (-v) := by simp only [map_neg]
example : Q v = - ‖v‖ ^ 2 := rfl

/-!
# Statement 3.2.5

-/
theorem s325_i_eu : ι v * conjugate (ι v) = algebraMap ℝ Cl (‖v‖ ^ 2) := by
  rw [s325_i]
  simp only [Q_euclid_neg, QuadraticMap.coe_mk, neg_neg]

theorem s325_ii_eu : ι v * conjugate (ι w) + ι w * conjugate (ι v) =
    algebraMap ℝ Cl (2 * ⟪v, w⟫) := by
  rw [s325_ii]
  congr 1
  rw [Q_euclid_neg_polarBilin]
  rw [neg_mul, neg_neg]

end CliffordAlgebra.Euclidean
