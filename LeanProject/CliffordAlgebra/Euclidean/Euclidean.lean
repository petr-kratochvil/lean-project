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

/-!
# Vector inversion
For a non-zero vector v: `(ι v)⁻¹ = - ι(v) / ‖v‖²`
* left inversion
* right inversion
* => `IsUnit (ι v)` (both inverses exist)

-/
theorem vector_inverse_right (hv : v ≠ 0) : (ι v) * ((-‖v‖ ^ 2)⁻¹ • ι v) = 1 := by
  rw [mul_smul_comm]
  rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
  rw [smul_smul]
  have hv₂ := Q_euclid_neg_ne_zero n v hv
  rw [Q_euclid_neg_identity] at hv₂ ⊢
  rw [inv_mul_cancel₀ hv₂, one_smul]

theorem vector_inverse_left (hv : v ≠ 0) : ((-‖v‖ ^ 2)⁻¹ • ι v) * (ι v) = 1 := by
  rw [smul_mul_assoc]
  rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
  rw [smul_smul]
  have hv₂ := Q_euclid_neg_ne_zero _ _ hv
  rw [Q_euclid_neg_identity] at hv₂ ⊢
  rw [inv_mul_cancel₀ hv₂, one_smul]

theorem isUnit_vector (hv : v ≠ 0) : IsUnit (ι v) := by
  have hv2 : - ‖v‖ ^ 2 ≠ 0 := by
    rw [← Q_euclid_neg_identity]
    exact Q_euclid_neg_ne_zero _ _ hv
  -- external refine: IsUnit (existential quantifier)
  -- internal refine: Units (val, inv, val_inv, inv_val)
  refine ⟨⟨ι v, (- ‖v‖ ^ 2)⁻¹ • ι v, ?_, ?_⟩, rfl⟩
  · rw [vector_inverse_right]
    exact hv
  · rw [vector_inverse_left]
    exact hv

end CliffordAlgebra.Euclidean
