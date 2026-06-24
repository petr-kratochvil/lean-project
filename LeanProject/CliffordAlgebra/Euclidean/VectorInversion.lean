import LeanProject.CliffordAlgebra.Euclidean.Conjugate
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
