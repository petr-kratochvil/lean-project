import LeanProject.CliffordAlgebra.Euclidean.VectorInversion

namespace CliffordAlgebra.Euclidean

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Q" => Q_euclid_neg n
local notation "Cl" => CliffordAlgebra (Q_euclid_neg n)
local notation "ι" => CliffordAlgebra.ι (Q_euclid_neg n)

variable (v w : EuclideanSpace ℝ (Fin n)) (a b : CliffordAlgebra (Q_euclid_neg n))

lemma conjugate_inv (hv : v ≠ 0) : conjugate (vector_inv v hv) = (‖v‖ ^ 2)⁻¹ • ι v := by
  simp only [vector_inv, toUnit_vector]
  simp only [inv_neg, neg_smul, Units.inv_mk, map_neg, map_smul, conjugate_ι, smul_neg, neg_neg]

/-!
# Statement 3.3.3 - Spherical inversion
`conjugate ∘ vector_inv n v)` is the sperical inversion:
* It is a positive multiply of `ι(x)`
* The norms square to 1
-/
theorem t333_part1 (hv : v ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
    conjugate (vector_inv v hv) = r • ι v := by
  use (‖v‖ ^ 2)⁻¹
  constructor
  · positivity
  · exact conjugate_inv v hv

theorem t333_part2 (hv : v ≠ 0) :
    ∃ w : V, ι w = conjugate (vector_inv v hv) ∧ ‖w‖ * ‖v‖ = 1 := by
  use (‖v‖ ^ 2)⁻¹ • v
  constructor
  · rw [map_smul, ← conjugate_inv v hv]
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp

end CliffordAlgebra.Euclidean
