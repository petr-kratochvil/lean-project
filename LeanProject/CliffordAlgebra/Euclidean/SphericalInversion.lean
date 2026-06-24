import LeanProject.CliffordAlgebra.Euclidean.VectorInversion

namespace CliffordAlgebra.Euclidean

variable (n : ℕ)

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Q" => Q_euclid_neg n
local notation "Cl" => CliffordAlgebra (Q_euclid_neg n)
local notation "ι" => CliffordAlgebra.ι (Q_euclid_neg n)

variable (v w : EuclideanSpace ℝ (Fin n)) (a b : CliffordAlgebra (Q_euclid_neg n))

/-!
# Definition: cliffordInverse
Definition of vector inverse using formula from
`vector_inverse_left` and `vector_inverse_right`

-/
noncomputable def cliffordInverse : Cl := (-‖v‖ ^ 2)⁻¹ • ι v
example (hv : v ≠ 0) : cliffordInverse n v * (ι v) = 1 := vector_inverse_left n v hv
example (hv : v ≠ 0) : (ι v) * cliffordInverse n v = 1 := vector_inverse_right n v hv

theorem conjugate_inv (_ : v ≠ 0) :
    conjugate (cliffordInverse n v) = (‖v‖ ^ 2)⁻¹ • ι v := by
  simp only [cliffordInverse, conjugate_ι,
      inv_neg, neg_smul, map_neg, map_smul, smul_neg, neg_neg]

/-!
# Statement 3.3.3 - Spherical inversion
`conjugate (cliffordInverse n v)` is the sperical inversion:
* It is a positive multiply of `ι(x)`
* The norms square to 1
-/
theorem t333_part1 (hv : v ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
    conjugate (cliffordInverse n v) = r • ι v := by
  use (‖v‖ ^ 2)⁻¹
  constructor
  · positivity
  · exact conjugate_inv n v hv

theorem t333_part2 (hv : v ≠ 0) :
    ∃ w : V, ι w = conjugate (cliffordInverse n v) ∧ ‖w‖ * ‖v‖ = 1 := by
  use (‖v‖ ^ 2)⁻¹ • v
  constructor
  · rw [map_smul, ← conjugate_inv n v hv]
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp

end CliffordAlgebra.Euclidean
