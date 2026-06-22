import LeanProject.CliffordAlgebra.CliffordGroup
import LeanProject.CliffordAlgebra.Euclidean.Euclidean

open CliffordAlgebra.Euclidean

variable (n : ℕ) (v w : EuclideanSpace ℝ (Fin n)) (a b : CliffordAlgebra (Q_euclid_neg n))

/-!
Vectors are invertible, so they belong to the Clifford group

-/
lemma image_vector_mem_cliffordGroup (hv : v ≠ 0) :
    (isUnit_vector n v hv).unit ∈ CliffordGroup := by
  apply Subgroup.subset_closure
  simp only [Set.mem_setOf_eq, IsUnit.unit_spec]
  use v
