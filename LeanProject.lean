import LeanProject.CliffordAlgebra

example (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
  (CliffordAlgebra.Euclidean.Q_euclid_neg n) v = - ‖v‖ ^ 2 := rfl
