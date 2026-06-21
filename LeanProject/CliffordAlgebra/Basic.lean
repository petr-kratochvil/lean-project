import Mathlib.LinearAlgebra.CliffordAlgebra.Basic

namespace CliffordAlgebra

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
  [Module R M] {Q : QuadraticForm R M}

local notation "Cl" => CliffordAlgebra Q
local notation "ι" => CliffordAlgebra.ι Q

theorem identity_example (v : M) : ι v * ι v = algebraMap R Cl (Q v) := by
  exact ι_sq_scalar Q v

theorem identity_example2 (v : M) : ι v * ι v = (Q v) • 1 := by
  rw [← Algebra.algebraMap_eq_smul_one]
  exact ι_sq_scalar Q v

end CliffordAlgebra
