import LeanProject.CliffordAlgebra.Euclidean.Conjugate
import LeanProject.CliffordAlgebra.Euclidean.CliffordGroupNorm
import LeanProject.CliffordAlgebra.Euclidean.VectorInversion

namespace CliffordAlgebra.Euclidean

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Q" => Q_euclid_neg n
local notation "Cl" => CliffordAlgebra (Q_euclid_neg n)
local notation "ι" => CliffordAlgebra.ι (Q_euclid_neg n)
local notation "ClGroup" => @CliffordGroup ℝ _ V _ _ Q

/-!
# Definition: rotation

-/
noncomputable def rotation (a : ClGroup) (x : V) (hx : x ≠ 0) :=
  (↑a : Clˣ) * (toUnit_vector x hx) * involute_unit (↑a⁻¹ : Clˣ)

/-
# Statement 3.2.12
* rotation_preserves_vectors
* rotation_isometry

-/
lemma rotation_preserves_vectors (a : ClGroup) (x : V) (hx : x ≠ 0) :
    ∃ y : V, ι y = rotation a x hx := by
  simp only [rotation, toUnit_vector, inv_neg, neg_smul, InvMemClass.coe_inv, Units.val_mul,
    coe_involute_unit]
  
  sorry

lemma rotation_isometry (a : ClGroup) (x : V) (hx : x ≠ 0):
    ‖(rotation_preserves_vectors a x hx).choose‖ = ‖x‖ := by
  sorry


end CliffordAlgebra.Euclidean
