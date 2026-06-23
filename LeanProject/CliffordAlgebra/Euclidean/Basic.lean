import LeanProject.CliffordAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped RealInnerProductSpace

namespace CliffordAlgebra.Euclidean

variable (n : ℕ)

local notation "V" => EuclideanSpace ℝ (Fin n)

/-!
# Definition: Euclidean negative quadratic form

-/
noncomputable def Q_euclid_neg : QuadraticForm ℝ V :=
  QuadraticMap.mk
    (fun x => - ‖x‖ ^ 2)
    (by
      intro a x
      simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, smul_eq_mul, mul_neg, neg_inj,
        mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        norm_eq_zero]
      left
      ring
    )
    (⟨LinearMap.mk₂ ℝ
        (fun x y => - ⟪x, y⟫ * 2)
        (by
          intro a x y
          simp only [neg_mul]
          rw [InnerProductSpace.add_left]
          ring)
        (by
          intro a x y
          simp only [neg_mul, smul_eq_mul, mul_neg, neg_inj]
          rw [real_inner_smul_left]
          ring)
        (by
          intro a x y
          simp only [neg_mul]
          rw [inner_add_right (𝕜 := ℝ)]
          ring)
        (by
          intro a x y
          simp only [neg_mul, smul_eq_mul, mul_neg, neg_inj]
          rw [real_inner_smul_right]
          ring),
      by
        intro x y
        simp only [LinearMap.mk₂_apply]
        rw [norm_add_sq_real]
        ring⟩)

local notation "Q" => Q_euclid_neg n
local notation "Cl" => CliffordAlgebra Q
local notation "ι" => CliffordAlgebra.ι Q

/-
Definitional identity for `Q_euclid_neg`
-/
theorem Q_euclid_neg_identity (v : V) : Q v = - ‖v‖ ^ 2 := rfl

/-
Nonzero-ness of `Q_euclid_neg`
-/
theorem Q_euclid_neg_ne_zero (v : V) (hv : v ≠ 0) : Q v ≠ 0 := by
  rw [Q_euclid_neg_identity]
  exact neg_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hv))

/-
Non-positivity of `Q_euclid_neg`
-/
theorem Q_euclid_nonpos (v : V) : Q v ≤ 0 := by
  rw [Q_euclid_neg_identity]
  have : 0 ≤ ‖v‖ ^ 2 := by positivity
  linarith

/-
Polarization identity for `Q_euclid_neg`
Similar to `‖v + w‖² - ‖v‖² - ‖w‖² = 2 * ⟪v, w⟫`, but with a minus sign
-/
theorem Q_euclid_neg_polarBilin : (Q).polarBilin v w = -2 * ⟪v, w⟫ := by
  simp only [QuadraticMap.polarBilin_apply_apply]
  unfold QuadraticMap.polar
  simp only [Q_euclid_neg, QuadraticMap.coe_mk]
  rw [norm_add_sq_real]
  ring

end CliffordAlgebra.Euclidean
