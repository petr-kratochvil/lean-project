import LeanProject.CliffordAlgebra.CliffordGroupNormSq
import LeanProject.CliffordAlgebra.Euclidean.Conjugate

/- this for synthesizing instance `[Nontrivial (CliffordAlgebra Q)]` (necessary for `normSq`) -/
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

open CliffordAlgebra
namespace CliffordAlgebra.Euclidean

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Q" => Q_euclid_neg n
local notation "Cl" => CliffordAlgebra (Q_euclid_neg n)
local notation "ι" => CliffordAlgebra.ι (Q_euclid_neg n)
local notation "ClGroup" => @CliffordGroup ℝ _ V _ _ Q

/-!
# Norm squared - Specialization for Euclidean spaces

Here we have R = ℝ and
* the `normSq` is non-negative
* we can use `Real.sqrt` to define the `Norm` instance

Theorems:
* `CliffordGroup.conjugate_nonneg`: `u * conjugate u` is non-negative
* `CliffordGroup.normSq_nonneg` : The squared norm is non-negative

-/
theorem CliffordGroup.conjugate_nonneg (u : Clˣ) (hu : u ∈ CliffordGroup) :
    ∀ r : ℝ, (↑u : Cl) * conjugate (↑u : Cl) = r • 1 → 0 ≤ r := by
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hu
  · rintro x ⟨m, hm⟩ r hr
    rw [hm.left, s325_i, Algebra.algebraMap_eq_smul_one] at hr
    have hr2 : - Q m = r := (smul_left_inj (one_ne_zero)).mp hr
    rw [← hr2]
    have := Q_euclid_nonpos n m
    linarith [this]
  · intro r hr
    have : r = 1 := by
      simp only [Units.val_one, conjugate.map_one, mul_one] at hr
      nth_rw 1 [← one_smul ℝ 1] at hr
      rw [smul_left_inj (one_ne_zero)] at hr
      exact hr.symm
    rw [this]
    exact zero_le_one
  · rintro x y hx hy hx_nonneg hy_nonneg r hr
    obtain ⟨r_x, hr_x⟩ := CliffordGroup.normSq_exists ⟨x, hx⟩
    obtain ⟨r_y, hr_y⟩ := CliffordGroup.normSq_exists ⟨y, hy⟩
    simp only [Units.val_mul, conjugate.map_mul, mul_assoc] at hr
    rw [← mul_assoc (↑y : Cl) (conjugate ↑y : Cl) (conjugate ↑x : Cl)] at hr
    rw [hr_y, smul_one_mul, mul_smul_comm, hr_x] at hr
    rw [smul_smul, smul_left_inj (one_ne_zero)] at hr
    have rx_nonneg := hx_nonneg r_x hr_x
    have ry_nonneg := hy_nonneg r_y hr_y
    rw [← hr]
    positivity
  · rintro x hx hr_nonneg r hx_r
    obtain ⟨r_x, hr_x⟩ := CliffordGroup.normSq_exists ⟨x, hx⟩
    have hx_r_inv := CliffordAlgebra.helper_conj_inv_2 x r_x hr_x
    have hr_eq : r = r_x⁻¹ := CliffordGroup.normSq_unique ⟨x, hx⟩⁻¹ r r_x⁻¹ hx_r hx_r_inv
    rw [hr_eq];
    exact inv_nonneg.mpr (hr_nonneg r_x hr_x)

theorem CliffordGroup.normSq_nonneg (u : Clˣ) (hu : u ∈ CliffordGroup) :
    0 ≤ CliffordGroup.normSq ⟨u, hu⟩ := by
  suffices h : ∀ r : ℝ, (u * conjugate_unit u) = r • (1 : Cl) → 0 ≤ r by
    specialize h (CliffordGroup.normSq ⟨u, hu⟩)
    exact h (CliffordGroup.normSq_spec ⟨u, hu⟩)
  exact CliffordGroup.conjugate_nonneg u hu

noncomputable section norm

/-!
## Definition of the `Norm` instance

* instance of `Norm` on Clifford group: defined as `Real.sqrt (u * conjugate u)`
* example usage
* `CliffordGroup.norm_def`: a rfl lemma
* `CliffordGroup.norm_mul`: the norm is multiplicative

-/
instance : Norm ClGroup := ⟨fun x => Real.sqrt (CliffordGroup.normSq x)⟩

/- Example usage of the Norm instance -/
example (a : ClGroup) : Real := ‖a‖
example (a : Clˣ) (ha : a ∈ CliffordGroup) : Real := ‖(⟨a, ha⟩ : ClGroup)‖
example (a : Cl) (ha_unit : (IsUnit a)) (ha_group : ha_unit.unit ∈ CliffordGroup) : Real :=
  ‖(⟨ha_unit.unit, ha_group⟩ : ClGroup)‖

end norm

@[simp]
lemma CliffordGroup.norm_def (x : ClGroup) : ‖x‖ = Real.sqrt (CliffordGroup.normSq x) := rfl

/-
# Statement 3.2.11 (ii)

-/
theorem CliffordGroup.norm_mul (a b : ClGroup) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  simp only [norm_def]
  rw [CliffordGroup.normSq_mul]
  rw [Real.sqrt_mul (normSq_nonneg a.val a.property)]

end CliffordAlgebra.Euclidean
