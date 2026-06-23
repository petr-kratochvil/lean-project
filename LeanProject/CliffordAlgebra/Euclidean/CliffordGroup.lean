import LeanProject.CliffordAlgebra.CliffordGroup
import LeanProject.CliffordAlgebra.Euclidean.Euclidean

open CliffordAlgebra
namespace CliffordAlgebra.Euclidean

variable {n : ℕ} (v w : EuclideanSpace ℝ (Fin n)) (a b : CliffordAlgebra (Q_euclid_neg n))

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "Q" => Q_euclid_neg n
local notation "Cl" => CliffordAlgebra (Q_euclid_neg n)
local notation "ι" => CliffordAlgebra.ι (Q_euclid_neg n)

/-!
# Helper lemmas

-/
lemma helper_conjugate_inv (x : Clˣ) (r : ℝ) (hr : (↑x : Cl) * conjugate (↑x : Cl) = r • 1) :
    (↑x : Cl) = r • conjugate (↑x⁻¹ : Cl) := by
  have h := congr_arg (· * conjugate (↑x⁻¹ : Cl)) hr
  simp only [mul_assoc, (s324_iii x).1, mul_one, smul_one_mul] at h;
  exact h

lemma helper_conjugate_inv_prod (x : Clˣ) (r : ℝ) (hr : (↑x : Cl) * conjugate (↑x : Cl) = r • 1) :
    r • ((↑x⁻¹ : Cl) * conjugate (↑x⁻¹ : Cl)) = 1 := by
  have h_conjugate_inv := helper_conjugate_inv x r hr
  rw [← mul_smul_comm, ← h_conjugate_inv, Units.inv_mul]

/-!
# Definition of the norm on CliffordGroup
We want to define the squared norm of `x` as `x * conjugate x`.

Preparation lemmas:
* `conjugate_mul_real`: `u * conjugate u` is a real number
* `CliffordGroup.normSq_exists`:
* `CliffordGroup.normSq_unique`:
* `CliffordGroup.conj_nonneg`: `u * conjugate u` is non-negative

-/
lemma conjugate_mul_real (u : Clˣ) (hu : u ∈ CliffordGroup) :
    (u : Cl) * (conjugate (u : Cl)) ∈ Submodule.span ℝ {1} := by
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hu
  · rintro u ⟨m, hm⟩
    rw [hm.left, s325_i, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ (-Q m) (Submodule.subset_span (Set.mem_singleton 1))
  · rw [Units.val_one, conjugate.map_one, mul_one]
    exact Submodule.subset_span (Set.mem_singleton 1)
  · rintro x y hx hy x_conj y_conj
    simp only [Units.val_mul, conjugate.map_mul, mul_assoc]
    rw [← mul_assoc (↑y : Cl) (conjugate ↑y : Cl) (conjugate ↑x : Cl)]
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp y_conj
    rw [← hs, smul_one_mul, Algebra.mul_smul_comm]
    exact Submodule.smul_mem _ s x_conj
  · rintro x hx x_conj
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp x_conj
    have h_r : IsUnit (r • (1 : Cl)) := by
      rw [hr];
      exact x.isUnit.mul (isUnit_conjugate.mpr x.isUnit)
    have hr_ne : r ≠ 0 := by
      intro hr0; rw [hr0, zero_smul] at h_r; exact not_isUnit_zero h_r
    have h_prod := helper_conjugate_inv_prod x r hr.symm
    have h_prod_2 := congr_arg (r⁻¹ • ·) h_prod
    rw [smul_smul, inv_mul_cancel₀ hr_ne, one_smul] at h_prod_2
    rw [h_prod_2]
    exact Submodule.smul_mem _ (r⁻¹) (Submodule.subset_span (Set.mem_singleton 1))

lemma CliffordGroup.normSq_exists (u : Clˣ) (hu : u ∈ CliffordGroup) :
    ∃ r : ℝ, (u : Cl) * conjugate (u : Cl) = r • 1 := by
  have in_span : (u : Cl) * (conjugate (u : Cl)) ∈ Submodule.span ℝ {1} := conjugate_mul_real u hu
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp in_span
  use r
  exact hr.symm

lemma CliffordGroup.normSq_unique (u : Clˣ) :
    ∀ r s : ℝ, (↑u : Cl) * conjugate (↑u : Cl) = r • 1
    → (↑u : Cl) * conjugate (↑u : Cl) = s • 1
    → r = s := CliffordAlgebra.CliffordGroup.normSq_unique u

lemma CliffordGroup.conj_nonneg (u : Clˣ) (hu : u ∈ CliffordGroup) :
    ∀ r : ℝ, (↑u : Cl) * conjugate (↑u : Cl) = r • 1 → 0 ≤ r := by
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hu
  · rintro x ⟨m, hm⟩ r hr
    rw [hm.left, s325_i, Algebra.algebraMap_eq_smul_one] at hr
    have hr2 : - Q m = r := (smul_left_inj (one_ne_zero)).mp hr
    rw [← hr2]
    have := Q_euclid_nonpos n m
    linarith [this]
  · intro r hr
    have heq : r = 1 := by
      simp only [Units.val_one, conjugate.map_one, mul_one] at hr
      nth_rw 1 [← one_smul ℝ 1] at hr
      rw [smul_left_inj (one_ne_zero)] at hr
      exact hr.symm
    rw [heq]
    exact zero_le_one
  · rintro x y hx hy hx_nonneg hy_nonneg r hr
    obtain ⟨r_x, hr_x⟩ := CliffordGroup.normSq_exists x hx
    obtain ⟨r_y, hr_y⟩ := CliffordGroup.normSq_exists y hy
    simp only [Units.val_mul, conjugate.map_mul, mul_assoc] at hr
    rw [← mul_assoc (↑y : Cl) (conjugate ↑y : Cl) (conjugate ↑x : Cl)] at hr
    rw [hr_y, smul_one_mul, Algebra.mul_smul_comm, hr_x] at hr
    rw [smul_smul, smul_left_inj (one_ne_zero)] at hr
    have rx_nonneg := hx_nonneg r_x hr_x
    have ry_nonneg := hy_nonneg r_y hr_y
    rw [← hr]
    positivity
  · rintro x hx hx_nonneg r hx_inv_nonneg
    obtain ⟨r_x, hr_x⟩ := CliffordGroup.normSq_exists x hx
    have h_prod := helper_conjugate_inv_prod x r_x hr_x
    have r_x_ne_zero : r_x ≠ 0 := by
      intro h
      have := x.isUnit.mul (isUnit_conjugate.mpr x.isUnit)
      rw [hr_x, h, zero_smul] at this;
      exact not_isUnit_zero this
    have hr_eq : r = r_x⁻¹ := CliffordGroup.normSq_unique x⁻¹ r r_x⁻¹ hx_inv_nonneg
      (by
        have := congr_arg (r_x⁻¹ • ·) h_prod
        rwa [smul_smul, inv_mul_cancel₀ r_x_ne_zero, one_smul] at this
      )
    rw [hr_eq];
    exact inv_nonneg.mpr (hx_nonneg r_x hr_x)

/- ## Definition: norm squared

Using `Classical.choose` and above preparation lemmas.

* `CliffordGroup.normSq`
* `CliffordGroup.normSq_spec`
* `CliffordGroup.normSq_mul`: The squared norm preserves multiplication
* `CliffordGroup.normSq_nonneg` : The squared norm is non-negative

 -/
noncomputable def CliffordGroup.normSq (u : Clˣ) (hu : u ∈ CliffordGroup) : ℝ :=
  Classical.choose (CliffordGroup.normSq_exists u hu)

theorem CliffordGroup.normSq_spec (u : Clˣ) (hu : u ∈ CliffordGroup) :
    (↑u : Cl) * conjugate (↑u : Cl) = CliffordGroup.normSq u hu • 1 :=
  Classical.choose_spec (CliffordGroup.normSq_exists u hu)

/-
The norm preserves multiplication

-/
theorem CliffordGroup.normSq_mul (x y : Clˣ) (hx : x ∈ CliffordGroup) (hy : y ∈ CliffordGroup) :
    CliffordGroup.normSq (x * y) (CliffordGroup.mul_mem hx hy) =
    CliffordGroup.normSq x hx * CliffordGroup.normSq y hy :=
  CliffordGroup.normSq_unique (x * y) _ _
    (CliffordGroup.normSq_spec (x * y) (CliffordGroup.mul_mem hx hy))
    (by
      simp only [Units.val_mul, conjugate.map_mul, mul_assoc]
      rw [← mul_assoc (↑y : Cl), CliffordGroup.normSq_spec y hy,
          smul_one_mul, Algebra.mul_smul_comm, CliffordGroup.normSq_spec x hx,
          smul_smul, mul_comm])

/-
The norm is non-negative

-/
lemma CliffordGroup.normSq_nonneg (u : Clˣ) (hu : u ∈ CliffordGroup) :
    0 ≤ CliffordGroup.normSq u hu := by
  suffices h : ∀ r : ℝ, (↑u : Cl) * conjugate (↑u : Cl) = r • 1 → 0 ≤ r by
    specialize h (CliffordGroup.normSq u hu)
    exact h (CliffordGroup.normSq_spec u hu)
  exact CliffordGroup.conj_nonneg u hu


noncomputable section norm

/-!
## Definition of the `Norm` instance

* instance of `Norm` on Clifford group
* example usage
* `norm_def`: a rfl lemma
* `CliffordGroup.norm_mul`: the norm is multiplicative

-/
instance : Norm { x : Clˣ // x ∈ CliffordGroup } :=
  ⟨fun x => Real.sqrt (CliffordGroup.normSq x.val x.property)⟩

/- Example usage of the Norm notation -/
example (cg : ↥(@CliffordGroup ℝ _ V _ _ Q)) : Real := ‖cg‖
example (cg : { x : Clˣ // x ∈ CliffordGroup }) : Real := ‖cg‖
example (cg : Clˣ) (hcg : cg ∈ CliffordGroup) : Real :=
  ‖(⟨cg, hcg⟩ : { x : Clˣ // x ∈ CliffordGroup })‖

end norm

@[simp]
lemma CliffordGroup.norm_def (x : { x : Clˣ // x ∈ CliffordGroup }) :
    ‖x‖ = Real.sqrt (CliffordGroup.normSq x.val x.property) := rfl

theorem CliffordGroup.norm_mul (a b : ↥(@CliffordGroup ℝ _ V _ _ Q)) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  simp only [CliffordGroup.norm_def, Subgroup.coe_mul]
  rw [CliffordGroup.normSq_mul (a : Clˣ) (b : Clˣ) a.property b.property]
  rw [Real.sqrt_mul (CliffordGroup.normSq_nonneg a.val a.property)]

/-!
# Invertibility of vectors
Non-zero vectors are invertible, so they belong to the Clifford group
(a special case, they are part of the Clifford group generator set)

-/
theorem image_vector_mem_cliffordGroup (hv : v ≠ 0) :
    (isUnit_vector n v hv).unit ∈ CliffordGroup := by
  apply Subgroup.subset_closure
  simp only [Set.mem_setOf_eq, IsUnit.unit_spec]
  use v
  constructor
  · trivial
  · rw [Q_euclid_neg_identity]
    simp only [isUnit_iff_ne_zero, ne_eq, neg_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, norm_eq_zero]
    exact hv

end CliffordAlgebra.Euclidean
