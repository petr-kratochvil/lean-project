import LeanProject.CliffordAlgebra.CliffordGroup

namespace CliffordAlgebra

section CommRing_R

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
  [Module R M] {Q : QuadraticForm R M}

local notation "Cl" => CliffordAlgebra Q
local notation "ι" => CliffordAlgebra.ι Q

/-!
Helper lemmas for the squared norm
-/

protected
lemma helper_conj_ne_zero [Nontrivial Cl] (x : Clˣ) (r : R)
    (hr : (↑x : Cl) * conjugate (↑x : Cl) = r • 1) : r ≠ 0 := by
  have h_unit : IsUnit (r • (1 : Cl)) := by
    rw [← hr];
    exact x.isUnit.mul (isUnit_conjugate.mpr x.isUnit)
  intro hr0
  rw [hr0, zero_smul] at h_unit
  exact not_isUnit_zero h_unit

protected
lemma helper_conj_inv (x : Clˣ) (r : R) (hr : (↑x : Cl) * conjugate (↑x : Cl) = r • 1) :
    (↑x : Cl) = r • conjugate (↑x⁻¹ : Cl) := by
  have h := congr_arg (· * (↑(conjugate_unit x)⁻¹ : Cl)) hr
  rw [coe_conjugate_unit_inv, smul_mul_assoc, one_mul] at h
  rw [← h, mul_assoc, (s324_iii x).1, mul_one]

end CommRing_R

/-!
# Squared norm for a nontrivial Clifford group over a field
Can be defined as `u * conjugate u`, if we have
* `[Field R]`
* `[Nontrivial Cl]`

Preparation theorems:
* `CliffordGroup.conjugate_mul_field`:
  `u * conjugate u` is a "member of the field"
    - more precisely, a member of `Submodule.span R {1}`
* `CliffordGroup.normSq_exists`: existence of the squered norm
* `CliffordGroup.normSq_unique`: uniqueness of the squared norm

Definition:
* `CliffordGroup.normSq`: Definition of the norm squared using `Classical.choose`

Theorems:
* `CliffordGroup.normSq_spec`: The norm squared has the definitional property
* `CliffordGroup.normSq_mul`: The squared norm preserves multiplication

-/
section Field_R

variable {R : Type*} [Field R] {M : Type*} [AddCommGroup M]
  [Module R M] {Q : QuadraticForm R M} [Nontrivial (CliffordAlgebra Q)]

local notation "Cl" => CliffordAlgebra Q
local notation "ClGroup" => @CliffordGroup R _ M _ _ Q

protected
lemma helper_conj_inv_2 (x : Clˣ) (r : R)
    (hr : (↑x : Cl) * conjugate (↑x : Cl) = r • 1) :
    (↑x⁻¹ : Cl) * conjugate (↑x⁻¹ : Cl) = r⁻¹ • (1 : Cl) := by
  have r_ne_zero : r ≠ 0 := CliffordAlgebra.helper_conj_ne_zero x r hr
  have : r • ((↑x⁻¹ : Cl) * conjugate (↑x⁻¹ : Cl)) = 1 := by
    rw [← mul_smul_comm, ← CliffordAlgebra.helper_conj_inv x r hr, Units.inv_mul]
  have := congr_arg (r⁻¹ • ·) this
  rw [smul_smul, inv_mul_cancel₀ r_ne_zero, one_smul] at this
  exact this

theorem CliffordGroup.conjugate_mul_field (u : ClGroup) :
    (u.val : Cl) * (conjugate (u.val : Cl)) ∈ Submodule.span R {1} := by
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ u.property
  · rintro u ⟨m, hm⟩
    rw [hm.left, s325_i, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ (-Q m) (Submodule.subset_span (Set.mem_singleton 1))
  · rw [Units.val_one, conjugate.map_one, mul_one]
    exact Submodule.subset_span (Set.mem_singleton 1)
  · rintro x y hx hy x_conj y_conj
    simp only [Units.val_mul, conjugate.map_mul, mul_assoc]
    rw [← mul_assoc (↑y : Cl) (conjugate ↑y : Cl) (conjugate ↑x : Cl)]
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp y_conj
    rw [← hs, smul_one_mul, mul_smul_comm]
    exact Submodule.smul_mem _ s x_conj
  · rintro x hx x_conj
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp x_conj
    rw [CliffordAlgebra.helper_conj_inv_2 x r hr.symm]
    exact Submodule.smul_mem _ (r⁻¹) (Submodule.subset_span (Set.mem_singleton 1))

theorem CliffordGroup.normSq_exists (u : ClGroup) : ∃ r : R,
    (u.val : Cl) * conjugate (u.val : Cl) = r • (1 : Cl) := by
  have in_span := conjugate_mul_field u
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp in_span
  exact ⟨r, hr.symm⟩

theorem CliffordGroup.normSq_unique (u : ClGroup) :
    ∀ r s : R,
      (↑u.1 : Cl) * conjugate (↑u.1 : Cl) = r • 1
    → (↑u.1 : Cl) * conjugate (↑u.1 : Cl) = s • 1
    → r = s := by
  intros r s hr hs
  rw [hr] at hs
  rw [smul_left_inj (one_ne_zero)] at hs
  exact hs

noncomputable def CliffordGroup.normSq (u : ClGroup) : R :=
  Classical.choose (normSq_exists u)

theorem CliffordGroup.normSq_spec (u : ClGroup) :
    (↑u.1 : Cl) * conjugate (↑u.1 : Cl) = CliffordGroup.normSq u • 1 :=
  Classical.choose_spec (normSq_exists u)

theorem CliffordGroup.normSq_mul (u v : ClGroup) : normSq (u * v) = normSq u * normSq v := by
  have spec : ((u * v).val : Cl) * _ = _ := normSq_spec (u * v)
  refine normSq_unique (u * v) _ _ spec ?_
  simp only [Subgroup.coe_mul, Units.val_mul, conjugate.map_mul, mul_assoc]
  rw [← mul_assoc (v.val : Cl)]
  rw [normSq_spec v, smul_one_mul, mul_smul_comm]
  rw [normSq_spec u, smul_smul, mul_comm]

/-
# Statement 3.2.11 (i)
* Maybe (?) true for general `[CommRing R]`
* Proven here for `[Field R]` with the use of `normSq_exists`

-/
theorem CliffordGroup.s3211_i1 (a : ClGroup) : a * CliffordGroup.conjugateFun a =
    (CliffordGroup.involuteHom a) * (CliffordGroup.reverseFun a) := by
  apply Subtype.ext
  apply Units.ext
  simp only [conjugateFun, conjugate_unit, Subgroup.coe_mul, Units.val_mul, involuteHom,
    MonoidHom.coe_mk, OneHom.coe_mk, reverseFun, MulMemClass.mk_mul_mk, coe_involute_unit,
    coe_reverse_unit]
  obtain ⟨r, hr⟩ := CliffordGroup.normSq_exists a
  have := congr_arg involute hr
  simp only [map_mul, map_smul, map_one] at this
  rw [conjugate_apply, ← reverse_involute, involute_involute] at this
  rw [this]
  exact hr

end Field_R

end CliffordAlgebra
