import LeanProject.CliffordAlgebra.ConjugateUnits

namespace CliffordAlgebra

/-
# Definition 3.2.10 CliffordGroup
Defined as the closure of invertible vectors
* In an Euclidean space, all non-zero vectors are invertible
* Generally,`Q v` being an invertible element of `[CommRing R]` is necessary
* If `R` is a field, the condition simplifies to `Q v ≠ 0`

The Clifford group is closed under `involute`, `reverse` and `conjugate`.

-/
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
  [Module R M] {Q : QuadraticForm R M} (v : M)

local notation "Cl" => CliffordAlgebra Q
local notation "ι" => CliffordAlgebra.ι Q

noncomputable def CliffordGroup : Subgroup Clˣ :=
  Subgroup.closure { u : Clˣ | ∃ m : M, (↑u : Cl) = ι m ∧ IsUnit (Q m)}

local notation "ClGroup" => @CliffordGroup R _ M _ _ Q

/-
Examples:
* Get `ClGroup` from `Clˣ`
* Get `Clˣ` from `ClGroup`
* Get `Cl` from `ClGroup`
* `ClGroup` written as a subtype
(Coercion works too)

-/
example (u : Clˣ) (hu : u ∈ ClGroup) : ClGroup := ⟨u, hu⟩

example (x : ClGroup) : Clˣ := x.1
example (x : ClGroup) : Clˣ := ↑x

example (x : ClGroup) : Cl := ↑(↑x : Clˣ)
example (x : ClGroup) : Cl := ↑x.1
example (x : ClGroup) : Cl := x.1.val

example : { x : Clˣ // x ∈ CliffordGroup } = ClGroup := rfl

/-
Clifford group is closed on involute
-/
theorem involute_mem_cliffordGroup {u : Clˣ} (hu : u ∈ ClGroup) :
    involute_unit u ∈ ClGroup := by
  rw [involute_unit]
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hu
  · rintro u ⟨m, hm1, hm2⟩
    apply Subgroup.subset_closure
    refine ⟨-m, ?_, ?_⟩
    · rw [map_neg, coe_involute_unitHom, hm1]
      exact involute_ι m
    · rwa [QuadraticMap.map_neg]
  · simp only [map_one, one_mem]
  · rintro x y hx hy x_mem y_mem
    simp only [map_mul]
    apply CliffordGroup.mul_mem x_mem y_mem
  · rintro x hx x_mem
    simp only [map_inv, inv_mem_iff]
    exact x_mem

def CliffordGroup.involuteHom : ClGroup →* ClGroup where
  toFun u := ⟨involute_unit u.1, involute_mem_cliffordGroup u.2⟩
  map_one' := by
    simp only [involute_unit, OneMemClass.coe_one, Subgroup.mk_eq_one, map_one]
  map_mul' u v := by
    simp only [involute_unit, Subgroup.coe_mul, map_mul, MulMemClass.mk_mul_mk]

/-
Clifford group is closed on reverse
-/
theorem reverse_mem_cliffordGroup {u : Clˣ} (hu : u ∈ ClGroup) :
    reverse_unit u ∈ ClGroup := by
  rw [reverse_unit]
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hu
  · rintro u ⟨m, hm1, hm2⟩
    apply Subgroup.subset_closure
    refine ⟨m, ?_, ?_⟩
    · simp [reverse_unitHomOp, reverse_homOp, hm1]
    · exact hm2
  · rw [MonoidHom.map_one, MulOpposite.unop_one]
    exact CliffordGroup.one_mem
  · rintro x y hx hy x_mem y_mem
    rw [MonoidHom.map_mul, MulOpposite.unop_mul]
    exact CliffordGroup.mul_mem y_mem x_mem
  · rintro x hx x_mem
    rw [MonoidHom.map_inv, MulOpposite.unop_inv]
    exact inv_mem x_mem

def CliffordGroup.reverseFun (u : ClGroup) : ClGroup :=
  ⟨reverse_unit u.1, reverse_mem_cliffordGroup u.2⟩

/-
Clifford group is closed on conjugate
-/
theorem conjugate_mem_cliffordGroup {u : Clˣ} (hu : u ∈ ClGroup) :
    conjugate_unit u ∈ ClGroup := by
  rw [conjugate_unit_comp_def]
  exact reverse_mem_cliffordGroup (involute_mem_cliffordGroup hu)

def CliffordGroup.conjugateFun (u : ClGroup) : ClGroup :=
  ⟨conjugate_unit u.1, conjugate_mem_cliffordGroup u.2⟩

end CliffordAlgebra
