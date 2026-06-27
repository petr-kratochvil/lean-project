import LeanProject.CliffordAlgebra.Conjugate

open CliffordAlgebra
namespace CliffordAlgebra

/-!
# Notation, variables

-/
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
  [Module R M] {Q : QuadraticForm R M}

local notation "Cl" => CliffordAlgebra Q
local notation "ι" => CliffordAlgebra.ι Q

/-
## Involute preserves units (maps units to units)
It is an algebra homomorphism `Cl →ₐ[R] Cl` which can be restricted to a
group homomorphism `Clˣ →* Clˣ` on the group of units

-/
def involute_unitHom : Clˣ →* Clˣ := Units.map involute.toMonoidHom

def involute_unit (u : Clˣ) : Clˣ := involute_unitHom u

lemma coe_involute_unitHom (u : Clˣ) : ↑(involute_unitHom u) = involute (u : Cl) := rfl

@[simp]
lemma coe_involute_unit (u : Clˣ) : ↑(involute_unit u) = involute (u : Cl) := rfl

theorem isUnit_involute {a : Cl} : IsUnit (involute a) ↔ IsUnit a := by
  constructor
  · intro hconj
    rw [← involute_involute a]
    obtain ⟨u, hu⟩ := hconj
    rw [← hu]
    exact ⟨involute_unitHom u, rfl⟩
  · intro ha
    obtain ⟨u, rfl⟩ := ha
    exact ⟨involute_unitHom u, rfl⟩

/-
## Reverse preserves units (maps units to units)

-/
def reverse_unitHomOp : Clˣ →* (Clˣ)ᵐᵒᵖ :=
  let unit_hom : Clˣ →* (Cl)ᵐᵒᵖˣ := Units.map reverse_homOp
  Units.opEquiv.toMonoidHom.comp unit_hom

def reverse_unit (u : Clˣ) : Clˣ := MulOpposite.unop (reverse_unitHomOp u)

lemma reverse_unit_def (u : Clˣ) : reverse_unit u =
    ⟨reverse ↑u, reverse ↑u⁻¹, (s324_ii u).1, (s324_ii u).2⟩ := by
  rfl

@[simp]
lemma coe_reverse_unit (u : Clˣ) : (↑(reverse_unit u) : Cl) = reverse (↑u : Cl) := by
  rfl

lemma coe_reverse_unit_inv (u : Clˣ) : (↑(reverse_unit u)⁻¹ : Cl) = reverse (↑(u⁻¹) : Cl) := by
  rfl

theorem isUnit_reverse {a : Cl} : IsUnit (reverse a) ↔ IsUnit a := by
  constructor
  · intro hconj
    rw [← reverse_reverse a]
    obtain ⟨u, hu⟩ := hconj
    rw [← hu]
    exact ⟨reverse_unit u, rfl⟩
  · intro ha
    obtain ⟨u, rfl⟩ := ha
    exact ⟨reverse_unit u, rfl⟩

/-
## Conjugate preserves units (maps units to units)
It is an algebra anti-homomorphism (changes the order of multiplication).

-/
def conjugate_unitHomOp : Clˣ →* (Clˣ)ᵐᵒᵖ := reverse_unitHomOp.comp involute_unitHom

def conjugate_unit (u : Clˣ) : Clˣ := MulOpposite.unop (conjugate_unitHomOp u)

lemma conjugate_unit_def (u : Clˣ) : conjugate_unit u =
    ⟨conjugate ↑u, conjugate ↑u⁻¹, (s324_iii u).1, (s324_iii u).2⟩ := by
  rfl

lemma coe_conjugate_unit (u : Clˣ) :
    (↑(conjugate_unit u) : Cl) = conjugate (↑u : Cl) := by
  rfl

lemma coe_conjugate_unit_inv (u : Clˣ) :
    (↑(conjugate_unit u)⁻¹ : Cl) = conjugate (↑(u⁻¹) : Cl) := by
  rfl

theorem isUnit_conjugate {a : Cl} : IsUnit (conjugate a) ↔ IsUnit a := by
  constructor
  · intro hconj
    rw [← conjugate_conjugate a]
    obtain ⟨u, hu⟩ := hconj
    rw [← hu]
    exact ⟨conjugate_unit u, rfl⟩
  · intro ha
    obtain ⟨u, rfl⟩ := ha
    exact ⟨conjugate_unit u, rfl⟩

/-
Composition lemma for `conjugate`
-/
lemma conjugate_unit_comp_def (u : Clˣ) : conjugate_unit u = reverse_unit (involute_unit u)
  := rfl

end CliffordAlgebra
