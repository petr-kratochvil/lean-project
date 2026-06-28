import LeanProject.CliffordAlgebra.Euclidean.Basic

open CliffordAlgebra
open CliffordAlgebra.Euclidean

variable {n : ℕ}

local notation "V"  => EuclideanSpace ℝ (Fin n)
local notation "Q"  => Q_euclid_neg n
local notation "Cl" => CliffordAlgebra (Q_euclid_neg n)
local notation "ι"  => CliffordAlgebra.ι (Q_euclid_neg n)

noncomputable section examples

private def e (i : Fin n) : V := EuclideanSpace.single i 1
private def e₁ : EuclideanSpace ℝ (Fin 2) := e ⟨0, by omega⟩
private def e₂ : EuclideanSpace ℝ (Fin 2) := e ⟨1, by omega⟩

lemma Q_basis (i : Fin n) : Q (e i) = -1 := by
  rw [Q_euclid_neg_identity]
  simp only [e, PiLp.norm_single, norm_one, one_pow]

lemma ι_sq_basis (i : Fin n) : ι (e i) * ι (e i) = algebraMap ℝ Cl (-1) := by
  have h := ι_sq_scalar (Q_euclid_neg n) (e i)
  rwa [Q_basis i] at h

lemma algebraMap_Cl : algebraMap ℝ Cl (-1) = -(1 : Cl) := by
  rw [map_neg, map_one]

lemma ι_sq_basis_Cl (i : Fin n) : ι (e i) * ι (e i) = -(1 : Cl) := by
  rw [ι_sq_basis, algebraMap_Cl]

end examples
