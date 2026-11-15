import HodgeLean.Foundations.Uniformization

/-! # Degree-one lattice summands (FROZEN)

The two summands in the real-linear dual of the tangent space of the S12 uniformization.
HC no distance; AV milestone no distance.
-/

noncomputable section

namespace HodgeLean.Adapters

/-- The real-linear complex-valued dual of the tangent space `ℂ^g` in S12.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1. -/
abbrev DegreeOneLatticeDual (g : ℕ) := (Fin g → ℂ) →ₗ[ℝ] ℂ

example (g : ℕ) : DegreeOneLatticeDual g = ((Fin g → ℂ) →ₗ[ℝ] ℂ) := rfl

/-- Complex-linear real functionals inside `Hom_ℝ(ℂ^g, ℂ)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1. -/
def degreeOneLatticeHolomorphic (g : ℕ) : Submodule ℂ (DegreeOneLatticeDual g) where
  carrier := {f | ∀ v, f (Complex.I • v) = Complex.I * f v}
  zero_mem' := by simp
  add_mem' := by
    intro f h hf hh v
    simp only [LinearMap.add_apply]
    rw [hf v, hh v, mul_add]
  smul_mem' := by
    intro c f hf v
    simp only [LinearMap.smul_apply]
    rw [hf v]
    ring

example (g : ℕ) (f : DegreeOneLatticeDual g) :
    f ∈ degreeOneLatticeHolomorphic g ↔
      ∀ v, f (Complex.I • v) = Complex.I * f v := Iff.rfl

/-- Conjugate-linear real functionals inside `Hom_ℝ(ℂ^g, ℂ)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1. -/
def degreeOneLatticeAntiholomorphic (g : ℕ) : Submodule ℂ (DegreeOneLatticeDual g) where
  carrier := {f | ∀ v, f (Complex.I • v) = -Complex.I * f v}
  zero_mem' := by simp
  add_mem' := by
    intro f h hf hh v
    simp only [LinearMap.add_apply]
    rw [hf v, hh v]
    ring
  smul_mem' := by
    intro c f hf v
    simp only [LinearMap.smul_apply]
    rw [hf v]
    ring

example (g : ℕ) (f : DegreeOneLatticeDual g) :
    f ∈ degreeOneLatticeAntiholomorphic g ↔
      ∀ v, f (Complex.I • v) = -Complex.I * f v := Iff.rfl

/-- Conjugation on the real-linear dual: conjugate the value.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1. -/
def degreeOneLatticeConjugate (g : ℕ) (f : DegreeOneLatticeDual g) : DegreeOneLatticeDual g where
  toFun v := star (f v)
  map_add' v w := by simp
  map_smul' r v := by simp [map_smul]

example (g : ℕ) : degreeOneLatticeConjugate g (0 : DegreeOneLatticeDual g) = 0 := by
  ext
  simp [degreeOneLatticeConjugate]

end HodgeLean.Adapters
