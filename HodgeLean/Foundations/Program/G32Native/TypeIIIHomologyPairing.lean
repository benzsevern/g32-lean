import HodgeLean.Foundations.DualForm
import Mathlib.LinearAlgebra.BilinearForm.Properties

noncomputable section
open Module HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program.G32Native
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The rational pairing on homology associated to a polarization two-vector. -/
def typeIIIHomologyPairing (ω : ⋀[ℚ]^2 V) : LinearMap.BilinForm ℚ (Dual ℚ V) :=
  LinearMap.mk₂ ℚ (fun x y => y (contract ω x))
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)

/-- The homology pairing is alternating. -/
theorem typeIIIHomologyPairing_isAlt (ω : ⋀[ℚ]^2 V) :
    (typeIIIHomologyPairing ω).IsAlt := apply_contract_self ω

/-- Nondegenerate contraction gives a nondegenerate homology pairing. -/
theorem typeIIIHomologyPairing_nondegenerate [FiniteDimensional ℚ V]
    {ω : ⋀[ℚ]^2 V} (hω : IsNondegenerate ω) :
    (typeIIIHomologyPairing ω).Nondegenerate := by
  constructor
  · intro x hx
    apply hω.1
    have h := (Module.forall_dual_apply_eq_zero_iff ℚ (contract ω x)).1 hx
    simpa using h
  · intro y hy
    ext v
    obtain ⟨x, rfl⟩ := hω.2 v
    exact hy x

/-- Nondegeneracy is preserved by a rational change of coordinates. -/
theorem typeIII_bilin_pullback_nondegenerate {M : Type*} [AddCommGroup M] [Module ℚ M]
    (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate) (e : M ≃ₗ[ℚ] V) :
    (B.compl₁₂ e.toLinearMap e.toLinearMap).Nondegenerate := by
  constructor
  · intro x hx
    apply e.injective
    rw [map_zero]
    apply hB.1
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    exact hx z
  · intro x hx
    apply e.injective
    rw [map_zero]
    apply hB.2
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    exact hx z

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIHomologyPairing_isAlt
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIHomologyPairing_nondegenerate
#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_bilin_pullback_nondegenerate
