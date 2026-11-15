import Mathlib.Algebra.QuaternionBasis
import Mathlib.LinearAlgebra.Basis.Defs

noncomputable section
open scoped Quaternion
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- Multiplication coordinates for an embedded quadratic generator and a
complementary anticommuting generator. This construction retains both generators.
Source: Voight, Quaternion Algebras, §2.2 (standard quaternion basis). -/
def quaternionCoordinates {D : Type*} [Ring D] [Algebra ℚ D]
    (b : ℚ) (u v : D) (hu : u * u = (-3 : ℚ) • (1 : D))
    (hv : v * v = b • (1 : D)) (huv : v * u = -(u * v)) :
    QuaternionAlgebra.Basis D (-3 : ℚ) 0 b where
  i := u
  j := v
  k := u * v
  i_mul_i := by simpa only [zero_smul, add_zero] using hu
  j_mul_j := hv
  i_mul_j := rfl
  j_mul_i := by simpa only [zero_smul, zero_sub] using huv

/-- A quaternion basis that is a vector-space basis gives an algebra presentation,
with no change to the chosen quadratic embedding.
Source: Voight, Quaternion Algebras, §2.2; Mathlib QuaternionAlgebra.Basis.liftHom. -/
def quaternionPresentation {D : Type*} [Ring D] [Algebra ℚ D]
    {b : ℚ} (q : QuaternionAlgebra.Basis D (-3 : ℚ) 0 b)
    (e : Module.Basis (Fin 4) ℚ D)
    (he : ∀ x : ℍ[ℚ, -3, 0, b], q.liftHom x =
      e.equivFun.symm (QuaternionAlgebra.linearEquivTuple (-3 : ℚ) 0 b x)) :
    ℍ[ℚ, -3, 0, b] ≃ₐ[ℚ] D :=
  AlgEquiv.ofBijective q.liftHom (by
    have h : (q.liftHom : ℍ[ℚ, -3, 0, b] → D) =
        e.equivFun.symm ∘ QuaternionAlgebra.linearEquivTuple (-3 : ℚ) 0 b :=
      funext he
    rw [h]
    exact e.equivFun.symm.bijective.comp
      (QuaternionAlgebra.linearEquivTuple (-3 : ℚ) 0 b).bijective)

/-- The presentation sends the standard Eisenstein generator to the retained one. -/
theorem quaternionPresentation_i {D : Type*} [Ring D] [Algebra ℚ D]
    {b : ℚ} (q : QuaternionAlgebra.Basis D (-3 : ℚ) 0 b)
    (e : Module.Basis (Fin 4) ℚ D) (he) :
    quaternionPresentation q e he (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, b]) = q.i := by
  change q.liftHom _ = _
  simp [QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.Basis.lift]

#print axioms quaternionPresentation
#print axioms quaternionPresentation_i
end HodgeLean.Foundations.Program.GeneralTypeIII
