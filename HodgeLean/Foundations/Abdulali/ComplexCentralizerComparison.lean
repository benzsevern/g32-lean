import HodgeLean.Foundations.Abdulali.ComplexAction
import HodgeLean.Foundations.Abdulali.SkewCentralizerBaseChange

noncomputable section
open scoped TensorProduct Quaternion
namespace HodgeLean.Foundations.Abdulali
open HodgeLean.Foundations

/-- Commuting with the four rational quaternion basis operators is equivalent
to commuting with the entire complexified quaternion action.
Source: scalar extension of centralizer equations in Abdulali, Annals of
Mathematics 155 (2002), §3.2 and §4. -/
theorem quaternionComplexAction_centralizer {V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : ℚ) (ρ : ℍ[ℚ, -3, 0, b] →ₐ[ℚ] Module.End ℚ V)
    (X : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    (∀ i : Fin 4,
      X * (ρ (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b i)).baseChange ℂ =
        (ρ (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b i)).baseChange ℂ * X) ↔
    ∀ q, X * quaternionComplexAction b ρ q = quaternionComplexAction b ρ q * X := by
  let τ := quaternionComplexAction b ρ
  let F : ℍ[ℂ, -3, 0, (b : ℂ)] →ₗ[ℂ] Module.End ℂ (ℂ ⊗[ℚ] V) :=
    (LinearMap.mulRight ℂ X - LinearMap.mulLeft ℂ X).comp τ.toLinearMap
  constructor
  · intro h
    have hF : F = 0 := by
      apply (QuaternionAlgebra.basisOneIJK (-3 : ℂ) 0 (b : ℂ)).ext
      intro i
      change τ (QuaternionAlgebra.basisOneIJK (-3 : ℂ) 0 (b : ℂ) i) * X -
        X * τ (QuaternionAlgebra.basisOneIJK (-3 : ℂ) 0 (b : ℂ) i) = 0
      rw [← quaternionRationalInclusion_basis, quaternionComplexAction_rational]
      exact sub_eq_zero.mpr (h i).symm
    intro q
    have hq := LinearMap.congr_fun hF q
    exact (sub_eq_zero.mp hq).symm
  · intro h i
    simpa only [quaternionComplexAction_rational] using h
      (quaternionRationalInclusion b (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b i))

/-- The finite rational skew-centralizer has precisely the skew centralizer
of the complex quaternion action as its complexification.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.2 and §4;
the scalar extension is computed by finite kernels. -/
theorem quaternion_skew_centralizer_baseChange {V : Type*} [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (b : ℚ)
    (ρ : ℍ[ℚ, -3, 0, b] →ₐ[ℚ] Module.End ℚ V) (E : LinearMap.BilinForm ℚ V)
    (X : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    X ∈ complexSpan (skewCentralizerOfFamily E
      (fun i => ρ (QuaternionAlgebra.basisOneIJK (-3 : ℚ) 0 b i))) ↔
      (∀ z w, E.baseChange ℂ (X z) w + E.baseChange ℂ z (X w) = 0) ∧
      ∀ q, X * quaternionComplexAction b ρ q = quaternionComplexAction b ρ q * X := by
  rw [skewCentralizerOfFamily_baseChange, quaternionComplexAction_centralizer]

end HodgeLean.Foundations.Abdulali
