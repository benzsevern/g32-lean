import HodgeLean.Foundations.QuotientDuality.DualityBaseChangeDefs

/-! # Comparison transport for quotient duality

Maps retain their coefficient field and the direction of pullback.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Transport an endomorphism through a specified comparison.
Source: Serre, Linear Representations of Finite Groups, section 2.6. -/
def comparisonEnd {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (c : V ≃ₗ[K] W) (P : V →ₗ[K] V) : W →ₗ[K] W :=
  c.toLinearMap.comp (P.comp c.symm.toLinearMap)
example : comparisonEnd (LinearEquiv.neg ℚ) (LinearMap.id : ℚ →ₗ[ℚ] ℚ) (3 : ℚ) = 3 := by
  simp [comparisonEnd]

/-- Transport a pairing with contravariance in both entries.
Source: Hatcher, Algebraic Topology, section 3.3. -/
def comparisonPairing {V W A B : Type*}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
    (c : V ≃ₗ[ℚ] A) (e : W ≃ₗ[ℚ] B) (P : V →ₗ[ℚ] Module.Dual ℚ W) :
    A →ₗ[ℚ] Module.Dual ℚ B :=
  e.symm.toLinearMap.dualMap.comp (P.comp c.symm.toLinearMap)
example : comparisonPairing (LinearEquiv.neg ℚ) (LinearEquiv.refl ℚ ℚ)
    (LinearMap.mul ℚ ℚ) (3 : ℚ) (4 : ℚ) = -12 := by
  norm_num [comparisonPairing]

/-- Integration after forgetting the specified support.
Source: Hatcher, Algebraic Topology, sections 3.1 and 3.3. -/
def supportedIntegral (X : TopCat.{0}) (Z : Set X) (n : ℕ) (c : Homology ℚ X n) :=
  (orientationIntegral X n c).comp (forgetSupport ℚ X Z n)
example (X : TopCat.{0}) (Z : Set X) (n : ℕ) (c : Homology ℚ X n) :
    supportedIntegral X Z n c 0 = 0 := map_zero _

/-- A cyclic weighted average transported through an additive comparison.
Source: Serre, Linear Representations of Finite Groups, section 2.6, Theorem 8. -/
def comparisonAverage {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] (c : V ≃+ W) (D : V →ₗ[K] V) (m : ℕ) (z : K) : W →+ W :=
  c.toAddMonoidHom.comp
    (((m : K)⁻¹ • ∑ i ∈ Finset.range m, z ^ i • D ^ i).toAddMonoidHom.comp
      c.symm.toAddMonoidHom)
example : comparisonAverage (AddEquiv.neg ℚ) (-LinearMap.id : ℚ →ₗ[ℚ] ℚ)
    2 (-1 : ℚ) (3 : ℚ) = 3 := by
  norm_num [comparisonAverage, Finset.sum_range_succ]

end HodgeLean.Foundations.QuotientDuality
