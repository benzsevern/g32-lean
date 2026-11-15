import HodgeLean.Foundations.Program.G32Native.PairedC3AffineRatioData

/-! # Restricting normalized parameters without changing their slice units -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- The coefficient map to a residual chart commutes with further affine
restriction as a ring homomorphism on the entire base quotient. -/
theorem pairedC3_residual_coefficient_restriction_hom
    {X Y : Scheme} (p : Y ⟶ X) (D : X.IdealSheafData)
    (U : X.affineOpens) (V W : Y.affineOpens)
    (hV : V.1 ≤ p ⁻¹ᵁ U.1) (hWV : W.1 ≤ V.1) :
    (pairedC3AffineResidualRestriction (D.comap p) V W hWV).comp
      (pairedC3AffineResidualCoefficient p D U V hV) =
      pairedC3AffineResidualCoefficient p D U W (hWV.trans hV) := by
  ext a
  exact pairedC3_affine_residual_restriction_coefficients p D U V W hV hWV a

namespace PairedC3AffineRatioData
variable {X Q : Scheme} {Y : Over (Spec ↧ℂ)} {p : Y.left ⟶ X} {i : Q ⟶ X}
  {D₀ D₁ : X.IdealSheafData}

/-- The restricted parameter keeps the originally chosen normalization unit
and restricts the actual raw ratio section. -/
theorem parameter_restriction (A : PairedC3AffineRatioData Y p i D₀ D₁)
    (W : Y.left.affineOpens) (hWV : W.1 ≤ A.V.1) :
    let D := (D₀ ⊔ D₁) ⊔ i.ker
    let F := pairedC3AffineResidualCoefficient p D A.U W (hWV.trans A.liesOver)
    let β := Units.map F.toMonoidHom A.unit.unit
    pairedC3AffineResidualRestriction (D.comap p) A.V W hWV A.parameter =
      (if A.k = 0 then (β : _) else ↑β⁻¹) *
        Ideal.Quotient.mk ((D.comap p).ideal W)
          ((Y.left.presheaf.map (homOfLE hWV).op).hom A.t) := by
  let D := (D₀ ⊔ D₁) ⊔ i.ker
  let r := pairedC3AffineResidualRestriction (D.comap p) A.V W hWV
  let F := pairedC3AffineResidualCoefficient p D A.U A.V A.liesOver
  let G := pairedC3AffineResidualCoefficient p D A.U W (hWV.trans A.liesOver)
  let β := Units.map F.toMonoidHom A.unit.unit
  let γ := Units.map G.toMonoidHom A.unit.unit
  have hβ : Units.map r.toMonoidHom β = γ := by
    apply Units.ext
    exact congrArg (fun f => f (A.unit.unit : Γ(X, A.U) ⧸ D.ideal A.U))
      (pairedC3_residual_coefficient_restriction_hom p D A.U A.V W A.liesOver hWV)
  have hval : r (β : _) = (γ : _) := congrArg Units.val hβ
  have hinv : r (↑β⁻¹ : _) = (↑γ⁻¹ : _) := by
    change (↑(Units.map r.toMonoidHom β)⁻¹ : Γ(Y.left, W) ⧸ (D.comap p).ideal W) = _
    rw [hβ]
  change r ((if A.k = 0 then (β : _) else ↑β⁻¹) * _) =
    (if A.k = 0 then (γ : _) else ↑γ⁻¹) * _
  rw [map_mul]
  by_cases hk : A.k = 0
  · simp only [hk, ite_true, hval]
    rfl
  · simp only [hk, ite_false, hinv]
    rfl

end PairedC3AffineRatioData
#print axioms pairedC3_residual_coefficient_restriction_hom
#print axioms PairedC3AffineRatioData.parameter_restriction
end HodgeLean.Foundations.Program.G32Native
