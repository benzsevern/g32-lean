import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedNormalizedResidualOpenCover
import HodgeLean.Foundations.Program.G32Native.PairedC3QuotientRulingCharts

/-! # The actual normalized local maps for the selected ruling -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

attribute [local instance] G32JointSlicedComponent.sliceImmersion
open HodgeLean.Foundations.Program.G32Native



open AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The original neighbourhoods and coefficients of the selected Rees charts.
The data store equations and maps, without ruling assertions.
Source: Hartshorne, Algebraic Geometry, II.3 and II.7.13. -/
structure PairedC3SelectedRulingParameters
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) where
  U : {x : ComplexPoint (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))) //
      x.underlying ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support} → (P.T.B i.castSucc).left.affineOpens
  V : {x : ComplexPoint (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))) //
      x.underlying ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support} → Fin 2 → (P.T.B i.succ).left.affineOpens
  contains : ∀ x, (Point.map (P.C.slices i.castSucc) x.val).underlying ∈ (U x).1
  chartCover : ∀ x, (V x 0).1 ⊔ (V x 1).1 = (P.T.b i).left ⁻¹ᵁ (U x).1
  u : ∀ x, Γ((P.T.B i.castSucc).left, U x)
  v : ∀ x, Γ((P.T.B i.castSucc).left, U x)
  α : ∀ x, Γ((P.T.B i.castSucc).left, U x)
  h₀ : ∀ x, (V x 0).1 ≤ (P.T.b i).left ⁻¹ᵁ (U x).1
  h₁ : ∀ x, (V x 1).1 ≤ (P.T.b i).left ⁻¹ᵁ (U x).1
  s : ∀ x, Γ((P.T.B i.succ).left, V x 0)
  t : ∀ x, Γ((P.T.B i.succ).left, V x 1)
  equations :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let D := K ⊔ (P.C.slices i.castSucc).left.ker
    ∀ x,
    (P.T.D i.castSucc ⟨2 * i.val, by omega⟩).ideal (U x) = Ideal.span {(u x)} ∧
        (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal (U x) = Ideal.span {(v x)} ∧
        ((P.C.slices i.castSucc).left.app (U x).1).hom ((v x) - (α x) * (u x)) = 0 ∧
        IsUnit (((P.C.slices i.castSucc).left.app (U x).1).hom (α x)) ∧
        IsUnit (Ideal.Quotient.mk (D.ideal (U x)) (α x)) ∧
        let f₀ : Γ((P.T.B i.castSucc).left, U x) →+*
          Γ((P.T.B i.succ).left, V x 0) := ((P.T.b i).left.appLE (U x).1 (V x 0).1 (h₀ x)).hom
        let f₁ : Γ((P.T.B i.castSucc).left, U x) →+*
          Γ((P.T.B i.succ).left, V x 1) := ((P.T.b i).left.appLE (U x).1 (V x 1).1 (h₁ x)).hom
        f₀ (u x) = (s x) * f₀ (v x) ∧ f₁ (v x) = (t x) * f₁ (u x) ∧
        Function.Surjective (Polynomial.eval₂RingHom f₀ (s x)) ∧
        RingHom.ker (Polynomial.eval₂RingHom f₀ (s x)) =
          Ideal.span {Polynomial.C (u x) - (Polynomial.X : Polynomial Γ((P.T.B i.castSucc).left, U x)) * Polynomial.C (v x)} ∧
        Function.Surjective (Polynomial.eval₂RingHom f₁ (t x)) ∧
        RingHom.ker (Polynomial.eval₂RingHom f₁ (t x)) =
          Ideal.span {Polynomial.C (v x) - (Polynomial.X : Polynomial Γ((P.T.B i.castSucc).left, U x)) * Polynomial.C (u x)}
  covers :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let D := K ⊔ (P.C.slices i.castSucc).left.ker
    (⨆ j : {x : ComplexPoint (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))) //
      x.underlying ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support} × Fin 2,
      (D.comap (P.T.b i).left).subschemeι ⁻¹ᵁ (V j.1 j.2).1) = ⊤

/-- Select the original normalized chart equations once, retaining their witnesses. -/
def pairedC3SelectedRulingParameters
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r) : PairedC3SelectedRulingParameters R P i := by
  classical
  choose U V hx hc hd ht using pairedC3_selected_normalized_residual_open_cover R P i hi
  choose u v α h₀ h₁ s t hdata using hd
  exact ⟨U, V, hx, hc, u, v, α, h₀, h₁, s, t, hdata, ht⟩

#print axioms pairedC3SelectedRulingParameters
end HodgeLean.Foundations.Program.ResidueSelected
