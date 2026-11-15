import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNRulingCharts
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNMarkedZero
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNMarkedOne
import HodgeLean.Foundations.Program.G32Native.PairedC3CanonicalIntersectionFibre
import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveMarkedPoint
import HodgeLean.Foundations.Program.G32Native.PairedResidualDiagram

/-! # Normalized ruling maps at every retained stage -/
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


open CategoryTheory.Limits
open AlgebraicGeometry.RamifiedNormalization.StageFour


/-- Each specified normalized ratio map has the actual slice intersection
as its fibre over the diagonal marked point.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.3, II.7.13 and III.10. -/
theorem pairedC3_route_n_ruling_chart_marked
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let M := (K ⊔ (P.C.slices i.castSucc).left.ker).comap (P.T.b i).left
    let A := pairedC3RouteNRulingCharts R P i
    let U := pairedC3ResidualQuotientCover.{0,0,0} M A.V A.covers
    let a := (residualIntersection (P.C.slices i.succ) M).hom
    let b := (residualIntersectionSecond (P.C.slices i.succ) M).left
    ∀ j, IsPullback (U.pullbackHom b j) ((U.pullback₁ b).f j ≫ a)
      (A.map j).left (projectiveLineChart 1 (1 : ℂ)).left := by
  classical
  let C := pairedC3RouteNRulingParameters R P i
  let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  let D := K ⊔ (P.C.slices i.castSucc).left.ker
  let M := D.comap (P.T.b i).left
  dsimp only
  intro j
  rcases j with ⟨x, k⟩
  refine Fin.cases ?_ (fun l => ?_) k
  · let base := pairedC3AffineResidualCoefficient (P.T.b i).left D (C.U x) (C.V x 0) (C.h₀ x)
    let β := Units.map base.toMonoidHom (C.equations x).2.2.2.2.1.unit
    let z := (↑β : Γ((P.T.B i.succ).left, C.V x 0) ⧸ M.ideal (C.V x 0)) *
      Ideal.Quotient.mk (M.ideal (C.V x 0)) (C.s x)
    letI := pairedC3SpecAlgebra (M.subschemeCover.f (C.V x 0) ≫
      M.subschemeι ≫ (P.T.B i.succ).hom)
    have h := pairedC3_canonical_intersection_fibre (P.T.B i.succ)
      (P.C.slices i.succ).left.ker M (C.V x 0) 0 z
      (pairedC3_route_n_parameter_marked_ideal_0 R P i C x)
    rw [pairedC3_projective_marked_chart_eq] at h
    exact h
  · have hl : l = 0 := Subsingleton.elim _ _
    subst l
    let base := pairedC3AffineResidualCoefficient (P.T.b i).left D (C.U x) (C.V x 1) (C.h₁ x)
    let β := Units.map base.toMonoidHom (C.equations x).2.2.2.2.1.unit
    let z := (↑β⁻¹ : Γ((P.T.B i.succ).left, C.V x 1) ⧸ M.ideal (C.V x 1)) *
      Ideal.Quotient.mk (M.ideal (C.V x 1)) (C.t x)
    letI := pairedC3SpecAlgebra (M.subschemeCover.f (C.V x 1) ≫
      M.subschemeι ≫ (P.T.B i.succ).hom)
    have h := pairedC3_canonical_intersection_fibre (P.T.B i.succ)
      (P.C.slices i.succ).left.ker M (C.V x 1) 1 z
      (pairedC3_route_n_parameter_marked_ideal_1 R P i C x)
    rw [pairedC3_projective_marked_chart_eq] at h
    exact h

#print axioms pairedC3_route_n_ruling_chart_marked
end HodgeLean.Foundations.Program.ResidueSelected
