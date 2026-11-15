import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNRulingCharts
import HodgeLean.Foundations.Program.G32Native.PairedC3ProjectiveParameterSmooth
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNResidualBaseSmooth

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


/-- Each specified normalized ratio map is smooth into the projective line.
Source: Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.3, II.7.13 and III.10. -/
theorem pairedC3_route_n_ruling_chart_smooth
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
    ∀ j, Smooth (A.map j).left := by
  classical
  let C := pairedC3RouteNRulingParameters R P i
  let U := C.U
  let V := C.V
  let u := C.u
  let v := C.v
  let h₀ := C.h₀
  let h₁ := C.h₁
  let s := C.s
  let t := C.t
  let hdata := C.equations
  let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  let D := K ⊔ (P.C.slices i.castSucc).left.ker
  let M := D.comap (P.T.b i).left
  have hbase : Smooth (D.subschemeι ≫ (P.T.B i.castSucc).hom) :=
    pairedC3_route_n_residual_base_smooth R P i
  have huM x : u x ∈ D.ideal (U x) := by
    apply (show P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ≤ D from
      le_sup_of_le_left le_sup_left) (U x)
    rw [(hdata x).1]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hvM x : v x ∈ D.ideal (U x) := by
    apply (show P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩ ≤ D from
      le_sup_of_le_left le_sup_right) (U x)
    rw [(hdata x).2.1]
    exact Ideal.subset_span (Set.mem_singleton _)
  dsimp only
  intro j
  rcases j with ⟨x, k⟩
  refine Fin.cases ?_ (fun l => ?_) k
  · let base := pairedC3AffineResidualCoefficient (P.T.b i).left D (U x) (V x 0) (h₀ x)
    let β := Units.map base.toMonoidHom (hdata x).2.2.2.2.1.unit
    change Smooth (pairedC3ResidualProjectiveMap (P.T.B i.succ) M (V x 0) 0
      ((β : Γ((P.T.B i.succ).left, V x 0) ⧸ M.ideal (V x 0)) *
        Ideal.Quotient.mk (M.ideal (V x 0)) (s x))).left
    letI := pairedC3SpecAlgebra (M.subschemeCover.f (V x 0) ≫
      M.subschemeι ≫ (P.T.B i.succ).hom)
    dsimp only [pairedC3ResidualProjectiveMap, Over.homMk_left]
    apply pairedC3_projective_parameter_smooth
    exact pairedC3_supplied_scaled_smooth _ _ (P.T.b i) D (U x) (V x 0) (h₀ x)
      (u x) (v x) (huM x) (hvM x) (s x)
      (hdata x).2.2.2.2.2.2.2.1 (hdata x).2.2.2.2.2.2.2.2.1
      (hdata x).2.2.2.2.1.unit hbase
  · have hl : l = 0 := Subsingleton.elim _ _
    subst l
    let base := pairedC3AffineResidualCoefficient (P.T.b i).left D (U x) (V x 1) (h₁ x)
    let β := Units.map base.toMonoidHom (hdata x).2.2.2.2.1.unit
    change Smooth (pairedC3ResidualProjectiveMap (P.T.B i.succ) M (V x 1) 1
      ((↑β⁻¹ : Γ((P.T.B i.succ).left, V x 1) ⧸ M.ideal (V x 1)) *
        Ideal.Quotient.mk (M.ideal (V x 1)) (t x))).left
    letI := pairedC3SpecAlgebra (M.subschemeCover.f (V x 1) ≫
      M.subschemeι ≫ (P.T.B i.succ).hom)
    dsimp only [pairedC3ResidualProjectiveMap, Over.homMk_left]
    apply pairedC3_projective_parameter_smooth
    exact pairedC3_supplied_scaled_smooth _ _ (P.T.b i) D (U x) (V x 1) (h₁ x)
      (v x) (u x) (hvM x) (huM x) (t x)
      (hdata x).2.2.2.2.2.2.2.2.2.1 (hdata x).2.2.2.2.2.2.2.2.2.2
      (hdata x).2.2.2.2.1.unit⁻¹ hbase


#print axioms pairedC3_route_n_ruling_chart_smooth
end HodgeLean.Foundations.Program.ResidueSelected
