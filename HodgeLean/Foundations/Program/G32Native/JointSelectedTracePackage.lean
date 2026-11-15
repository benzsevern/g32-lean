import HodgeLean.Foundations.Program.G32Native.JointSelectedBase
import HodgeLean.Foundations.Program.G32Native.SelectedTowerAdjoint
import HodgeLean.Foundations.Program.G32Native.SelectedTowerPointClasses

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.Program
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure G32JointTracePackage
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (T : G32JointBase R)
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (eFinal : s2b_normalizationOver (T.B (Fin.last R.r)) (T.η (Fin.last R.r)) ≅ W)
    (f : ∀ i, s2b_normalizationOver (T.B i) (T.η i) ⟶ R.W₀) where
  trr : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W)) (2 * (2 * R.P.k)) →ₗ[ℚ] ℚ
  tr₀ : AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint R.W₀)) (2 * (2 * R.P.k)) →ₗ[ℚ] ℚ
  h_T15_final : Function.Bijective (s2e_middlePairing (TopCat.of (ComplexPoint W)) R.P.k trr)
  h_T15_initial : Function.Bijective (s2e_middlePairing (TopCat.of (ComplexPoint R.W₀)) R.P.k tr₀)
  h_T16_final_point : (∃ (U : W.left.Opens) (x : ComplexPoint W),
        Point.underlying x ∈ U ∧ Smooth (U.ι ≫ W.hom) ∧
        ∃ c, a3b4_IsCycleClass W.hom (s2e_componentCycle x ℚ) (2 * R.P.k) c ∧
          trr (s2e_classToAbsolute W (s2e_componentCycle x ℚ) (2 * R.P.k) c) = 1)
  h_T16_initial_point : (∃ (U : R.W₀.left.Opens) (x : ComplexPoint R.W₀),
        Point.underlying x ∈ U ∧ Smooth (U.ι ≫ R.W₀.hom) ∧
        ∃ c, a3b4_IsCycleClass R.W₀.hom (s2e_componentCycle x ℚ) (2 * R.P.k) c ∧
          tr₀ (s2e_classToAbsolute R.W₀ (s2e_componentCycle x ℚ) (2 * R.P.k) c) = 1)
  G : (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W)) (2 * R.P.k)) →ₗ[ℚ] (AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint R.W₀)) (2 * R.P.k))
  h_T18_adjoint : (∀ u v, s2e_middlePairing (TopCat.of (ComplexPoint R.W₀)) R.P.k tr₀ (G u) v =
        s2e_middlePairing (TopCat.of (ComplexPoint W)) R.P.k trr u (s2e_pullback ℚ (eFinal.inv ≫ f (Fin.last R.r)) (2 * R.P.k) v))
  h_T18_retraction : (∀ v, G (s2e_pullback ℚ (eFinal.inv ≫ f (Fin.last R.r)) (2 * R.P.k) v) = v)
  h_T18_deck : (∀ v, G (s2e_pullback ℚ (eFinal.inv ≫ T.d (Fin.last R.r) ≫ eFinal.hom) (2 * R.P.k) v) = s2e_pullback ℚ R.d₀ (2 * R.P.k) (G v))

end HodgeLean.Foundations.Program
