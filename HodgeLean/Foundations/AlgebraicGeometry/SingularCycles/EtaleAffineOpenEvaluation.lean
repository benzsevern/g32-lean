import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.EtaleHolomorphicEvaluation
import HodgeLean.Foundations.Program.SchoenCycleSectionEvaluation
import HodgeLean.Foundations.Program.SchoenCycleComplexSectionPullback

/-! # Holomorphic evaluations on affine étale neighbourhoods

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open Set Filter Topology HodgeLean.Foundations.Analytic HodgeLean.Foundations.Program
namespace AlgebraicGeometry.SingularCycles

/-- Continuous lifts on affine étale neighbourhoods preserve holomorphic regular evaluations.
Source: SGA 1, Exposé XII, §1; regular section pullback and étale algebra evaluation. -/
theorem etale_affineOpen_lift_evaluation {M : Type*} [TopologicalSpace M]
    (S : an_ReducedSpace M) {U : Set M} (hU : IsOpen U)
    {X Z : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (f : X ⟶ Z) [Etale f.left]
    (A : Z.left.Opens) (hA : IsAffineOpen A) (B : X.left.Opens) (hB : IsAffineOpen B)
    (hBA : B ≤ f.left ⁻¹ᵁ A) (s : U → ComplexPoint X) (hs : Continuous s)
    (hsB : ∀ y, (s y).underlying ∈ B)
    (hbase : ∀ a : Γ(Z.left, A), S.IsHolFun
      (fun y => Point.evaluate A a (Point.map f (s y))))
    (b : Γ(X.left, B)) : S.IsHolFun (fun y => Point.evaluate B b (s y)) := by
  letI := s2e_step1_sectionAlgebra X B
  letI := s2e_step1_sectionAlgebra Z A
  let G := s2e_complex_section_pullback X Z f A B hBA
  letI : Algebra Γ(Z.left, A) Γ(X.left, B) := G.toRingHom.toAlgebra
  letI : IsScalarTower ℂ Γ(Z.left, A) Γ(X.left, B) :=
    IsScalarTower.of_algebraMap_eq (fun c => (G.commutes c).symm)
  haveI : Algebra.Etale Γ(Z.left, A) Γ(X.left, B) :=
    RingHom.etale_algebraMap.mp (f.left.etale_appLE hA hB hBA)
  let E : U → (Γ(X.left, B) →ₐ[ℂ] ℂ) := fun y => s2e_step1_pointEvaluation X B
    (s y) (s2e_step1_point_preimage X (s y) B (hsB y))
  have heq : ∀ y c, E y c = Point.evaluate B c (s y) := by
    intro y c
    exact (s2e_regular_evaluation_eq_pointEvaluation X B (s y) (hsB y) _ c).symm
  have hcont : ∀ c, Continuous (fun y => E y c) := by
    intro c
    simp_rw [heq]
    exact (anb_isHolFun_continuous _ (f4_isHolFun_evaluate X B c)).comp
      (hs.subtype_mk hsB)
  have hEa : ∀ a : Γ(Z.left, A), S.IsHolFun
      (fun y => E y (algebraMap Γ(Z.left, A) Γ(X.left, B) a)) := by
    intro a
    have hval : (fun y => E y (algebraMap Γ(Z.left, A) Γ(X.left, B) a)) =
        (fun y => Point.evaluate A a (Point.map f (s y))) := by
      funext y
      rw [heq]
      change Point.evaluate B ((f.left.appLE A B hBA).hom a) (s y) = _
      exact (Point.evaluate_res hBA (f.left.app A a) (s y) (hsB y)).symm.trans
        (Point.evaluate_map f A a (s y)).symm
    rw [hval]
    exact hbase a
  have h := etale_holomorphic_evaluation S hU E hcont hEa b
  simpa only [heq] using h

end AlgebraicGeometry.SingularCycles
