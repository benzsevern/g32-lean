import HodgeLean.Foundations.Program.SchoenCycleU1SpecSectionEvaluation
import HodgeLean.Foundations.Program.SchoenCycleU1SpecOver

/-! # Actual constant complex points over dual numbers -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A complex point extended constantly to the specified dual-number scheme.
Source: Hartshorne, Algebraic Geometry, II.8, constant tangent vectors. -/
def s2e_u1_constantDualPoint (X : Over (Spec ↧ℂ)) (x : ComplexPoint X) :
    s2e_u1_specOver (DualNumber ℂ) ⟶ X :=
  Over.homMk ((s2e_u1_specOver (DualNumber ℂ)).hom ≫ x.left) (by
    rw [Category.assoc, Over.w x]
    exact Category.comp_id _)

/-- A constant dual-number point lies entirely in every open containing
its specified complex point.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_u1_constantDualPoint_open (X : Over (Spec ↧ℂ)) (x : ComplexPoint X)
    (U : X.left.Opens) (hx : x.underlying ∈ U) :
    ⊤ ≤ (s2e_u1_constantDualPoint X x).left ⁻¹ᵁ U := by
  have hp := s2e_step1_point_preimage X x U hx
  intro z _
  exact hp (by trivial : (s2e_u1_specOver (DualNumber ℂ)).hom z ∈
    (⊤ : (Spec (CommRingCat.of ℂ)).Opens))

/-- A regular section evaluated on the actual constant dual point has zero
variation and its specified complex value as residue.
Source: Hartshorne, Algebraic Geometry, II.2 and II.8. -/
theorem s2e_u1_constantDualPoint_sectionEvaluation
    (X : Over (Spec ↧ℂ)) (x : ComplexPoint X)
    (U : X.left.Opens) (hx : x.underlying ∈ U) (a : Γ(X.left, U)) :
    s2e_u1_specSectionEvaluation X.left (s2e_u1_constantDualPoint X x).left U
      (s2e_u1_constantDualPoint_open X x U hx) a =
        TrivSqZeroExt.inl (Point.evaluate U a x) := by
  have hc := s2e_u1_specSectionEvaluation_comp (Spec (CommRingCat.of ℂ)) X.left
    (s2e_u1_specOver (DualNumber ℂ)).hom x.left U ⊤
    (s2e_step1_point_preimage X x U hx) (by simp)
    (s2e_u1_constantDualPoint_open X x U hx)
  change s2e_u1_specSectionEvaluation X.left
    ((s2e_u1_specOver (DualNumber ℂ)).hom ≫ x.left) U _ a = _
  rw [← hc]
  change ((s2e_u1_specSectionEvaluation (Spec (CommRingCat.of ℂ))
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)))) ⊤ (by simp)).comp
    (x.left.appLE U ⊤ (s2e_step1_point_preimage X x U hx)).hom) a = _
  rw [s2e_u1_specSectionEvaluation_specMap_top]
  change algebraMap ℂ (DualNumber ℂ)
    (s2e_step1_pointEvaluation X U x (s2e_step1_point_preimage X x U hx) a) = _
  rw [s2e_u1_pointEvaluation_eq_evaluate X U x hx a, TrivSqZeroExt.algebraMap_eq_inl]

end HodgeLean.Foundations.Program
