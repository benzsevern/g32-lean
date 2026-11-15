import HodgeLean.Foundations.Program.SchoenTowerL1aRationalStabilizers
import HodgeLean.Foundations.Program.SchoenTowerOverSections
import HodgeLean.Foundations.Program.SchoenTowerAffineComplexPoints

/-! # Actual affine rational points and section actions

Implication from the actual inverse-pullback section action to the corresponding
rational point action and its kernel stabilizers.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped Pointwise
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- Actual affine point evaluation is natural for the actual section algebra map.
Source: Hartshorne, Algebraic Geometry, II.2, pullback and rational evaluation. -/
theorem s2v_l1a_affine_point_evaluation_map
    {X Y : Over (Spec ↧ℂ)} (f : X ⟶ Y) (p : ComplexPoint X) :
    s2t_affinePointAlgHom Y (Point.map f p) =
      (s2t_affinePointAlgHom X p).comp (s2t_overSectionsAlgHom f) := by
  ext s
  rw [s2t_affinePointAlgHom_apply]
  change Point.evaluate ⊤ s (Point.map f p) = s2t_affinePointAlgHom X p (f.left.appTop s)
  rw [s2t_affinePointAlgHom_apply]
  exact Point.evaluate_map f ⊤ s p

/-- The actual rational evaluation kernel stabilizer is exactly the actual
point stabilizer, with section pullback by inverse automorphisms.
Source: Hartshorne, Algebraic Geometry, II.2, rational points of affine schemes. -/
theorem s2v_l1a_affine_point_kernel_stabilizer
    (X : Over (Spec ↧ℂ)) [IsAffine X.left] (G : Type) [Group G]
    (a : G →* Aut X) (p : ComplexPoint X) (g : G) :
    let a' := ((Over.forget (Spec ↧ℂ)).mapAut X).comp a
    letI := s2_schemeSectionAction X.left G a'
    g • RingHom.ker (s2t_affinePointAlgHom X p).toRingHom =
      RingHom.ker (s2t_affinePointAlgHom X p).toRingHom ↔
        Point.map (a g).asIso.hom p = p := by
  let a' := ((Over.forget (Spec ↧ℂ)).mapAut X).comp a
  letI := s2_schemeSectionAction X.left G a'
  letI := s2t_overSectionAction_smulCommClass X G a
  dsimp only
  rw [s2v_l1a_rational_kernel_stabilizer]
  have heq : (s2t_affinePointAlgHom X p).comp
      (MulSemiringAction.toAlgHom ℂ Γ(X.left, ⊤) g⁻¹) =
        s2t_affinePointAlgHom X (Point.map (a g).asIso.hom p) := by
    rw [s2v_l1a_affine_point_evaluation_map]
    ext s
    change s2t_affinePointAlgHom X p
      ((a ((g⁻¹)⁻¹)).asIso.hom.left.appTop s) =
        s2t_affinePointAlgHom X p ((a g).asIso.hom.left.appTop s)
    rw [inv_inv]
  rw [heq]
  exact ⟨(fun h => s2t_affinePointAlgHom_injective X h), fun h => congrArg (s2t_affinePointAlgHom X) h⟩

end HodgeLean.Foundations.Program
