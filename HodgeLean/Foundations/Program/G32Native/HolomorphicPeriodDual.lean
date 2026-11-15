import HodgeLean.Foundations.Program.G32Native.HolomorphicTangentDual
import HodgeLean.Foundations.Program.G32Native.GeometricPeriodNaturality

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Module TopologicalSpace
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program.G32Native
variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

/-- Holomorphic cohomology in the actual period coordinates is the tangent dual.
Source: Birkenhake–Lange, Complex Abelian Varieties, Theorem 1.4.1. -/
def holomorphicPeriodDual : complexHolomorphicH1 A ≃ₗ[ℂ]
    Module.Dual ℂ (Fin (dim A.left) → ℂ) :=
  (show complexHolomorphicH1 A ≃ₗ[ℂ] degreeOneLatticeHolomorphic (dim A.left) from
    { toFun := fun w => ⟨abelianPeriodComplexEquiv A w,
        (show w.val ∈ (degreeOneLatticeHolomorphic (dim A.left)).comap
          (abelianPeriodComplexEquiv A).toLinearMap from complexHolomorphicH1_eq A ▸ w.property)⟩
      invFun := fun φ => ⟨(abelianPeriodComplexEquiv A).symm φ, by
        rw [complexHolomorphicH1_eq]
        change abelianPeriodComplexEquiv A ((abelianPeriodComplexEquiv A).symm φ.val) ∈ degreeOneLatticeHolomorphic (dim A.left)
        rw [LinearEquiv.apply_symm_apply]
        exact φ.property⟩
      left_inv := fun w => Subtype.ext ((abelianPeriodComplexEquiv A).symm_apply_apply w)
      right_inv := fun φ => Subtype.ext ((abelianPeriodComplexEquiv A).apply_symm_apply φ)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
      map_smul' := fun _ _ => Subtype.ext (map_smul _ _ _) }).trans
    (holomorphicTangentDual (dim A.left)).symm

/-- Evaluation retains the period coordinates exactly.
Source: Birkenhake–Lange, Complex Abelian Varieties, §1.2. -/
theorem holomorphicPeriodDual_apply (w : complexHolomorphicH1 A)
    (v : Fin (dim A.left) → ℂ) :
    holomorphicPeriodDual A w v = abelianPeriodComplexEquiv A w v := rfl

#print axioms holomorphicPeriodDual
end HodgeLean.Foundations.Program.G32Native
