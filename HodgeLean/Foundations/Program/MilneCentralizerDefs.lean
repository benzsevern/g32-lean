import HodgeLean.Foundations.Program.G32PropFourSixDefs
import HodgeLean.Foundations.PositivePolarization
import HodgeLean.Foundations.InvariantsExterior

/-! # Endomorphism centralizer and the complex polarization form

Concrete linear objects for the complex Betti specialization of Milne's group.
The action on H¹ is contravariant; its value is read using `MulOpposite.unop`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

/-- The complex centralizer of the rational endomorphism action on H¹.
Source: Milne, Lefschetz classes on abelian varieties (1999), §1, definition of C(A),
transported from homology to cohomology. -/
def m0_endCentralizer (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] :
    Subalgebra ℂ (Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) :=
  Subalgebra.centralizer ℂ
    (Set.range fun φ : AbelianEnd0 J => ((abelianEnd0Action J φ).unop).baseChange ℂ)

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] :
    (1 : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) ∈ m0_endCentralizer J :=
  (m0_endCentralizer J).one_mem

/-- The bilinear, not Hermitian, extension of the rational dual polarization form.
Source: Birkenhake–Lange, Complex Abelian Varieties, 2nd ed., §5.1;
`polarizationForm` and `LinearMap.BilinForm.baseChange`. -/
def m0_form (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) :
    LinearMap.BilinForm ℂ (ℂ ⊗[ℚ] HQ J 1) :=
  (polarizationForm (torusCohomology_cupProductOf J) hη).baseChange ℂ

example (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (x y : HQ J 1) :
    m0_form J pol hη (1 ⊗ₜ[ℚ] x) (1 ⊗ₜ[ℚ] y) =
      (polarizationForm (torusCohomology_cupProductOf J) hη x y : ℂ) := by
  simp [m0_form, LinearMap.BilinForm.baseChange_tmul]

/-- The normalized alternating lift on the degree-one space of a power.
Source: Bourbaki, Algebra, Chapter III, §7; the normalization in
`InvariantsExterior.exteriorProjector`. -/
def m0_tensorLift (J : Over (Spec ↧ℂ)) [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom] (r n : ℕ) :
    (⋀[ℂ]^n (Fin r → ℂ ⊗[ℚ] HQ J 1)) →ₗ[ℂ]
      ⨂[ℂ]^n (Fin r → ℂ ⊗[ℚ] HQ J 1) :=
  (n.factorial : ℂ)⁻¹ • exteriorPower.toTensorPower ℂ _ n

example (J : Over (Spec ↧ℂ)) [IsIntegral J.left]
    [Smooth J.hom] [IsProjective J.hom] (r n : ℕ)
    (v : ⋀[ℂ]^n (Fin r → ℂ ⊗[ℚ] HQ J 1)) :
    InvariantsExterior.wedgeQuotient n (m0_tensorLift J r n v) = v := by
  simp only [m0_tensorLift, LinearMap.smul_apply, map_smul,
    InvariantsExterior.wedgeQuotient_toTensorPower, smul_smul]
  rw [inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_smul]

end HodgeLean.Foundations.Program
