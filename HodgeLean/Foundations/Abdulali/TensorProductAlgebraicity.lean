import HodgeLean.Foundations.Abdulali.ComplexCup
import HodgeLean.Foundations.Program.MilneIntegration

noncomputable section
set_option maxHeartbeats 20000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 20000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
attribute [local irreducible] cupProductOf algebraicCycleClassSpan

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- The two existing complex cup comparisons use the same exterior coordinates.
Source: scalar extension of the cup-wedge equivalence. -/
theorem complexCupEquiv_f1575 (n : ℕ) (v : ⋀[ℂ]^n (ℂ ⊗[ℚ] HQ Y 1)) :
    complexCupEquiv Y n v =
      f1575ExteriorCohomology (torusCohomology_cupProductOf Y) n v := by
  letI := (torusCohomology_cupProductOf Y).finite
  rw [f1575ExteriorCohomology_eq_baseChange]
  change (((torusCohomology_cupProductOf Y).cupWedgeEquiv n).baseChange ℚ ℂ)
      ((WeilPower.exteriorBaseChange n).symm v) =
    (((torusCohomology_cupProductOf Y).cupWedgeEquiv n).toLinearMap.baseChange ℂ)
      ((WeilPower.exteriorBaseChange n).symm v)
  rfl

/-- Cup comparison commutes with multiplication in the complex exterior algebra.
Source: Birkenhake–Lange, Complex Abelian Varieties, Lemma 1.3.1. -/
theorem complexCupEquiv_wedge (i j : ℕ)
    (v : ⋀[ℂ]^i (ℂ ⊗[ℚ] HQ Y 1)) (w : ⋀[ℂ]^j (ℂ ⊗[ℚ] HQ Y 1)) :
    complexCupEquiv Y (i+j) (exteriorPower.wedge ℂ _ i j v w) =
      (cupProductOf Y).cupC rfl (complexCupEquiv Y i v) (complexCupEquiv Y j w) := by
  rw [complexCupEquiv_f1575, complexCupEquiv_f1575, complexCupEquiv_f1575]
  exact f1575ExteriorCohomology_wedge (torusCohomology_cupProductOf Y) i j v w


/-- Alternating tensor products map to cup products under any degree-one map.
Source: functoriality of exterior algebras and cycle products, Fulton, §19. -/
theorem tensorCup_append (f : V →ₗ[ℂ] (ℂ ⊗[ℚ] HQ Y 1)) (i j : ℕ)
    (a : ⨂[ℂ]^i V) (b : ⨂[ℂ]^j V) :
    complexCupEquiv Y (i+j) (exteriorPower.map (i+j) f
      (InvariantsExterior.wedgeQuotient (i+j)
        (InvariantsExterior.tensorAppend i j (a ⊗ₜ[ℂ] b)))) =
    (cupProductOf Y).cupC rfl
      (complexCupEquiv Y i (exteriorPower.map i f (InvariantsExterior.wedgeQuotient i a)))
      (complexCupEquiv Y j (exteriorPower.map j f (InvariantsExterior.wedgeQuotient j b))) := by
  rw [InvariantsExterior.wedgeQuotient_tensorAppend]
  have hm : exteriorPower.map (i+j) f (exteriorPower.wedge ℂ V i j
      (InvariantsExterior.wedgeQuotient i a) (InvariantsExterior.wedgeQuotient j b)) =
      exteriorPower.wedge ℂ _ i j
        (exteriorPower.map i f (InvariantsExterior.wedgeQuotient i a))
        (exteriorPower.map j f (InvariantsExterior.wedgeQuotient j b)) := by
    apply Subtype.ext
    simp only [exteriorPower.coe_map, Symplectic.coe_wedge, map_mul]
  rw [hm, complexCupEquiv_wedge]


end HodgeLean.Foundations.Abdulali
