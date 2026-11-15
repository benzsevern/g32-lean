import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian8
import HodgeLean.Foundations.Program.PrymFamilyPositivity
import HodgeLean.Foundations.Program.MilneCentralizerDefs
import HodgeLean.Foundations.PositivePolarization
import HodgeLean.Foundations.LieReductiveProofs
import HodgeLean.Foundations.Program.MilneFactorsSemisimple

noncomputable section

open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic

namespace HodgeLean.Foundations.Program

theorem m1_hodgeEnd_semisimple_of_polarization (J : Over (Spec ↧ℂ))
    [GrpObj J] [IsCommMonObj J] [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {pol : HQ J 2} (hP : p1_IsPolarization J pol) : IsSemisimpleRing (hodgeEndH1 J) := by
  letI := (torusCohomology_cupProductOf J).finite
  apply pol2_semisimple_of_trace_separates (hodgeEndH1 J).val
  intro x hx
  by_contra hzero
  have hx0 : x.val ≠ 0 := fun h => hzero (Subtype.ext h)
  let hη := p1_isNondegenerate J hP
  let y : hodgeEndH1 J := ⟨p1_adjoint _ hη x.val,
    p1r_adjoint_mem_hodgeEndH1 J hη (p1_mem_hdg J hP) x.property⟩
  have hI : weightOneComplexStructure J (finiteBetti_abelian J)
      (spec_bettiDeRhamIso_abelian J) ∘ₗ weightOneComplexStructure J
      (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J) = -LinearMap.id :=
    LinearMap.ext (spec_weightOneComplexStructure J (finiteBetti_abelian J)
      (spec_bettiDeRhamIso_abelian J)).1
  have hp := p1l_trace_pos hP hI
    (p1r_baseChange_comp_weightOneComplexStructure J x.property) hx0 hη
  have hz := hx y
  change LinearMap.trace ℚ (HQ J 1) (y.val ∘ₗ x.val) = 0 at hz
  rw [LinearMap.trace_comp_comm'] at hz
  exact (ne_of_gt hp) hz


theorem m1_exists_positive_polarization (J : Over (Spec ↧ℂ))
    [GrpObj J] [IsCommMonObj J] [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] :
    ∃ pol : HQ J 2, p1_IsPolarization J pol := by
  obtain ⟨D, hD⟩ := bh8_polarization J
  let Q : LinearMap.BilinForm ℤ (b2_abelianLattice J) :=
    LinearMap.mk₂ ℤ (fun l m => D.E l m)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp)
  have hQ : b2_IsRiemannForm (b2_abelianLattice J) (b2_abelianF J) Q := by
    apply (b2_abelian_isRiemannForm_iff J Q).mpr
    exact ⟨D.H, hD, D.integral⟩
  refine ⟨latticeClassHQ J (b2_bilinToAddHom Q), ?_⟩
  exact (p1_isPolarization_iff J _).mpr
    ⟨b2_abelian_nondegenerate J Q hQ, b63g4_abelian_positive J Q hQ⟩


theorem m1_centralizer_semisimple_of_polarization (J : Over (Spec ↧ℂ))
    [GrpObj J] [IsCommMonObj J] [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {pol : HQ J 2} (hP : p1_IsPolarization J pol) :
    IsSemisimpleRing (m0_endCentralizer J) := by
  letI := (torusCohomology_cupProductOf J).finite
  letI := m1_hodgeEnd_semisimple_of_polarization J hP
  have he : (Set.range fun φ : AbelianEnd0 J =>
      ((abelianEnd0Action J φ).unop).baseChange ℂ) =
      Set.range (fun b : hodgeEndH1 J => b.val.baseChange ℂ) := by
    ext u
    constructor
    · rintro ⟨φ, rfl⟩
      exact ⟨⟨(abelianEnd0Action J φ).unop,
        spec_g4_abelianEnd0Action_mem_hodgeEndH1 J φ⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨φ, hφ⟩ := (p1r_mem_range_iff J b.val).mpr b.property
      exact ⟨φ, congrArg (LinearMap.baseChange ℂ) hφ⟩
  rw [m0_endCentralizer, he]
  exact m1_baseChange_commutant_semisimple (hodgeEndH1 J)

end HodgeLean.Foundations.Program
