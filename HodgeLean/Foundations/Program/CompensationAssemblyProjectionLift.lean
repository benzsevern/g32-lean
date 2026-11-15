import HodgeLean.Foundations.Program.CompensationAssemblySurfacePrime

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology.Singular
open AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

theorem cq_relative_absolute_exists (P : TopPair.{0}) (n : ℕ)
    (c : Cohomology ℚ P.fst n) (hc : cohomologyMap ℚ n P.map c = 0) :
    ∃ d : RelativeCohomology ℚ P n, relativeCohomologyToAbsolute ℚ P n d = c := by
  have hS := cq_relative_cochain_shortExact P
  have hex := (ShortComplex.moduleCat_exact_iff _).mp (hS.homology_exact₂ n)
  exact hex c hc

theorem cq_surfaceProjection_prime_supported (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hY : TopologicalSpace.dim Y.left = 2) (I : HQ Y 4 ≃ₗ[ℚ] ℚ)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = 5) :
    ∃ c : RelativeCohomology ℚ
        (TopPair.ofSubset (X := TopCat.of (ComplexPoint A))
          ((cycleComponentAnalyticClosedSupport A ((fst A Y).left x) : Set (ComplexPoint A))ᶜ)) 6,
      relativeCohomologyToAbsolute ℚ _ 6 c =
        cupComparison A 6 (cq_surfaceProjection A Y hY I 6
          (cycleComponentSheafClass (A ⊗ Y) x hx)) := by
  apply cq_relative_absolute_exists
  have hc : cupComparison A 6 (cq_surfaceProjection A Y hY I 6
      (cycleComponentSheafClass (A ⊗ Y) x hx)) =
      cq_surfaceTrace (TopCat.of (ComplexPoint A)) Y hY I 6
        (cohomologyHomeomorphEquiv (HodgeLean.Foundations.complexPointProdHomeomorph A Y)
          10 (cupComparison (A ⊗ Y) 10
            (cycleComponentSheafClass (A ⊗ Y) x hx))) := by
    exact (cupComparison A 6).apply_symm_apply _
  change cohomologyMap ℚ 6
    (TopologicalSpace.Opens.inclusion' (X := TopCat.of (ComplexPoint A))
      (cycleComponentAnalyticClosedSupport A ((fst A Y).left x)).compl)
    (cupComparison A 6 (cq_surfaceProjection A Y hY I 6
      (cycleComponentSheafClass (A ⊗ Y) x hx))) = 0
  rw [hc, ← cq_surfaceTrace_naturality,
    cq_projection_component_restriction_zero A Y x hx, map_zero]

end HodgeLean.Foundations.Program
