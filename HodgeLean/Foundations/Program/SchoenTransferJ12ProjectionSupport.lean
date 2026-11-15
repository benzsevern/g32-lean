import HodgeLean.Foundations.Program.CompensationAssemblyProjectionLift
import HodgeLean.Foundations.Program.SchoenTransferJ12Projection
import HodgeLean.Foundations.Program.CompensationAssemblyProductSupport

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Singular
open AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupComparison cohomologyMap

/-- The projected prime class has support on the actual algebraic projection image.
Source: Fulton, Intersection Theory, §19.1, support of proper pushforward and cycle classes. -/
theorem s4_selected_projection_prime_supported
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d s q : ℕ) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (h : 2 * s = 2 * d + 2 * q)
    (x : (A ⊗ Y).left) (hx : Order.coheight x = s) :
    ∃ c : RelativeCohomology ℚ
        (TopPair.ofSubset (X := TopCat.of (ComplexPoint A))
          ((cycleComponentAnalyticClosedSupport A ((fst A Y).left x) :
            Set (ComplexPoint A))ᶜ)) (2 * q),
      relativeCohomologyToAbsolute ℚ _ (2 * q) c =
        cupComparison A (2 * q) (s4_selected_projection A Y d (2 * q) I
          (HQ.castEquiv (A ⊗ Y) h (cycleComponentSheafClass (A ⊗ Y) x hx))) := by
  have hfibre (p : ℕ) : Module.Finite ℚ
      (Cohomology ℚ (TopCat.of (ComplexPoint Y)) p) := by
    letI := (finbetti_finiteBetti Y).finite p
    exact Module.Finite.equiv (cupComparison Y p)
  let T := TopCat.of (ComplexPoint A)
  let Z := TopCat.of (ComplexPoint Y)
  let S := cycleComponentAnalyticClosedSupport A ((fst A Y).left x)
  let U := TopCat.of S.compl
  let i : U ⟶ T := TopologicalSpace.Opens.inclusion' (X := T) S.compl
  let c₀ := cohomologyHomeomorphEquiv (complexPointProdHomeomorph A Y)
    (2 * d + 2 * q) (cupComparison (A ⊗ Y) (2 * d + 2 * q)
      (HQ.castEquiv (A ⊗ Y) h (cycleComponentSheafClass (A ⊗ Y) x hx)))
  apply cq_relative_absolute_exists
  change cohomologyMap ℚ (2 * q) i
    (cupComparison A (2 * q) (s4_selected_projection A Y d (2 * q) I
      (HQ.castEquiv (A ⊗ Y) h (cycleComponentSheafClass (A ⊗ Y) x hx)))) = 0
  rw [s4_selected_projection_comparison A Y d (2 * q) I hfibre]
  change cohomologyMap ℚ (2 * q) i
    (s4_selected_fibre_trace T Z hfibre (2 * d) (2 * q)
      ((cupComparison Y (2 * d)).symm.trans I) c₀) = 0
  rw [← s4_selected_fibre_trace_naturality Z U T i hfibre (2 * d) (2 * q)
    ((cupComparison Y (2 * d)).symm.trans I) c₀]
  have hz : cohomologyMap ℚ (2 * d + 2 * q)
      (s4_selected_product_map i (𝟙 Z)) c₀ = 0 := by
    have hc (r : ℕ) (hr : 2 * s = r) : cohomologyMap ℚ r
        (s4_selected_product_map i (𝟙 Z))
        (cohomologyHomeomorphEquiv (complexPointProdHomeomorph A Y) r
          (cupComparison (A ⊗ Y) r
            (HQ.castEquiv (A ⊗ Y) hr (cycleComponentSheafClass (A ⊗ Y) x hx)))) = 0 := by
      subst r
      change cohomologyMap ℚ (2 * s) (cq_fibreProductMap i Z)
        (cohomologyHomeomorphEquiv (complexPointProdHomeomorph A Y) (2 * s)
          (cupComparison (A ⊗ Y) (2 * s) (cycleComponentSheafClass (A ⊗ Y) x hx))) = 0
      exact cq_projection_component_restriction_zero A Y x hx
    exact hc _ h
  rw [hz, map_zero]

#print axioms s4_selected_projection_prime_supported

end HodgeLean.Foundations.Program
