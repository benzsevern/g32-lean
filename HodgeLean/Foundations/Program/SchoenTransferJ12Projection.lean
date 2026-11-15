import HodgeLean.Foundations.Program.SchoenTransferE1Binary
import HodgeLean.Foundations.Program.CycleFoundationsDefs
import HodgeLean.Foundations.Program.SchoenTransferJ12FibreTraceNaturality

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
open HodgeLean.Foundations.Singular AlgebraicTopology.Singular
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupComparison

/-- Integration along the actual smooth projective fibre through its finite cohomology decomposition.
Source: Fulton, Intersection Theory, §19.1; Hatcher, Algebraic Topology, §3.2. -/
def s4_selected_projection
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d n : ℕ) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ) :
    HQ (A ⊗ Y) (2 * d + n) →ₗ[ℚ] HQ A n := by
  have hfibre (p : ℕ) : Module.Finite ℚ
      (Cohomology ℚ (TopCat.of (ComplexPoint Y)) p) := by
    letI := (finbetti_finiteBetti Y).finite p
    exact Module.Finite.equiv (cupComparison Y p)
  let integral := (cupComparison Y (2 * d)).symm.trans I
  exact (cupComparison A n).symm.toLinearMap ∘ₗ
    s4_selected_fibre_trace (TopCat.of (ComplexPoint A))
      (TopCat.of (ComplexPoint Y)) hfibre (2 * d) n integral ∘ₗ
    (cohomologyHomeomorphEquiv (complexPointProdHomeomorph A Y)
      (2 * d + n)).toLinearMap ∘ₗ
    (cupComparison (A ⊗ Y) (2 * d + n)).toLinearMap

/-- The algebraic cohomology projection is the specified finite-fibre contraction under comparison.
Source: Fulton, Intersection Theory, §19.1, comparison with topological integration. -/
theorem s4_selected_projection_comparison
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (d n : ℕ) (I : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (hfibre : ∀ p : ℕ, Module.Finite ℚ
      (Cohomology ℚ (TopCat.of (ComplexPoint Y)) p))
    (x : HQ (A ⊗ Y) (2 * d + n)) :
    cupComparison A n (s4_selected_projection A Y d n I x) =
      s4_selected_fibre_trace (TopCat.of (ComplexPoint A))
        (TopCat.of (ComplexPoint Y)) hfibre (2 * d) n
        ((cupComparison Y (2 * d)).symm.trans I)
        (cohomologyHomeomorphEquiv (complexPointProdHomeomorph A Y)
          (2 * d + n) (cupComparison (A ⊗ Y) (2 * d + n) x)) := by
  simp only [s4_selected_projection, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]

#print axioms s4_selected_projection_comparison

end HodgeLean.Foundations.Program
