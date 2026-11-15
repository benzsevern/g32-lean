import HodgeLean.Foundations.Program.CompensationAssemblySingle

/-! # Proofs for compensation assembly -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 10000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Symplectic
open HodgeLean.Foundations
open HodgeLean.Foundations.HermitianForm HodgeLean.Papers ComplexConjugate
namespace HodgeLean.Foundations.Program

theorem cq_smooth_pullback_span_core {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) :
    (algebraicCycleClassSpan Z q).map (homPullback f (2 * q)) ≤
      algebraicCycleClassSpan X q := by
  classical
  apply Submodule.map_le_iff_le_comap.mpr
  rw [algebraicCycleClassSpan]
  refine sSup_le ?_
  rintro _ ⟨x, hx, rfl⟩
  apply (Submodule.span_singleton_le_iff_mem _ _).mpr
  change homPullback f (2 * q) (cycleComponentSheafClass Z x hx) ∈
    algebraicCycleClassSpan X q
  let c : AlgebraicCycle Z.left ℚ :=
    (Function.locallyFinsuppWithin.single x 1).restrict (Set.subset_univ _)
  have hc : ∀ z, c z ≠ 0 → Order.coheight z = q := by
    intro z hz
    by_cases he : z = x
    · simpa only [he] using hx
    · exfalso
      apply hz
      simp only [c, Function.locallyFinsuppWithin.restrict_apply, Set.mem_univ,
        ↓reduceIte, Function.locallyFinsuppWithin.single_apply, if_neg he]
  have he := ccm6_homPullback_cycleClass (X := X) (Z := Z) f q c hc
  have hclass : ccm3_cycleClass Z q c = cycleComponentSheafClass Z x hx := by
    simpa only [one_smul] using cq_cycle_single_eq (X := Z) q x hx 1
  have he' : homPullback f (2 * q) (cycleComponentSheafClass Z x hx) =
      ccm3_cycleClass X q (ccm3_flatPullback f.left c) :=
    (congrArg (homPullback f (2 * q)) hclass).symm.trans he
  exact he'.symm ▸ cq_cycleClass_mem_span X q _

end HodgeLean.Foundations.Program
