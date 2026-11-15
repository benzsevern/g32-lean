import HodgeLean.Foundations.Program.CompensationAssemblyMembership

/-! # Proofs for compensation assembly -/

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Symplectic
open HodgeLean.Foundations
open HodgeLean.Foundations.HermitianForm HodgeLean.Papers ComplexConjugate
namespace HodgeLean.Foundations.Program

theorem cq_cycle_single_eq {X : Over (Spec ↧ℂ)}
    [DecidableEq X.left]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (x : X.left) (hx : Order.coheight x = q) (a : ℚ) :
    ccm3_cycleClass X q
        ((Function.locallyFinsuppWithin.single x a).restrict (Set.subset_univ _)) =
      a • (cycleComponentSheafClass X x hx : HQ X (2 * q)) := by
  classical
  unfold ccm3_cycleClass
  change (∑ᶠ z : {z : X.left // Order.coheight z = q},
    ((Function.locallyFinsuppWithin.single x a).restrict (Set.subset_univ _)) z.1 •
      (cycleComponentSheafClass X z.1 z.2 : HQ X (2 * q))) = _
  rw [finsum_eq_single _ ⟨x, hx⟩ (fun z hz ↦ by
    simp only [Function.locallyFinsuppWithin.restrict_apply,
      Set.mem_univ, ↓reduceIte, Function.locallyFinsuppWithin.single_apply]
    rw [if_neg]
    · exact zero_smul _ _
    · intro hzx
      exact hz (Subtype.ext hzx))]
  simp only [Function.locallyFinsuppWithin.restrict_apply,
    Set.mem_univ, Function.locallyFinsuppWithin.single_apply, ↓reduceIte]

end HodgeLean.Foundations.Program
