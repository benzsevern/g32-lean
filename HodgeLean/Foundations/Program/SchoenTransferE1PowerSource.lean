import HodgeLean.Foundations.Program.SchoenTransferE1Defs
import HodgeLean.Foundations.Program.SchoenTransferE1Multidegrees
import HodgeLean.Foundations.Program.SchoenTransferE1SourceAlgebra

/-! Reindexing and tensor distribution for the recursive power source. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct DirectSum BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Grouping total multidegrees by the first coordinate gives a binary tensor source.
Source: Hatcher, Algebraic Topology, §3.2, iteration of the Künneth formula. -/
def s4_e1_powerSourceEquiv
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h n : ℕ) :
    (⨁ d : {d : Fin (h + 1) → ℕ // ∑ i, d i = n}, s4_e1_tensor Y (h + 1) d.val) ≃ₗ[ℚ]
      (⨁ p : {p : ℕ × ℕ // p.1 + p.2 = n}, HQ Y p.val.1 ⊗[ℚ]
        (⨁ d : {d : Fin h → ℕ // ∑ i, d i = p.val.2}, s4_e1_tensor Y h d.val)) :=
  s4_e1_gradedSourceEquiv h n (HQ Y) (fun d => s4_e1_tensor Y h d)

/-- The grouped source equivalence preserves the actual first-factor pure tensor.
Source: the coproduct inclusions and tensor distribution universal properties. -/
theorem s4_e1_powerSourceEquiv_lof
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h n : ℕ) (d : {d : Fin (h + 1) → ℕ // ∑ i, d i = n})
    (x : HQ Y (d.val 0)) (y : s4_e1_tensor Y h (Fin.tail d.val)) :
    s4_e1_powerSourceEquiv Y h n (DirectSum.lof ℚ _ _ d (x ⊗ₜ[ℚ] y)) =
      DirectSum.lof ℚ _ _ ((s4_e1_multidegree_split h n d).1)
        (x ⊗ₜ[ℚ] DirectSum.lof ℚ _ _ ((s4_e1_multidegree_split h n d).2) y) :=
  s4_e1_gradedSourceEquiv_lof h n (HQ Y) (fun d => s4_e1_tensor Y h d) d x y

#print axioms s4_e1_powerSourceEquiv_lof
#print axioms s4_e1_powerSourceEquiv
end HodgeLean.Foundations.Program
