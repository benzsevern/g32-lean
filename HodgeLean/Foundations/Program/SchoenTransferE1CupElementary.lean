import HodgeLean.Foundations.Program.SchoenTransferE1OrderedTensor

/-! Compatibility of the indexed and recursively ordered degree-one cup maps. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

/-- The total degree of h degree-one factors is h. -/
theorem s4_e1_sum_one (h : ℕ) : (∑ _ : Fin h, (1 : ℕ)) = h := by simp

/-- Degree transport in the right input preserves the actual cup product.
Source: Hatcher, Algebraic Topology, §3.2, the graded cup product. -/
theorem s4_e1_cup_cast_right
    (T : Over (Spec ↧ℂ)) [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    {i j j' k : ℕ} (hj : j = j') (h : i + j = k) (h' : i + j' = k)
    (a : HQ T i) (b : HQ T j) :
    (cupProductOf T).cup h a b =
      (cupProductOf T).cup h' a (HQ.castEquiv T hj b) := by
  subst j'
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 400000 in
/-- One step of the ordered cup evaluates a tensor by the binary cup product.
Source: Hatcher, Algebraic Topology, §3.2, the ordered external cup product. -/
theorem s4_e1_orderedCup_tmul
    (Y T : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (h : ℕ) (d : Fin (h + 1) → ℕ) (f : Fin (h + 1) → (T ⟶ Y))
    (x : HQ Y (d 0)) (y : s4_e1_tensor Y h (Fin.tail d)) :
    s4_e1_orderedCup Y T (h + 1) d f (show HQ Y (d 0) ⊗[ℚ] s4_e1_tensor Y h (Fin.tail d) from x ⊗ₜ[ℚ] y) =
      (cupProductOf T).cup (i := d 0) (j := ∑ i, Fin.tail d i) (k := ∑ i, d i)
        (show d 0 + (∑ i, Fin.tail d i) = (∑ i, d i) from (Fin.sum_univ_succ d).symm)
        (homPullback (f 0) (d 0) x)
        (s4_e1_orderedCup Y T h (Fin.tail d) (Fin.tail f) y) := rfl


#print axioms s4_e1_sum_one
#print axioms s4_e1_cup_cast_right
#print axioms s4_e1_orderedCup_tmul
end HodgeLean.Foundations.Program
