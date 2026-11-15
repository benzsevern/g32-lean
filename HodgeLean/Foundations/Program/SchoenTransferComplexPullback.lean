import HodgeLean.Foundations.Program.SchoenTransferComplexCup

noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Pullback commutes with the actual complex bilinear cup product.
Source: Hatcher, Algebraic Topology, §3.2, naturality of cup products. -/
theorem s4_complex_pullback_cup
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : Z ⟶ X) {p q r : ℕ} (h : p + q = r)
    (x : ℂ ⊗[ℚ] HQ X p) (y : ℂ ⊗[ℚ] HQ X q) :
    (homPullback f r).baseChange ℂ ((cupProductOf X).cupC h x y) =
      (cupProductOf Z).cupC h ((homPullback f p).baseChange ℂ x)
        ((homPullback f q).baseChange ℂ y) := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul z x =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | tmul w y =>
      simp only [CupProduct.cupC_tmul, LinearMap.baseChange_tmul, spec_homPullback_cup]

/-- Pullback commutes with the full complex iterated degree-one cup product.
Source: Hatcher, Algebraic Topology, §3.2, naturality and the unit. -/
theorem s4_complex_pullback_cupMulti
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : Z ⟶ X) : ∀ (h : ℕ) (v : Fin h → ℂ ⊗[ℚ] HQ X 1),
    (homPullback f h).baseChange ℂ ((cupProductOf X).cupMultiC h v) =
      (cupProductOf Z).cupMultiC h (fun i => (homPullback f 1).baseChange ℂ (v i))
  | 0, v => by
      change (homPullback f 0).baseChange ℂ ((1 : ℂ) ⊗ₜ[ℚ] (cupUnit X)) =
        (1 : ℂ) ⊗ₜ[ℚ] (cupUnit Z)
      rw [LinearMap.baseChange_tmul, spec_homPullback_unit]
  | h + 1, v => by
      rw [CupProduct.cupMultiC_succ, CupProduct.cupMultiC_succ,
        s4_complex_pullback_cup, s4_complex_pullback_cupMulti f h (Fin.tail v)]
      rfl

end HodgeLean.Foundations.Program
