import HodgeLean.Foundations.Program.SchoenTransferDefs
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
/-! Implication from the explicit curve, coordinate action and primitive-kernel data
to the ordered Künneth and equal-character interfaces.
Determinant transport, rational comparison and algebraic cycles belong to later units.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct DirectSum BigOperators CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program
/-- Ordered tensor factors for a multidegree, with the empty tensor equal to the field.
Source: Hatcher, Algebraic Topology, §3.2, Künneth over a field. -/
def s4_e1_tensor (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] :
    (h : ℕ) → (Fin h → ℕ) → ModuleCat ℚ
  | 0, _ => ModuleCat.of ℚ ℚ
  | h + 1, d => ModuleCat.of ℚ (HQ Y (d 0) ⊗[ℚ] s4_e1_tensor Y h (Fin.tail d))

example (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] :
    s4_e1_tensor Y 0 Fin.elim0 = ModuleCat.of ℚ ℚ := rfl

/-- Ordered coordinate cup product in every multidegree on a specified source.
Source: Hatcher, Algebraic Topology, §3.2, external cup product. -/
def s4_e1_orderedCup (Y T : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom] :
    (h : ℕ) → (d : Fin h → ℕ) → (Fin h → (T ⟶ Y)) →
      s4_e1_tensor Y h d →ₗ[ℚ] HQ T (∑ i, d i)
  | 0, _, _ => by
      dsimp only [s4_e1_tensor]
      simp only [Fin.sum_univ_zero]
      exact LinearMap.toSpanSingleton ℚ (HQ T 0) (unitClass T)
  | h + 1, d, f =>
      TensorProduct.lift (((cupProductOf T).cup (show d 0 + (∑ i, Fin.tail d i) = (∑ i, d i) from (Fin.sum_univ_succ d).symm)).compl₁₂
        (homPullback (f 0) (d 0))
        (s4_e1_orderedCup Y T h (Fin.tail d) (Fin.tail f)))

example (Y T : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (h : ℕ) (d : Fin h → ℕ) (f : Fin h → (T ⟶ Y)) :
    s4_e1_orderedCup Y T h d f 0 = 0 := map_zero _

/-- The total degree-n Künneth map, with the actual ordered projection cup maps.
Source: Hatcher, Algebraic Topology, §3.2, Künneth over a field. -/
def s4_e1_kunneth (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] (h n : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] :
    (⨁ d : {d : Fin h → ℕ // ∑ i, d i = n}, s4_e1_tensor Y h d.val) →ₗ[ℚ]
      HQ (g3_power Y h) n :=
  DirectSum.toModule ℚ _ _ (fun d : {d : Fin h → ℕ // ∑ i, d i = n} => by
    have f := s4_e1_orderedCup Y (g3_power Y h) h d.val (g3_proj Y h)
    rw [d.property] at f
    exact f)

example (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h n : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] : s4_e1_kunneth Y h n 0 = 0 := map_zero _

/-- The all-degree-one coordinate cup map, linearized on the ordered tensor product.
Source: Schoen (1988), Lemmas 1.1–1.2; Hatcher, Algebraic Topology, §3.2. -/
def s4_e1_oneCup (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] (h : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] :
    (⨂[ℚ] i : Fin h, HQ Y 1) →ₗ[ℚ] HQ (g3_power Y h) h :=
  PiTensorProduct.lift (((cupProductOf (g3_power Y h)).cupMulti h).compLinearMap
    (fun i => homPullback (g3_proj Y h i) 1))

example (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom] : s4_e1_oneCup Y h 0 = 0 := map_zero _

end HodgeLean.Foundations.Program
