import HodgeLean.Foundations.GeometricIntegralityC
import HodgeLean.Foundations.SegreProjective
import HodgeLean.Foundations.Program.SchoenTransferE1BinaryCup
import HodgeLean.Foundations.Program.SchoenTransferE1PowerSource
import HodgeLean.Foundations.Program.SchoenTransferE1PowerCup
import HodgeLean.Foundations.Program.SchoenTransferE1KunnethComponents
import HodgeLean.Foundations.Program.SchoenTransferE1KunnethBase

/-! Iteration of the binary comparison on the specified ordered power maps. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct DirectSum BigOperators
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.decEq Classical.propDecidable

/-- One binary step applied to actual equivalences for the remaining power.
Source: Hatcher, Algebraic Topology, §3.2, iteration of field-coefficient Künneth. -/
def s4_e1_powerStepEquiv
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ)
    (e : ∀ n : ℕ,
      (⨁ d : {d : Fin h → ℕ // ∑ i, d i = n}, s4_e1_tensor Y h d.val) ≃ₗ[ℚ] HQ (g3_power Y h) n)
    (n : ℕ) :
    (⨁ d : {d : Fin (h + 1) → ℕ // ∑ i, d i = n}, s4_e1_tensor Y (h + 1) d.val) ≃ₗ[ℚ]
      HQ (g3_power Y (h + 1)) n :=
  (s4_e1_powerSourceEquiv Y h n).trans
    ((DirectSum.congrLinearEquiv fun p : {p : ℕ × ℕ // p.1 + p.2 = n} =>
      TensorProduct.congr (LinearEquiv.refl ℚ (HQ Y p.val.1)) (e p.val.2)).trans
        (s4_e1_binaryDegreeEquiv Y (g3_power Y h) n))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
/-- A pure summand of the binary step is the cup with the transported tail component.
Source: Hatcher, Algebraic Topology, §3.2, iteration of external cups. -/
theorem s4_e1_powerStepEquiv_lof
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ)
    (e : ∀ n : ℕ,
      (⨁ d : {d : Fin h → ℕ // ∑ i, d i = n}, s4_e1_tensor Y h d.val) ≃ₗ[ℚ] HQ (g3_power Y h) n)
    (n : ℕ) (d : {d : Fin (h + 1) → ℕ // ∑ i, d i = n})
    (x : HQ Y (d.val 0)) (y : s4_e1_tensor Y h (Fin.tail d.val)) :
    s4_e1_powerStepEquiv Y h e n (DirectSum.lof ℚ _ _ d (x ⊗ₜ[ℚ] y)) =
    (cupProductOf (g3_power Y (h + 1))).cup ((Fin.sum_univ_succ d.val).symm.trans d.property)
      (homPullback (CategoryTheory.CartesianMonoidalCategory.fst Y (g3_power Y h)) (d.val 0) x)
      (homPullback (CategoryTheory.CartesianMonoidalCategory.snd Y (g3_power Y h)) (∑ i, Fin.tail d.val i)
        (e (∑ i, Fin.tail d.val i)
        (DirectSum.lof ℚ _ _ ⟨Fin.tail d.val, rfl⟩ y))) := by
  simp only [s4_e1_powerStepEquiv, LinearEquiv.trans_apply]
  erw [s4_e1_powerSourceEquiv_lof]
  simp only [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
  erw [TensorProduct.congr_tmul]
  simp only [LinearEquiv.refl_apply]
  erw [s4_e1_binaryDegreeEquiv_tmul]
  dsimp only [s4_e1_multidegree_split, Equiv.coe_fn_mk]
  apply congrArg ((cupProductOf (g3_power Y (h + 1))).cup
    ((Fin.sum_univ_succ d.val).symm.trans d.property)
    (homPullback (CategoryTheory.CartesianMonoidalCategory.fst Y (g3_power Y h)) (d.val 0) x))
  apply congrArg (homPullback (CategoryTheory.CartesianMonoidalCategory.snd Y (g3_power Y h))
    (∑ i, Fin.tail d.val i))
  apply congrArg (e (∑ i, Fin.tail d.val i))
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
/-- Each successor component of the specified map satisfies the same binary recursion.
Source: Hatcher, Algebraic Topology, §3.2, ordered external cups. -/
theorem s4_e1_kunneth_succ_component
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ)
    (d : Fin (h + 1) → ℕ)
    (x : HQ Y (d 0)) (y : s4_e1_tensor Y h (Fin.tail d)) :
    s4_e1_kunneth Y (h + 1) (∑ i, d i) (DirectSum.lof ℚ _ _ ⟨d, rfl⟩ (x ⊗ₜ[ℚ] y)) =
    (cupProductOf (g3_power Y (h + 1))).cup (Fin.sum_univ_succ d).symm
      (homPullback (CategoryTheory.CartesianMonoidalCategory.fst Y (g3_power Y h)) (d 0) x)
      (homPullback (CategoryTheory.CartesianMonoidalCategory.snd Y (g3_power Y h)) (∑ i, Fin.tail d i)
        (s4_e1_kunneth Y h (∑ i, Fin.tail d i)
        (DirectSum.lof ℚ _ _ ⟨Fin.tail d, rfl⟩ y))) := by
  have ht : s4_e1_kunneth Y h (∑ i, Fin.tail d i)
      (DirectSum.lof ℚ _ _ ⟨Fin.tail d, rfl⟩ y) =
      s4_e1_orderedCup Y (g3_power Y h) h (Fin.tail d) (g3_proj Y h) y :=
    s4_e1_kunneth_component Y h _ ⟨Fin.tail d, rfl⟩ y
  have hf : s4_e1_kunneth Y (h + 1) (∑ i, d i)
      (DirectSum.lof ℚ _ _ ⟨d, rfl⟩ (x ⊗ₜ[ℚ] y)) =
      s4_e1_orderedCup Y (g3_power Y (h + 1)) (h + 1) d (g3_proj Y (h + 1))
        (x ⊗ₜ[ℚ] y) :=
    by
      let z : s4_e1_tensor Y (h + 1) d := x ⊗ₜ[ℚ] y
      have hz := s4_e1_kunneth_component Y (h + 1) (∑ i, d i) ⟨d, rfl⟩ z
      simpa only [HQ.castEquiv_apply_self, s4_e1_tensor, ModuleCat.of, z] using hz
  exact hf.trans ((s4_e1_powerCup_succ Y h d x y).trans
    (congrArg (fun z => (cupProductOf (g3_power Y (h + 1))).cup (Fin.sum_univ_succ d).symm
      (homPullback (CategoryTheory.CartesianMonoidalCategory.fst Y (g3_power Y h)) (d 0) x)
      (homPullback (CategoryTheory.CartesianMonoidalCategory.snd Y (g3_power Y h))
        (∑ i, Fin.tail d i) z)) ht.symm))

#print axioms s4_e1_powerStepEquiv
#print axioms s4_e1_powerStepEquiv_lof
#print axioms s4_e1_kunneth_succ_component
end HodgeLean.Foundations.Program
