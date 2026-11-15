import HodgeLean.Foundations.Program.SchoenTransferE1Defs

/-! Ordered and indexed tensor constructions for the degree-one summand. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped TensorProduct
open HodgeLean.RealDefs

namespace HodgeLean.Foundations.Program

/-- Separate the first coordinate from the remaining ordered coordinates.
Source: Mathlib `Fin.cases`, the decomposition of a finite ordinal. -/
def s4_e1_consIndex (h : ℕ) : Unit ⊕ Fin h ≃ Fin (h + 1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl Unit.unit) Sum.inr
  left_inv x := by cases x with
    | inl x => cases x; rfl
    | inr x => rfl
  right_inv i := by cases i using Fin.cases <;> rfl

/-- The actual recursive tensor in degree one is the indexed tensor product.
Source: Hatcher, Algebraic Topology, §3.2, associativity and the unit of tensor products. -/
def s4_e1_oneTensorEquiv
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] :
    (h : ℕ) → s4_e1_tensor Y h (fun _ => 1) ≃ₗ[ℚ]
      (⨂[ℚ] _ : Fin h, HQ Y 1)
  | 0 => by
      change ℚ ≃ₗ[ℚ] (⨂[ℚ] _ : Fin 0, HQ Y 1)
      exact (PiTensorProduct.isEmptyEquiv (R := ℚ) (s := fun _ : Fin 0 => HQ Y 1) (Fin 0)).symm
  | h + 1 => by
      change (HQ Y 1 ⊗[ℚ] s4_e1_tensor Y h (fun _ => 1)) ≃ₗ[ℚ] _
      exact (TensorProduct.congr
        (PiTensorProduct.subsingletonEquiv (R := ℚ)
          (s := fun _ : Unit => HQ Y 1) Unit.unit).symm
        (s4_e1_oneTensorEquiv Y h)).trans
          ((PiTensorProduct.tmulEquiv ℚ (HQ Y 1)).trans
            (PiTensorProduct.reindex ℚ (fun _ : Unit ⊕ Fin h => HQ Y 1)
              (s4_e1_consIndex h)))

set_option backward.isDefEq.respectTransparency false in
/-- The ordered equivalence preserves the first factor and the tail on pure tensors.
Source: Hatcher, Algebraic Topology, §3.2, associativity of tensor products. -/
theorem s4_e1_oneTensorEquiv_tmul
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) (v : Fin (h + 1) → HQ Y 1) :
    s4_e1_oneTensorEquiv Y (h + 1)
      (v 0 ⊗ₜ[ℚ] (s4_e1_oneTensorEquiv Y h).symm
        (PiTensorProduct.tprod ℚ (Fin.tail v))) = PiTensorProduct.tprod ℚ v := by
  change PiTensorProduct.reindex ℚ (fun _ : Unit ⊕ Fin h => HQ Y 1)
    (s4_e1_consIndex h)
      (PiTensorProduct.tmulEquiv ℚ (HQ Y 1)
        ((PiTensorProduct.subsingletonEquiv (R := ℚ)
          (s := fun _ : Unit => HQ Y 1) Unit.unit).symm (v 0) ⊗ₜ[ℚ]
          (s4_e1_oneTensorEquiv Y h) ((s4_e1_oneTensorEquiv Y h).symm
            (PiTensorProduct.tprod ℚ (Fin.tail v))))) = PiTensorProduct.tprod ℚ v
  simp only [LinearEquiv.apply_symm_apply,
    PiTensorProduct.subsingletonEquiv_symm_apply', PiTensorProduct.tmulEquiv_apply,
    PiTensorProduct.reindex_tprod]
  congr 1
  funext i
  cases i using Fin.cases <;> rfl

/-- The inverse tensor equivalence separates a pure tensor into its first factor
and its ordered tail.
Source: Hatcher, Algebraic Topology, §3.2, associativity of tensor products. -/
theorem s4_e1_oneTensorEquiv_symm_tprod
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (h : ℕ) (v : Fin (h + 1) → HQ Y 1) :
    (s4_e1_oneTensorEquiv Y (h + 1)).symm (PiTensorProduct.tprod ℚ v) =
      v 0 ⊗ₜ[ℚ] (s4_e1_oneTensorEquiv Y h).symm
        (PiTensorProduct.tprod ℚ (Fin.tail v)) := by
  exact (LinearEquiv.symm_apply_eq _).mpr (s4_e1_oneTensorEquiv_tmul Y h v).symm

#print axioms s4_e1_consIndex
#print axioms s4_e1_oneTensorEquiv
#print axioms s4_e1_oneTensorEquiv_tmul
#print axioms s4_e1_oneTensorEquiv_symm_tprod
end HodgeLean.Foundations.Program
