import HodgeLean.Foundations.Program.SchoenTransferE1Multidegrees
import Mathlib.LinearAlgebra.DirectSum.TensorProduct

/-! Distribution of graded tensor sources over total multidegrees. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped TensorProduct DirectSum BigOperators
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Reindex and distribute a first graded factor and a family of tail tensors.
Source: the universal properties of direct sums and tensor products. -/
def s4_e1_gradedSourceEquiv (h n : ℕ)
    (M : ℕ → Type*) (N : (Fin h → ℕ) → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℚ (M i)]
    [∀ d, AddCommGroup (N d)] [∀ d, Module ℚ (N d)] :
    (⨁ d : {d : Fin (h + 1) → ℕ // ∑ i, d i = n}, M (d.val 0) ⊗[ℚ] N (Fin.tail d.val)) ≃ₗ[ℚ]
    (⨁ p : {p : ℕ × ℕ // p.1 + p.2 = n}, M p.val.1 ⊗[ℚ]
      (⨁ d : {d : Fin h → ℕ // ∑ i, d i = p.val.2}, N d.val)) := by
  let A := fun p : {p : ℕ × ℕ // p.1 + p.2 = n} =>
    fun d : {d : Fin h → ℕ // ∑ i, d i = p.val.2} => M p.val.1 ⊗[ℚ] N d.val
  let e₁ := (DirectSum.lequivCongrLeft ℚ (M := fun x => A x.1 x.2)
    (s4_e1_multidegree_split h n).symm).symm
  let e₂ := DirectSum.sigmaLcurryEquiv ℚ (δ := A)
  let e₃ := DirectSum.congrLinearEquiv fun p : {p : ℕ × ℕ // p.1 + p.2 = n} =>
    (TensorProduct.directSumRight ℚ ℚ (M p.val.1)
      (fun d : {d : Fin h → ℕ // ∑ i, d i = p.val.2} => N d.val)).symm
  exact e₁.trans (e₂.trans e₃)

/-- The graded source equivalence evaluates a pure component tensor without changing its order.
Source: the coproduct inclusions and tensor distribution formulas. -/
theorem s4_e1_gradedSourceEquiv_lof (h n : ℕ)
    (M : ℕ → Type*) (N : (Fin h → ℕ) → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℚ (M i)]
    [∀ d, AddCommGroup (N d)] [∀ d, Module ℚ (N d)]
    (d : {d : Fin (h + 1) → ℕ // ∑ i, d i = n}) (x : M (d.val 0)) (y : N (Fin.tail d.val)) :
    s4_e1_gradedSourceEquiv h n M N (DirectSum.lof ℚ _ _ d (x ⊗ₜ[ℚ] y)) =
      DirectSum.lof ℚ _ _ ((s4_e1_multidegree_split h n d).1)
        (x ⊗ₜ[ℚ] DirectSum.lof ℚ _ _ ((s4_e1_multidegree_split h n d).2) y) := by
  let A := fun p : {p : ℕ × ℕ // p.1 + p.2 = n} =>
    fun d : {d : Fin h → ℕ // ∑ i, d i = p.val.2} => M p.val.1 ⊗[ℚ] N d.val
  change (DirectSum.congrLinearEquiv fun p : {p : ℕ × ℕ // p.1 + p.2 = n} =>
    (TensorProduct.directSumRight ℚ ℚ (M p.val.1)
      (fun d : {d : Fin h → ℕ // ∑ i, d i = p.val.2} => N d.val)).symm)
    ((DirectSum.sigmaLcurryEquiv ℚ (δ := A))
      ((DirectSum.lequivCongrLeft ℚ (M := fun z => A z.1 z.2)
        (s4_e1_multidegree_split h n).symm).symm
        (DirectSum.lof ℚ _ _ d (x ⊗ₜ[ℚ] y)))) = _
  erw [DirectSum.lequivCongrLeft_symm_lof]
  have hs : (DirectSum.sigmaLcurryEquiv ℚ (δ := fun p : {p : ℕ × ℕ // p.1 + p.2 = n} =>
      fun d : {d : Fin h → ℕ // ∑ i, d i = p.val.2} => M p.val.1 ⊗[ℚ] N d.val))
      (DirectSum.lof ℚ _ _ (s4_e1_multidegree_split h n d) (x ⊗ₜ[ℚ] y)) =
      DirectSum.lof ℚ _ _ ((s4_e1_multidegree_split h n d).1)
        (DirectSum.lof ℚ _ _ ((s4_e1_multidegree_split h n d).2) (x ⊗ₜ[ℚ] y)) := by
    exact DirectSum.sigmaCurry_of (δ := A) (s4_e1_multidegree_split h n d) (x ⊗ₜ[ℚ] y)
  erw [hs]
  simp only [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
  have ht := TensorProduct.directSumRight_symm_lof_tmul ℚ ℚ
    (M₁' := M (d.val 0))
    (M₂ := fun j : {j : Fin h → ℕ // ∑ i, j i = ∑ i, Fin.tail d.val i} => N j.val)
    x ⟨Fin.tail d.val, rfl⟩ y
  exact congrArg (DirectSum.lof ℚ {p : ℕ × ℕ // p.1 + p.2 = n}
    (fun p => M p.val.1 ⊗[ℚ] (⨁ j : {j : Fin h → ℕ // ∑ i, j i = p.val.2}, N j.val))
    ((s4_e1_multidegree_split h n d).1)) ht

#print axioms s4_e1_gradedSourceEquiv
#print axioms s4_e1_gradedSourceEquiv_lof
end HodgeLean.Foundations.Program
