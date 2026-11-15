import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects

/-! # Lifting morphisms from finite sums of the negative native line -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Lifts from the actual negative line assemble into lifts from every
finite sum, including the literal zero-rank free endpoint. -/
theorem paired_c3_negative_sum_hom_lift (k : ℕ)
    {M N : (pairedC3Proj k).Modules} (g : M ⟶ N)
    (h : Function.Surjective (fun v : pairedC3NegativeLine k ⟶ M => v ≫ g))
    (b : ℕ) (u : pairedC3SplitBundle k 0 b ⟶ N) :
    ∃ v : pairedC3SplitBundle k 0 b ⟶ M, v ≫ g = u := by
  induction b with
  | zero =>
    refine ⟨0, ?_⟩
    apply (SheafOfModules.freeHomEquiv _ (I := Fin 0)).injective
    funext j
    exact Fin.elim0 j
  | succ b ih =>
    obtain ⟨v₁, hv₁⟩ := ih (biprod.inl ≫ u)
    obtain ⟨v₂, hv₂⟩ := h (biprod.inr ≫ u)
    refine ⟨biprod.desc v₁ v₂, ?_⟩
    apply biprod.hom_ext'
    · rw [← Category.assoc, biprod.inl_desc]
      exact hv₁
    · rw [← Category.assoc, biprod.inr_desc]
      exact hv₂

/-- The identity of the original negative-sum quotient lifts once all
morphisms from the actual negative line lift through its projection. -/
theorem paired_c3_negative_sum_section (k b : ℕ)
    {M N : (pairedC3Proj k).Modules} (g : M ⟶ N)
    (e : N ≅ pairedC3SplitBundle k 0 b)
    (h : Function.Surjective (fun v : pairedC3NegativeLine k ⟶ M => v ≫ g)) :
    ∃ s : N ⟶ M, s ≫ g = 𝟙 _ := by
  obtain ⟨v, hv⟩ := paired_c3_negative_sum_hom_lift k g h b e.inv
  refine ⟨e.hom ≫ v, ?_⟩
  rw [Category.assoc, hv, e.hom_inv_id]

#print axioms paired_c3_negative_sum_hom_lift
#print axioms paired_c3_negative_sum_section
end HodgeLean.Foundations.Program.G32Native
