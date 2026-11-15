import HodgeLean.Foundations.Program.SchoenTowerL1bKummerStageFinite

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The original finite quotient square and the retained Cartier tower give finite field embeddings at every stage. -/
theorem s2v_l1b_original_tower_finite_embeddings
    {Y Z W B₀ : Over (Spec ↧ℂ)} [IsIntegral W.left]
    [IsIntegral B₀.left] [LocallyOfFiniteType B₀.hom]
    (p : Y ⟶ Z) (hp : Function.Surjective (Point.map p)) (n : ℕ)
    (q : g3_power Y n ⟶ W) (γ : g3_power Z n ⟶ B₀)
    (hγ : Function.Surjective (Point.map γ)) (β : W ⟶ B₀) [IsFinite β.left]
    (hβ : q ≫ β = s2_powerMap p n ≫ γ)
    {r : ℕ} (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsIntegral (B i).left] (e₀ : B 0 ≅ B₀)
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (I : ∀ i : Fin r, (B i.castSucc).left.IdealSheafData)
    (hcartier : ∀ (i : Fin r) (x : (B i.succ).left),
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((I i).comap (b i).left).ideal U) ≃ₗ[Γ((B i.succ).left, U)]
          Γ((B i.succ).left, U)))
    (huniv : ∀ (i : Fin r) (T : Over (Spec ↧ℂ)) (f : T ⟶ B i.castSucc),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((I i).comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B i.succ, u ≫ b i = f)
    (η : ∀ i, Spec W.left.functionField ⟶ (B i).left)
    (hη₀ : η 0 ≫ e₀.hom.left = W.left.fromSpecStalk (genericPoint W.left) ≫ β.left)
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc) :
    ∀ i, ∃ κ : (B i).left.functionField ⟶ W.left.functionField,
      Spec.map κ ≫ (B i).left.fromSpecStalk (genericPoint (B i).left) = η i ∧
      (letI := κ.hom.toAlgebra; Module.Finite (B i).left.functionField W.left.functionField) := by
  haveI : ∀ i, IsDominant (η i) :=
    s2v_l1b_original_tower_generic_dominant p hp n q γ hγ β hβ B e₀ b I
      hcartier huniv η hη₀ hη
  obtain ⟨κ₀, _, hκ₀, hfin⟩ :=
    s2v_l1b_original_finite_field_embedding p hp n q γ hγ β hβ
  obtain ⟨κ, hκ, hfinite⟩ := s2v_l1b_generic_field_embedding_finite e₀.hom.left
    (η 0) κ₀ (hκ₀.trans hη₀.symm) hfin
  exact s2v_l1b_tower_field_embeddings_finite (fun i => (B i).left)
    (fun i => (b i).left) η hη κ hκ hfinite

end HodgeLean.Foundations.Program
