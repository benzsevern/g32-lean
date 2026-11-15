import HodgeLean.Foundations.Program.SchoenTowerL1bKummerStageDegree

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The retained Cartier tower transports cyclic Galois degree from the actual original base field. -/
theorem s2v_l1b_original_tower_cyclic_degree
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
    ∀ (κ₀ : B₀.left.functionField ⟶ W.left.functionField),
    Spec.map κ₀ ≫ B₀.left.fromSpecStalk (genericPoint B₀.left) =
      W.left.fromSpecStalk (genericPoint W.left) ≫ β.left →
    ∀ m : ℕ,
    (letI := κ₀.hom.toAlgebra;
      Module.Finite B₀.left.functionField W.left.functionField ∧
      IsGalois B₀.left.functionField W.left.functionField ∧
      IsCyclic (W.left.functionField ≃ₐ[B₀.left.functionField] W.left.functionField) ∧
      Module.finrank B₀.left.functionField W.left.functionField = m) →
    ∀ i, ∃ κ : (B i).left.functionField ⟶ W.left.functionField,
      Spec.map κ ≫ (B i).left.fromSpecStalk (genericPoint (B i).left) = η i ∧
      (letI := κ.hom.toAlgebra;
        Module.Finite (B i).left.functionField W.left.functionField ∧
        IsGalois (B i).left.functionField W.left.functionField ∧
        IsCyclic (W.left.functionField ≃ₐ[(B i).left.functionField] W.left.functionField) ∧
        Module.finrank (B i).left.functionField W.left.functionField = m) := by
  intro κ₀ hκ₀ m hdata
  haveI : ∀ i, IsDominant (η i) :=
    s2v_l1b_original_tower_generic_dominant p hp n q γ hγ β hβ B e₀ b I
      hcartier huniv η hη₀ hη
  have he : zmtiso_IsBirational e₀.hom.left :=
    ⟨s2_dominant_genericPoint e₀.hom.left, inferInstance⟩
  obtain ⟨κ, hκ, hfin, hgal, hcyc, hdeg⟩ :=
    s2v_l1b_generic_field_embedding_cyclic_degree e₀.hom.left he
      (η 0) κ₀ (hκ₀.trans hη₀.symm) hdata.1 hdata.2.1 hdata.2.2.1
  have hb : ∀ j, zmtiso_IsBirational (b j).left := fun j =>
    s2v_l1b_retained_cartier_birational _ _ (b j) (I j) (hcartier j) (huniv j)
  exact s2v_l1b_tower_field_embeddings_cyclic_degree (fun i => (B i).left)
    (fun i => (b i).left) hb η hη κ hκ m
      ⟨hfin, hgal, hcyc, hdeg.trans hdata.2.2.2⟩

end HodgeLean.Foundations.Program
