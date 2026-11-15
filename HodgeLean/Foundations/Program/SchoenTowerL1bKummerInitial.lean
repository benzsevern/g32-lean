import HodgeLean.Foundations.Program.SchoenTowerL1bKummerDominance
import HodgeLean.Foundations.Program.SchoenTowerN1bcHelpers
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerFinite

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The original quotient square supplies dominance of its retained initial generic map. -/
theorem s2v_l1b_initial_generic_dominant
    {Y Z W B₀ B : Over (Spec ↧ℂ)} [IsIntegral W.left]
    [LocallyOfFiniteType B₀.hom]
    (p : Y ⟶ Z) (hp : Function.Surjective (Point.map p)) (n : ℕ)
    (q : g3_power Y n ⟶ W) (γ : g3_power Z n ⟶ B₀)
    (hγ : Function.Surjective (Point.map γ)) (β : W ⟶ B₀)
    (hβ : q ≫ β = s2_powerMap p n ≫ γ) (e₀ : B ≅ B₀)
    (η : Spec W.left.functionField ⟶ B.left)
    (hη : η ≫ e₀.hom.left = W.left.fromSpecStalk (genericPoint W.left) ≫ β.left) :
    IsDominant η := by
  haveI : IsDominant β.left := n1bc_dominant_of_points_surjective β
    (n1bc_originalCover_points_surjective p hp n q γ hγ β hβ)
  haveI : IsDominant (W.left.fromSpecStalk (genericPoint W.left)) :=
    s2_genericPointMorphism_dominant W.left
  haveI : IsDominant (η ≫ e₀.hom.left) := by
    rw [hη]
    infer_instance
  haveI : IsDominant ((η ≫ e₀.hom.left) ≫ e₀.inv.left) := inferInstance
  simpa only [Category.assoc, ← Over.comp_left, Iso.hom_inv_id,
    Over.id_left, Category.comp_id] using this

/-- The actual quotient square and the retained Cartier tower make every specified generic map dominant. -/
theorem s2v_l1b_original_tower_generic_dominant
    {Y Z W B₀ : Over (Spec ↧ℂ)} [IsIntegral W.left]
    [LocallyOfFiniteType B₀.hom]
    (p : Y ⟶ Z) (hp : Function.Surjective (Point.map p)) (n : ℕ)
    (q : g3_power Y n ⟶ W) (γ : g3_power Z n ⟶ B₀)
    (hγ : Function.Surjective (Point.map γ)) (β : W ⟶ B₀)
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
    ∀ i, IsDominant (η i) := by
  haveI : IsDominant (η 0) :=
    s2v_l1b_initial_generic_dominant p hp n q γ hγ β hβ e₀ (η 0) hη₀
  exact s2v_l1b_retained_tower_dominant B b I hcartier huniv η hη

/-- The original finite quotient square supplies a finite field embedding with its actual generic spectrum square. -/
theorem s2v_l1b_original_finite_field_embedding
    {Y Z W B₀ : Over (Spec ↧ℂ)} [IsIntegral W.left] [IsIntegral B₀.left]
    [LocallyOfFiniteType B₀.hom]
    (p : Y ⟶ Z) (hp : Function.Surjective (Point.map p)) (n : ℕ)
    (q : g3_power Y n ⟶ W) (γ : g3_power Z n ⟶ B₀)
    (hγ : Function.Surjective (Point.map γ)) (β : W ⟶ B₀) [IsFinite β.left]
    (hβ : q ≫ β = s2_powerMap p n ≫ γ) :
    ∃ κ : B₀.left.functionField ⟶ W.left.functionField,
      Function.Injective κ.hom ∧
      Spec.map κ ≫ B₀.left.fromSpecStalk (genericPoint B₀.left) =
        W.left.fromSpecStalk (genericPoint W.left) ≫ β.left ∧
      (letI := κ.hom.toAlgebra
       Module.Finite B₀.left.functionField W.left.functionField) := by
  haveI : IsDominant β.left := n1bc_dominant_of_points_surjective β
    (n1bc_originalCover_points_surjective p hp n q γ hγ β hβ)
  refine ⟨s2v_l1b_functionFieldPullback β.left, ?_, ?_, ?_⟩
  · exact (s2v_l1b_functionFieldPullback β.left).hom.injective
  · exact s2v_l1b_functionFieldPullback_generic_square β.left
  · exact s2v_l1b_functionFieldPullback_finite β.left

end HodgeLean.Foundations.Program
