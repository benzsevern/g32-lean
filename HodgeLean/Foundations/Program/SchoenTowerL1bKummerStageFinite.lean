import HodgeLean.Foundations.Program.SchoenTowerL1bKummerInitial
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerAction

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A dominant field point has a unique embedding compatible with its generic spectrum map. -/
theorem s2v_l1b_generic_field_embedding
    {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X]
    (η : Spec (.of K) ⟶ X) [IsDominant η] :
    ∃! κ : X.functionField ⟶ CommRingCat.of K,
      Spec.map κ ≫ X.fromSpecStalk (genericPoint X) = η := by
  refine ⟨Spec.preimage (s2_dominantFieldFactor η), ?_, ?_⟩
  · dsimp only
    rw [Spec.map_preimage]
    exact s2_dominantFieldFactor_comp η
  · intro κ hκ
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (genericPoint X))).mp
    rw [hκ, Spec.map_preimage, s2_dominantFieldFactor_comp]

/-- Finiteness at an earlier base persists for a compatible dominant field point. -/
theorem s2v_l1b_generic_field_embedding_finite
    {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f]
    (η : Spec (.of K) ⟶ X) [IsDominant η]
    (κ₀ : Y.functionField ⟶ CommRingCat.of K)
    (hκ₀ : Spec.map κ₀ ≫ Y.fromSpecStalk (genericPoint Y) = η ≫ f)
    (hfinite : letI := κ₀.hom.toAlgebra; Module.Finite Y.functionField K) :
    ∃ κ : X.functionField ⟶ CommRingCat.of K,
      Spec.map κ ≫ X.fromSpecStalk (genericPoint X) = η ∧
      (letI := κ.hom.toAlgebra; Module.Finite X.functionField K) := by
  obtain ⟨κ, hκ, _⟩ := s2v_l1b_generic_field_embedding X η
  have heq : s2v_l1b_functionFieldPullback f ≫ κ = κ₀ := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp
    rw [Spec.map_comp, Category.assoc,
      s2v_l1b_functionFieldPullback_generic_square, ← Category.assoc, hκ, hκ₀]
  refine ⟨κ, hκ, ?_⟩
  letI := κ₀.hom.toAlgebra
  letI := κ.hom.toAlgebra
  letI := (s2v_l1b_functionFieldPullback f).hom.toAlgebra
  haveI : IsScalarTower Y.functionField X.functionField K :=
    IsScalarTower.of_algebraMap_eq fun z =>
      (congrArg (fun g : Y.functionField ⟶ CommRingCat.of K => g z) heq).symm
  haveI : Module.Finite Y.functionField K := hfinite
  exact Module.Finite.of_restrictScalars_finite Y.functionField X.functionField K

/-- A retained tower of dominant field points inherits a finite embedding at every stage. -/
theorem s2v_l1b_tower_field_embeddings_finite
    {K : Type} [Field K] {r : ℕ} (B : Fin (r + 1) → Scheme.{0})
    [∀ i, IsIntegral (B i)]
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (η : ∀ i, Spec (.of K) ⟶ B i) [∀ i, IsDominant (η i)]
    (hη : ∀ i : Fin r, η i.succ ≫ b i = η i.castSucc)
    (κ₀ : (B 0).functionField ⟶ CommRingCat.of K)
    (hκ₀ : Spec.map κ₀ ≫ (B 0).fromSpecStalk (genericPoint (B 0)) = η 0)
    (hfinite : letI := κ₀.hom.toAlgebra; Module.Finite (B 0).functionField K) :
    ∀ i, ∃ κ : (B i).functionField ⟶ CommRingCat.of K,
      Spec.map κ ≫ (B i).fromSpecStalk (genericPoint (B i)) = η i ∧
      (letI := κ.hom.toAlgebra; Module.Finite (B i).functionField K) := by
  intro i
  induction i using Fin.induction with
  | zero => exact ⟨κ₀, hκ₀, hfinite⟩
  | succ i ih =>
    obtain ⟨κ, hκ, hfin⟩ := ih
    haveI : IsDominant (η i.succ ≫ b i) := by rw [hη]; infer_instance
    haveI : IsDominant (b i) := IsDominant.of_comp (η i.succ) (b i)
    exact s2v_l1b_generic_field_embedding_finite (b i) (η i.succ) κ
      (hκ.trans (hη i).symm) hfin

end HodgeLean.Foundations.Program
