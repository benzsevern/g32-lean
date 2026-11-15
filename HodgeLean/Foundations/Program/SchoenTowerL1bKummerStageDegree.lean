import HodgeLean.Foundations.Program.SchoenTowerL1bKummerStageFinite
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerDegree
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerBirationalField

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Compatible generic embeddings preserve cyclic Galois degree along a birational base map. -/
theorem s2v_l1b_generic_field_embedding_cyclic_degree
    {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (hf : zmtiso_IsBirational f)
    (η : Spec (.of K) ⟶ X) [IsDominant η]
    (κ₀ : Y.functionField ⟶ CommRingCat.of K)
    (hκ₀ : Spec.map κ₀ ≫ Y.fromSpecStalk (genericPoint Y) = η ≫ f)
    (hfinite : letI := κ₀.hom.toAlgebra; Module.Finite Y.functionField K)
    (hgal : letI := κ₀.hom.toAlgebra; IsGalois Y.functionField K)
    (hcyc : letI := κ₀.hom.toAlgebra; IsCyclic (K ≃ₐ[Y.functionField] K)) :
    ∃ κ : X.functionField ⟶ CommRingCat.of K,
      Spec.map κ ≫ X.fromSpecStalk (genericPoint X) = η ∧
      (letI := κ.hom.toAlgebra
       Module.Finite X.functionField K ∧ IsGalois X.functionField K ∧
       IsCyclic (K ≃ₐ[X.functionField] K) ∧
       Module.finrank X.functionField K =
         @Module.finrank Y.functionField K _ _ κ₀.hom.toAlgebra.toModule) := by
  obtain ⟨κ, hκ, _⟩ := s2v_l1b_generic_field_embedding X η
  have heq : s2v_l1b_functionFieldPullback f ≫ κ = κ₀ := by
    apply Spec.map_injective
    apply (cancel_mono (Y.fromSpecStalk (genericPoint Y))).mp
    rw [Spec.map_comp, Category.assoc,
      s2v_l1b_functionFieldPullback_generic_square, ← Category.assoc, hκ, hκ₀]
  letI := κ₀.hom.toAlgebra
  letI := κ.hom.toAlgebra
  letI := (s2v_l1b_functionFieldPullback f).hom.toAlgebra
  haveI : IsScalarTower Y.functionField X.functionField K :=
    IsScalarTower.of_algebraMap_eq fun z =>
      (congrArg (fun g : Y.functionField ⟶ CommRingCat.of K => g z) heq).symm
  haveI : Module.Finite Y.functionField K := hfinite
  haveI : IsGalois Y.functionField K := hgal
  haveI : IsCyclic (K ≃ₐ[Y.functionField] K) := hcyc
  haveI := s2v_l1b_birational_functionFieldPullback_isIso f hf
  have hbase : Module.finrank Y.functionField X.functionField = 1 :=
    Module.finrank_of_bijective_algebraMap
      (asIso (s2v_l1b_functionFieldPullback f)).commRingCatIsoToRingEquiv.bijective
  exact ⟨κ, hκ, s2v_l1b_cyclic_degree_tower Y.functionField X.functionField K hbase⟩

/-- A tower of birational base maps preserves cyclic Galois data for its specified generic points. -/
theorem s2v_l1b_tower_field_embeddings_cyclic_degree
    {K : Type} [Field K] {r : ℕ} (B : Fin (r + 1) → Scheme.{0})
    [∀ i, IsIntegral (B i)]
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (hb : ∀ i, zmtiso_IsBirational (b i))
    (η : ∀ i, Spec (.of K) ⟶ B i) [∀ i, IsDominant (η i)]
    (hη : ∀ i : Fin r, η i.succ ≫ b i = η i.castSucc)
    (κ₀ : (B 0).functionField ⟶ CommRingCat.of K)
    (hκ₀ : Spec.map κ₀ ≫ (B 0).fromSpecStalk (genericPoint (B 0)) = η 0)
    (m : ℕ)
    (hdata : letI := κ₀.hom.toAlgebra
      Module.Finite (B 0).functionField K ∧ IsGalois (B 0).functionField K ∧
      IsCyclic (K ≃ₐ[(B 0).functionField] K) ∧ Module.finrank (B 0).functionField K = m) :
    ∀ i, ∃ κ : (B i).functionField ⟶ CommRingCat.of K,
      Spec.map κ ≫ (B i).fromSpecStalk (genericPoint (B i)) = η i ∧
      (letI := κ.hom.toAlgebra
       Module.Finite (B i).functionField K ∧ IsGalois (B i).functionField K ∧
       IsCyclic (K ≃ₐ[(B i).functionField] K) ∧ Module.finrank (B i).functionField K = m) := by
  intro i
  induction i using Fin.induction with
  | zero => exact ⟨κ₀, hκ₀, hdata⟩
  | succ i ih =>
    obtain ⟨κ, hκ, hfin, hgal, hcyc, hdeg⟩ := ih
    haveI : IsDominant (η i.succ ≫ b i) := by rw [hη]; infer_instance
    haveI : IsDominant (b i) := IsDominant.of_comp (η i.succ) (b i)
    obtain ⟨κ', hκ', hfin', hgal', hcyc', hdeg'⟩ :=
      s2v_l1b_generic_field_embedding_cyclic_degree (b i) (hb i) (η i.succ) κ
        (hκ.trans (hη i).symm) hfin hgal hcyc
    exact ⟨κ', hκ', hfin', hgal', hcyc', hdeg'.trans hdeg⟩

end HodgeLean.Foundations.Program
