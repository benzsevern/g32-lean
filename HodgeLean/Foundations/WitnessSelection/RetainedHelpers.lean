import HodgeLean.Foundations.WitnessSelection.GeometricProofs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.WitnessSelection

theorem normalization_transition_square
    {K : Type} [Field K] (X Y : Over (Spec ↧ℂ)) [IsProjective Y.hom]
    (f : Spec (CommRingCat.of K) ⟶ X.left) (g : Spec (CommRingCat.of K) ⟶ Y.left)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    (b : X ⟶ Y) (hf : f ≫ b.left = g)
    (w : s2b_normalizationOver X f ⟶ s2b_normalizationOver Y g)
    (hw : f.toNormalization ≫ w.left = g.toNormalization) :
    w ≫ s2b_normalizationMap Y g = s2b_normalizationMap X f ≫ b := by
  apply Over.OverMorphism.ext
  apply ext_of_isDominant_of_isSeparated (ι := f.toNormalization) Y.hom
  · simp only [Over.comp_left, Category.assoc, Over.w]
  · change f.toNormalization ≫ (w.left ≫ g.fromNormalization) =
      f.toNormalization ≫ (f.fromNormalization ≫ b.left)
    rw [← Category.assoc, hw, Scheme.Hom.toNormalization_fromNormalization,
      ← Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hf]

theorem tower_slice_equation {C : Type*} [Category C] {r : ℕ}
    (B : Fin (r + 1) → C) (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    {P : C} (ℓ : ∀ i, P ⟶ B i) (hℓ : ∀ i : Fin r, ℓ i.succ ≫ b i = ℓ i.castSucc) :
    ∀ i, ℓ i ≫ s2e_towerTotalMap B (𝟙 _) b i = ℓ 0 := by
  intro i
  induction i using Fin.induction with
  | zero => simp
  | succ j ih => rw [s2e_towerTotalMap_succ, ← Category.assoc, hℓ j, ih]

theorem tower_normalization_square
    {K : Type} [Field K] (r : ℕ) (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsProjective (B i).hom]
    (η : ∀ i, Spec (CommRingCat.of K) ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left = (η i.castSucc).toNormalization) :
    ∀ i, s2e_towerTotalMap (fun j => s2b_normalizationOver (B j) (η j)) (𝟙 _) w i ≫
      s2b_normalizationMap (B 0) (η 0) =
        s2b_normalizationMap (B i) (η i) ≫ s2e_towerTotalMap B (𝟙 _) b i := by
  intro i
  induction i using Fin.induction with
  | zero => simp
  | succ j ih =>
    rw [s2e_towerTotalMap_succ, s2e_towerTotalMap_succ, Category.assoc, ih,
      ← Category.assoc, normalization_transition_square _ _ _ _ (b j) (hη j) (w j) (hw j),
      Category.assoc]

end HodgeLean.WitnessSelection
