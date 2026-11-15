import HodgeLean.Foundations.WitnessSelection.RetainedHelpers
import HodgeLean.Foundations.Program.SchoenTransferOrbitSupport

/-! # Retained maps in the R2 support assembly

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.WitnessSelection
namespace HodgeLean.Foundations.Program

/-- The recursively specified maps in the S2 existential are its literal tower maps.
Source: Schoen (1988), Lemma 2.6, p. 18.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_retained_tower_map
    {C : Type*} [Category C] {r : ℕ} (X : Fin (r + 1) → C)
    (Y : C) (e : X 0 ⟶ Y) (w : ∀ i : Fin r, X i.succ ⟶ X i.castSucc)
    (f : ∀ i, X i ⟶ Y) (hf0 : f 0 = e)
    (hfs : ∀ i : Fin r, f i.succ = w i ≫ f i.castSucc) :
    ∀ i, f i = s2e_towerTotalMap X e w i := by
  intro i
  induction i using Fin.induction with
  | zero => exact hf0
  | succ j ih => rw [hfs, ih, s2e_towerTotalMap_succ]

/-- The S2 component projection retains its original-base equation after the tower.
Source: Schoen (1988), Lemma 2.6, p. 18.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_component_projection
    {K : Type} [Field K] (r : ℕ) (B : Fin (r + 1) → Over (Spec ↧ℂ))
    [∀ i, IsProjective (B i).hom]
    (η : ∀ i, Spec (CommRingCat.of K) ⟶ (B i).left)
    [∀ i, QuasiCompact (η i)] [∀ i, QuasiSeparated (η i)]
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (hη : ∀ i : Fin r, η i.succ ≫ (b i).left = η i.castSucc)
    (w : ∀ i : Fin r, s2b_normalizationOver (B i.succ) (η i.succ) ⟶
      s2b_normalizationOver (B i.castSucc) (η i.castSucc))
    (hw : ∀ i : Fin r, (η i.succ).toNormalization ≫ (w i).left =
      (η i.castSucc).toNormalization)
    (W₀ B₀ W Q PP : Over (Spec ↧ℂ))
    (e₀ : B 0 ≅ B₀) (eW : s2b_normalizationOver (B 0) (η 0) ≅ W₀)
    (β₀ : W₀ ⟶ B₀)
    (heW : eW.hom ≫ β₀ = s2b_normalizationMap (B 0) (η 0) ≫ e₀.hom)
    (eWr : s2b_normalizationOver (B (Fin.last r)) (η (Fin.last r)) ≅ W)
    (f : ∀ i, s2b_normalizationOver (B i) (η i) ⟶ W₀)
    (hf0 : f 0 = eW.hom) (hfs : ∀ i : Fin r, f i.succ = w i ≫ f i.castSucc)
    (π : Q ⟶ PP) (ℓ : PP ⟶ B (Fin.last r)) (ι : Q ⟶ W)
    (hcomponent : ι ≫ eWr.inv ≫ s2b_normalizationMap (B (Fin.last r))
      (η (Fin.last r)) = π ≫ ℓ) :
    ι ≫ (eWr.inv ≫ f (Fin.last r)) ≫ β₀ =
      π ≫ ℓ ≫ s2e_towerTotalMap B e₀.hom b (Fin.last r) := by
  have hf := s4_assembly_retained_tower_map
    (fun i => s2b_normalizationOver (B i) (η i)) W₀ eW.hom w f hf0 hfs
  have hmap : ∀ i, s2e_towerTotalMap
      (fun j => s2b_normalizationOver (B j) (η j)) eW.hom w i ≫ β₀ =
      s2b_normalizationMap (B i) (η i) ≫ s2e_towerTotalMap B e₀.hom b i := by
    intro i
    induction i using Fin.induction with
    | zero => exact heW
    | succ j ih =>
      rw [s2e_towerTotalMap_succ, s2e_towerTotalMap_succ, Category.assoc, ih,
        ← Category.assoc, normalization_transition_square _ _ _ _ (b j) (hη j) (w j) (hw j),
        Category.assoc]
  rw [hf, Category.assoc, hmap]
  simpa only [Category.assoc] using congrArg
    (fun g : Q ⟶ B (Fin.last r) => g ≫ s2e_towerTotalMap B e₀.hom b (Fin.last r))
    hcomponent

end HodgeLean.Foundations.Program
