import HodgeLean.Foundations.QuotientDuality.ProperCycleDerivedSupportChainClass

/-! # Original coefficient-forgetting and negative-degree homology coordinates -/

noncomputable section
open CategoryTheory HomologicalComplex
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified original chain coordinates through coefficient forgetting and negative regrading.
Source: HomologicalComplex.extendHomologyIso; ShortComplex.mapHomologyIso.
-/
def retainedChainHomologyCoordinates (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    ((((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.down ℕ)).obj K).extend
      ComplexShape.embeddingDownNat).homology (-(n : ℤ)) ≅
    (forget₂ (ModuleCat ℚ) AddCommGrpCat).obj (K.homology n) :=
  (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.down ℕ)).obj K).extendHomologyIso
    ComplexShape.embeddingDownNat
      (show ComplexShape.embeddingDownNat.f n = -(n : ℤ) from rfl) ≪≫
        (K.sc n).mapHomologyIso (forget₂ (ModuleCat ℚ) AddCommGrpCat)

/-- The original negative-degree chain coordinates commute with every actual chain map. -/
lemma retained_chain_homology_coordinates_naturality
    {K L : ChainComplex (ModuleCat ℚ) ℕ} (f : K ⟶ L) (n : ℕ) :
    (forget₂ (ModuleCat ℚ) AddCommGrpCat).map (HomologicalComplex.homologyMap f n) ≫
      (retainedChainHomologyCoordinates L n).inv =
    (retainedChainHomologyCoordinates K n).inv ≫
      HomologicalComplex.homologyMap (extendMap
        (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.down ℕ)).map f)
          ComplexShape.embeddingDownNat) (-(n : ℤ)) := by
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let G := F.mapHomologicalComplex (.down ℕ)
  let eK := (G.obj K).extendHomologyIso ComplexShape.embeddingDownNat
    (show ComplexShape.embeddingDownNat.f n = -(n : ℤ) from rfl)
  let eL := (G.obj L).extendHomologyIso ComplexShape.embeddingDownNat
    (show ComplexShape.embeddingDownNat.f n = -(n : ℤ) from rfl)
  have h0 := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.down ℕ) n).map f) F
  change F.map (HomologicalComplex.homologyMap f n) ≫ ((L.sc n).mapHomologyIso F).inv =
    ((K.sc n).mapHomologyIso F).inv ≫ HomologicalComplex.homologyMap (G.map f) n at h0
  have h1 : eK.inv ≫ HomologicalComplex.homologyMap
      (extendMap (G.map f) ComplexShape.embeddingDownNat) (-(n : ℤ)) =
      HomologicalComplex.homologyMap (G.map f) n ≫ eL.inv := by
    apply (cancel_mono eL.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [HomologicalComplex.extendHomologyIso_hom_naturality,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change F.map (HomologicalComplex.homologyMap f n) ≫
      ((L.sc n).mapHomologyIso F).inv ≫ eL.inv =
    (((K.sc n).mapHomologyIso F).inv ≫ eK.inv) ≫ _
  rw [← Category.assoc, h0, Category.assoc, ← h1, ← Category.assoc]

end HodgeLean.Foundations.QuotientDuality
