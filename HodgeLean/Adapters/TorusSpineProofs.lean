import HodgeLean.Adapters.TorusCohomologyChecks

/-! # Proof obligations for the torus-spine frozen spec

This file isolates the three statements left for a proving run. The general torus spine is
already established by `torusCohomology_cupProductOf`, `finiteBetti_abelian`,
`vanishingAboveTop_abelian`, and `finrank_HQ_abelian`.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Singular

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

theorem torusSpine_abelianTorusComparison_cupWedgeMap_aux (m : ℕ) :
    (abelianTorusComparison X m).toLinearMap ∘ₗ (cupProductOf X).cupWedgeMap m =
      HodgeLean.Foundations.Singular.cupWedgeMap
          (TopCat.of (UnitAddTorus (Fin (2 * dim X.left)))) m ∘ₗ
        exteriorPower.map m (abelianTorusComparison X 1).toLinearMap := by
  let e := complexPointTorusHomeomorph X (dim X.left)
  let E (k : ℕ) := cohomologyHomeomorphEquiv e k
  have hE := HodgeLean.Foundations.Singular.cohomologyMap_cupWedgeMap
    (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩) m
  change (E m).toLinearMap ∘ₗ (cupComparison X m).toLinearMap ∘ₗ
      (cupProductOf X).cupWedgeMap m = _
  rw [cupComparison_cupWedgeMap]
  change (E m).toLinearMap ∘ₗ
      HodgeLean.Foundations.Singular.cupWedgeMap (TopCat.of (ComplexPoint X)) m ∘ₗ _ = _
  rw [show (E m).toLinearMap =
    AlgebraicTopology.Singular.cohomologyMap ℚ m
      (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩) by rfl]
  rw [← LinearMap.comp_assoc]
  rw [hE]
  rw [LinearMap.comp_assoc, ← exteriorPower.map_comp]
  rfl

theorem torusSpine_bettiRanks_g1_aux (hg : dim X.left = 1) :
    Module.finrank ℚ (HQ X 0) = 1 ∧
      Module.finrank ℚ (HQ X 1) = 2 ∧
      Module.finrank ℚ (HQ X 2) = 1 := by
  constructor
  · rw [finrank_HQ_abelian, hg]
    decide
  constructor
  · rw [finrank_HQ_abelian, hg]
    norm_num
  · rw [finrank_HQ_abelian, hg]
    norm_num

theorem torusSpine_bettiRanks_g2_aux (hg : dim X.left = 2) :
    Module.finrank ℚ (HQ X 0) = 1 ∧
      Module.finrank ℚ (HQ X 1) = 4 ∧
      Module.finrank ℚ (HQ X 2) = 6 ∧
      Module.finrank ℚ (HQ X 3) = 4 ∧
      Module.finrank ℚ (HQ X 4) = 1 := by
  constructor
  · rw [finrank_HQ_abelian, hg]
    decide
  constructor
  · rw [finrank_HQ_abelian, hg]
    decide
  constructor
  · rw [finrank_HQ_abelian, hg]
    decide
  constructor
  · rw [finrank_HQ_abelian, hg]
    decide
  · rw [finrank_HQ_abelian, hg]
    norm_num

end HodgeLean.Adapters
