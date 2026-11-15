import HodgeLean.Foundations.QuotientDuality.PersistenceMarkedChartModel
import HodgeLean.Foundations.QuotientDuality.PersistenceBooleanModel

/-! Actual fixed neighbourhood deformations inside compact marked chart carriers. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HodgeLean.Foundations.ComplexTopology
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_marked_chart_truncation_neighbourhood
    {X : Type} [TopologicalSpace X] {s : ℕ} {D : Fin s → Set X}
    (c : Marked.SubsetChart X D) (j : Fin s)
    (a : EuclideanSpace ℝ (Fin (c.n + c.n))) (r : ℝ) (hr : 0 ≤ r) :
    let V : Set c.domain := {x | complexEuclideanCoordinates c.n (c.coordinates x).val ∈
      Metric.closedBall a r}
    let A : Set V := {x | x.val.val ∈ D j}
    ∃ (W : Set V), IsOpen W ∧ ∃ (hAW : A ⊆ W)
      (q : TopCat.of W ⟶ TopCat.of A),
      persistenceSubsetNeighbourhoodInclusion A W hAW ≫ q = 𝟙 (TopCat.of A) ∧
      ∃ H : TopCat.Homotopy (𝟙 (TopCat.of W))
        (q ≫ persistenceSubsetNeighbourhoodInclusion A W hAW),
        ∀ (t : unitInterval) (x : A),
          H (t, persistenceSubsetNeighbourhoodInclusion A W hAW x) =
            persistenceSubsetNeighbourhoodInclusion A W hAW x := by
  obtain ⟨f, b, hf, hb, e, hmark⟩ :=
    persistence_marked_chart_truncation_model c j a r hr
  exact persistence_boolean_model_neighbourhood_deformation _ f b hf hb e hmark

end HodgeLean.Foundations.QuotientDuality
