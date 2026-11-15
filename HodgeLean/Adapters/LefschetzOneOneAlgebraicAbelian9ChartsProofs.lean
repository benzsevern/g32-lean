import HodgeLean.Adapters.CycleClassSmoothChartsProofs

noncomputable section
open CategoryTheory AlgebraicTopology.Singular AlgebraicGeometry.ComplexPoint
open TopologicalSpace Set Topology
namespace HodgeLean.Adapters

/-- Holomorphic normal charts with holomorphic inverse transition give the same local coclass.
Source: `exists_open_chartNormalProjectionCoclass_eq` and
`supportRelativeCohomologyGerm_eq_of_restrict_eq`; the normal-chart argument in
`CycleClassSmoothChartsProofs.lean`. -/
theorem bh9_chart_germ_aux
    (M E : Type) [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (q : ℕ) (e d : OpenPartialHomeomorph M (E × (Fin q → ℂ)))
    (S : Set M)
    (he : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hd : ∀ y ∈ d.source, y ∈ S ↔ (d y).2 = 0)
    (a : M) (hae : a ∈ e.source) (had : a ∈ d.source) (haS : a ∈ S)
    (ht : AnalyticAt ℂ (e.symm.trans d) (e a))
    (hti : AnalyticAt ℂ (e.symm.trans d).symm ((e.symm.trans d) (e a))) :
    supportRelativeCohomologyGerm (TopCat.of M) S (2 * q) ⟨e.source, e.open_source⟩ a hae
      (chartNormalProjectionCoclass E q e S he e.source (le_refl _)) =
    supportRelativeCohomologyGerm (TopCat.of M) S (2 * q) ⟨d.source, d.open_source⟩ a had
      (chartNormalProjectionCoclass E q d S hd d.source (le_refl _)) := by
  obtain ⟨W, hWe, hWd, haW, hW⟩ :=
    exists_open_chartNormalProjectionCoclass_eq q e d S he hd a hae
      ((he a hae).mp haS) had ht hti
  apply supportRelativeCohomologyGerm_eq_of_restrict_eq (TopCat.of M) S (2 * q)
    hWe hWd a haW
  exact (chartNormalProjectionCoclass_restrict E q e S he hWe (le_refl _)).trans
    (hW.trans (chartNormalProjectionCoclass_restrict E q d S hd hWd (le_refl _)).symm)

end HodgeLean.Adapters
