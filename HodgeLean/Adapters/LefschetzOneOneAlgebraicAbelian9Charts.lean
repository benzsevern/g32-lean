import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian9ChartsProofs

/-! # Public comparison of analytic normal-chart germs

An implication from holomorphic transition data, usable on arbitrary topological chart
carriers, including local analytic covering charts. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular AlgebraicGeometry.ComplexPoint
open TopologicalSpace Set Topology
namespace HodgeLean.Adapters

/-- Holomorphic normal charts with holomorphic inverse transition give the same local coclass.
Source: `exists_open_chartNormalProjectionCoclass_eq` and
`supportRelativeCohomologyGerm_eq_of_restrict_eq`; the normal-chart argument in
`CycleClassSmoothChartsProofs.lean`. -/
theorem bh9_chart_germ
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
      (chartNormalProjectionCoclass E q d S hd d.source (le_refl _)) :=
  bh9_chart_germ_aux M E q e d S he hd a hae had haS ht hti

example :
    supportRelativeCohomologyGerm
      (TopCat.of ((Fin 1 → ℂ) × (Fin 1 → ℂ)))
      {y | y.2 = 0} 2 ⊤ 0 (by trivial)
      (chartNormalProjectionCoclass (Fin 1 → ℂ) 1
        (OpenPartialHomeomorph.refl _) {y | y.2 = 0}
        (fun _ _ ↦ Iff.rfl) ⊤ (by intro y _hy; trivial)) =
    supportRelativeCohomologyGerm
      (TopCat.of ((Fin 1 → ℂ) × (Fin 1 → ℂ)))
      {y | y.2 = 0} 2 ⊤ 0 (by trivial)
      (chartNormalProjectionCoclass (Fin 1 → ℂ) 1
        (OpenPartialHomeomorph.refl _) {y | y.2 = 0}
        (fun _ _ ↦ Iff.rfl) ⊤ (by intro y _hy; trivial)) := by
  exact bh9_chart_germ _ (Fin 1 → ℂ) 1
    (OpenPartialHomeomorph.refl _) (OpenPartialHomeomorph.refl _)
    {y | y.2 = 0} (fun _ _ ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl)
    0 (by trivial) (by trivial) rfl
    (by simpa using (analyticAt_id : AnalyticAt ℂ
      (fun x : (Fin 1 → ℂ) × (Fin 1 → ℂ) ↦ x) 0))
    (by simpa using (analyticAt_id : AnalyticAt ℂ
      (fun x : (Fin 1 → ℂ) × (Fin 1 → ℂ) ↦ x) 0))

end HodgeLean.Adapters
