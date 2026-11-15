import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDefs
import HodgeLean.Adapters.NormalConeB4aGysinBridge2OpenCharts

/-! # Analytic coordinate expressions for the finite-map calculation

Morphisms from a smooth complex scheme are analytic when read in the
supplied holomorphic charts.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem map_in_holomorphic_point_charts_analytic
    {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [Smooth X.hom] (f : X ⟶ Z) (d : ℕ)
    (eX : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (eZ : OpenPartialHomeomorph (ComplexPoint Z) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (heX : a3b4_IsHolChart X.hom eX) (heZ : a3b4_IsHolChart Z.hom eZ)
    (v : (Fin 0 → ℂ) × (Fin d → ℂ)) (hv : v ∈ eX.target)
    (hvZ : Point.map f (eX.symm v) ∈ eZ.source) :
    AnalyticAt ℂ (fun w => (eZ (Point.map f (eX.symm w))).2) v := by
  rw [analyticAt_pi_iff]
  intro j
  exact a3b4g_holFun_comp_chart_analytic X Z f eX heX eZ.source eZ.open_source
    (fun z => (eZ z).2 j) (heZ.2 j) v hv hvZ

theorem map_in_pointChart_analytic
    {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [Smooth X.hom] (f : X ⟶ Z) (d : ℕ)
    (eX : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (eZ : OpenPartialHomeomorph (ComplexPoint Z) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (heX : a3b4_IsHolChart X.hom eX) (heZ : a3b4_IsHolChart Z.hom eZ)
    (v : Fin d → ℂ) (hv : v ∈ (pointChart eX).target)
    (hvZ : Point.map f ((pointChart eX).symm v) ∈ eZ.source) :
    AnalyticAt ℂ
      (fun w => pointChart eZ (Point.map f ((pointChart eX).symm w))) v := by
  have hinv : ∀ w, (pointChart eX).symm w = eX.symm ((0 : Fin 0 → ℂ), w) := by
    intro w
    change eX.symm ((Homeomorph.uniqueProd (Fin 0 → ℂ) (Fin d → ℂ)).symm w) = _
    apply congrArg eX.symm
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have hsrc : (pointChart eX).symm v ∈ eX.source :=
    ((pointChart eX).map_target hv).1
  have heq : eX ((pointChart eX).symm v) = ((0 : Fin 0 → ℂ), v) :=
    Prod.ext (Subsingleton.elim _ _) ((pointChart eX).right_inv hv)
  have htarget : ((0 : Fin 0 → ℂ), v) ∈ eX.target :=
    heq ▸ eX.map_source hsrc
  have hZ : Point.map f (eX.symm ((0 : Fin 0 → ℂ), v)) ∈ eZ.source := by
    rwa [← hinv]
  have h := map_in_holomorphic_point_charts_analytic f d eX eZ heX heZ
    ((0 : Fin 0 → ℂ), v) htarget hZ
  have hi : AnalyticAt ℂ (fun w : Fin d → ℂ => ((0 : Fin 0 → ℂ), w)) v :=
    analyticAt_const.prod analyticAt_id
  change AnalyticAt ℂ (fun w => (eZ (Point.map f ((pointChart eX).symm w))).2) v
  simpa only [Function.comp_def, ← hinv] using h.comp hi

end AlgebraicGeometry.SingularCycles
