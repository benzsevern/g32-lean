import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDefs

/-! # Inverses of transported point charts

A chart transported from an open source retains its coordinate target and
its actual inverse at every coordinate point of the original chart.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace AlgebraicGeometry.SingularCycles

theorem transported_point_chart_inverse
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N] (j : M → N) (d : ℕ)
    (e : OpenPartialHomeomorph M ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (E : OpenPartialHomeomorph N ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (hsource : E.source = j '' e.source) (hvalue : ∀ y, E (j y) = e y)
    (v : Fin d → ℂ) (hv : v ∈ (pointChart e).target) :
    v ∈ (pointChart E).target ∧ (pointChart E).symm v = j ((pointChart e).symm v) := by
  let y := (pointChart e).symm v
  have hy : y ∈ (pointChart e).source := (pointChart e).map_target hv
  have hjy : j y ∈ E.source := hsource.symm ▸ Set.mem_image_of_mem j hy.1
  have hjy' : j y ∈ (pointChart E).source := ⟨hjy, by trivial⟩
  have hcoord : pointChart E (j y) = v := by
    change (E (j y)).2 = v
    rw [hvalue y]
    exact (pointChart e).right_inv hv
  refine ⟨hcoord ▸ (pointChart E).map_source hjy', ?_⟩
  exact (congrArg (pointChart E).symm hcoord.symm).trans ((pointChart E).left_inv hjy')

end AlgebraicGeometry.SingularCycles
