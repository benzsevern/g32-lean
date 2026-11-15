import HodgeLean.Adapters.NormalConeB4aGysinSmoothParametrization
import HodgeLean.Adapters.NormalConeB4aGysinCountableCharts

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Analytic

/-- The coordinate image of a smooth scheme source inside an ambient chart is
covered exactly by countably many of its intrinsic coordinate parametrizations. -/
theorem a3b4a_gysin_smooth_source_countable_image_cover
    (X Y : Over (Spec (CommRingCat.of ℂ))) (d n c : ℕ)
    [SmoothOfRelativeDimension d X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ))) :
    ∃ J : Set (ComplexPoint X), J.Countable ∧
      (fun y => Φ (Point.map f y)) '' (Point.map f ⁻¹' Φ.source) =
        ⋃ x ∈ J, (fun a => Φ (Point.map f ((chartAt (Fin d → ℂ) x).symm a))) ''
          ((chartAt (Fin d → ℂ) x).target ∩
            (chartAt (Fin d → ℂ) x).symm ⁻¹' (Point.map f ⁻¹' Φ.source)) := by
  letI : SecondCountableTopology (ComplexPoint X) := f4_secondCountable X
  let V := Point.map f ⁻¹' Φ.source
  have hV : IsOpen V := Φ.open_source.preimage (Point.continuous_map f)
  obtain ⟨J, hJ, _, hcover⟩ := a3b4a_gysin_countable_restricted_chart_cover
    (H := Fin d → ℂ) V hV
  refine ⟨J, hJ, Set.Subset.antisymm ?_ ?_⟩
  · rintro p ⟨y, hy, rfl⟩
    have hycover : y ∈ ⋃ z ∈ J, ((chartAt (Fin d → ℂ) z).restrOpen V hV).source :=
      hcover ▸ hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp hycover
    let e := chartAt (Fin d → ℂ) z
    apply Set.mem_iUnion₂.mpr
    refine ⟨z, hz, e y, ⟨e.map_source hyz.1, ?_⟩, ?_⟩
    · change e.symm (e y) ∈ V
      rwa [e.left_inv hyz.1]
    · change Φ (Point.map f (e.symm (e y))) = Φ (Point.map f y)
      rw [e.left_inv hyz.1]
  · intro p hp
    obtain ⟨z, _, a, ha, rfl⟩ := Set.mem_iUnion₂.mp hp
    exact ⟨(chartAt (Fin d → ℂ) z).symm a, ha.2, rfl⟩

end HodgeLean.Adapters
