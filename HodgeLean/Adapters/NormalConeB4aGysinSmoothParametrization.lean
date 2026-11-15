import HodgeLean.Adapters.NormalConeB4aGysinSmoothSourceChart

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff

/-- Ambient holomorphic coordinates of a smooth scheme source are analytic in
its intrinsic coordinate parametrizations, even for a singular ambient scheme. -/
theorem a3b4a_gysin_smooth_source_coordinate_parametrization
    (X Y : Over (Spec (CommRingCat.of ℂ))) (d n c : ℕ)
    [SmoothOfRelativeDimension d X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ) (x : ComplexPoint X) :
    AnalyticOnNhd ℂ (fun a => Φ (Point.map f ((chartAt (Fin d → ℂ) x).symm a)))
      ((chartAt (Fin d → ℂ) x).target ∩
        (chartAt (Fin d → ℂ) x).symm ⁻¹' (Point.map f ⁻¹' Φ.source)) := by
  let V := Point.map f ⁻¹' Φ.source
  have hV : IsOpen V := Φ.open_source.preimage (Point.continuous_map f)
  let e := chartAt (Fin d → ℂ) x
  have hW : IsOpen (e.target ∩ e.symm ⁻¹' V) := e.isOpen_inter_preimage_symm hV
  have hreg := a3b4a_gysin_smooth_source_chart_contMDiffOn X Y d n c f Φ hΦ
  have hinv : ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω
      e.symm e.target := contMDiffOn_chart_symm (I := 𝓘(ℂ, Fin d → ℂ)) (x := x)
  have hcomp := hreg.comp (hinv.mono (Set.inter_subset_left (t := e.symm ⁻¹' V)))
    (fun _ hw => hw.2)
  have hd := contMDiffOn_iff_contDiffOn.mp hcomp
  intro a ha
  exact (hd.contDiffAt (hW.mem_nhds ha)).analyticAt

end HodgeLean.Adapters
