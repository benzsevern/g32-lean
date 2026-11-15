import HodgeLean.Adapters.NormalConeB4aClassChartRegularity

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Analytic
open scoped Manifold ContDiff

/-- Holomorphic ambient chart coordinates pull back analytically to a smooth
source, without a smoothness assumption on the ambient scheme. -/
theorem a3b4a_gysin_smooth_source_chart_contMDiffOn
    (X Y : Over (Spec (CommRingCat.of ℂ))) (d n c : ℕ)
    [SmoothOfRelativeDimension d X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ) :
    ContMDiffOn 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, (Fin n → ℂ) × (Fin c → ℂ)) ω
      (fun x => Φ (Point.map f x)) (Point.map f ⁻¹' Φ.source) := by
  have hO : IsOpen (Point.map f ⁻¹' Φ.source) :=
    Φ.open_source.preimage (Point.continuous_map f)
  have hmap := f4_map_isHom f
  apply (contMDiffOn_prod_module_iff _).mpr
  constructor
  · apply contMDiffOn_pi_space.mpr
    intro j
    apply (f4_isHolFun_iff_contMDiffOn X d
      (fun x => (Φ (Point.map f x)).1 j) hO).mp
    exact hmap.2 Φ.source Φ.open_source (fun y => (Φ y).1 j) (hΦ.1 j)
  · apply contMDiffOn_pi_space.mpr
    intro j
    apply (f4_isHolFun_iff_contMDiffOn X d
      (fun x => (Φ (Point.map f x)).2 j) hO).mp
    exact hmap.2 Φ.source Φ.open_source (fun y => (Φ y).2 j) (hΦ.2 j)

end HodgeLean.Adapters
