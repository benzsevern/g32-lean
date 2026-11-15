import HodgeLean.Adapters.NormalConeB4aClassHolomorphicCharts

/-! # Analytic regularity of normal charts

Route: the ambient manifold chart is analytic. The inverse normal coordinate
map is analytic by the inverse function theorem, and the final identification
of the normal kernel with a complex coordinate space is complex linear.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry
open scoped Manifold ContDiff

/-- The standard flattening chart for a smooth closed immersion is analytic
at its center as a map from the complex-point manifold. -/
theorem a3b4a_classStandardFlatteningChart_contMDiffAt
    (X Y : Over (Spec (CommRingCat.of ℂ))) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y) :
    ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, (Fin m → ℂ) × (Fin (d - m) → ℂ)) ω
      (ComplexPoint.closedImmersionStandardFlatteningChart X Y i m d z) (Point.map i z) := by
  let p := Point.map i z
  let eX := ComplexPoint.localChart X d p
  let eN := ComplexPoint.closedImmersionNormalChart X Y i m d z
  let L := (ContinuousLinearEquiv.refl ℂ (Fin m → ℂ)).prodCongr
    (ComplexPoint.closedImmersionNormalKernelEquiv X Y i m d z)
  have hX : ContMDiffAt 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) ω eX p :=
    (contMDiffOn_chart (I := 𝓘(ℂ, Fin d → ℂ)) (n := ω) (x := p)).contMDiffAt
      (eX.open_source.mem_nhds (ComplexPoint.mem_localChart_source X d p))
  have hN : ContMDiffAt 𝓘(ℂ, Fin d → ℂ)
      𝓘(ℂ, (Fin m → ℂ) × (ComplexPoint.closedImmersionDerivativeProjection X Y i m d z).ker)
      ω eN.symm (eX p) :=
    (ComplexPoint.analyticAt_closedImmersionNormalChart_symm X Y i m d z).contDiffAt.contMDiffAt
  change ContMDiffAt 𝓘(ℂ, Fin d → ℂ)
    𝓘(ℂ, (Fin m → ℂ) × (Fin (d - m) → ℂ)) ω (L ∘ eN.symm ∘ eX) p
  exact L.toContinuousLinearMap.contMDiffAt.comp p (hN.comp p hX)

/-- A smooth closed immersion between fixed-dimensional complex schemes has
flattening charts satisfying the frozen F4 holomorphic predicate. -/
theorem a3b4a_classSmoothClosedImmersion_exists_holomorphic_flattening
    (X Y : Over (Spec (CommRingCat.of ℂ))) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y) :
    ∃ e : OpenPartialHomeomorph (ComplexPoint X) ((Fin m → ℂ) × (Fin (d - m) → ℂ)),
      Point.map i z ∈ e.source ∧ a3b4_IsHolChart X.hom e ∧
      ∀ y ∈ e.source, y ∈ Set.range (Point.map i) ↔ (e y).2 = 0 := by
  let e := ComplexPoint.closedImmersionStandardFlatteningChart X Y i m d z
  have hp : Point.map i z ∈ e.source :=
    ComplexPoint.closedImmersionStandardFlatteningChart_mem_source X Y i m d z
  obtain ⟨W, hWo, hpW, hhol⟩ := a3b4a_classLocal_exists_holomorphic_restriction
    X d m (d - m) e (Point.map i z) hp
      (a3b4a_classStandardFlatteningChart_contMDiffAt X Y i m d z)
  refine ⟨e.restrOpen W hWo, ⟨hp, hpW⟩, hhol, ?_⟩
  intro y hy
  exact ComplexPoint.closedImmersionStandardFlatteningChart_mem_range_iff X Y i m d z y hy.1

end HodgeLean.Adapters
