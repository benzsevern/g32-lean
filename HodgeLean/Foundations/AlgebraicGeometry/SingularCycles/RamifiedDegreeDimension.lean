import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeAnalytic
import HodgeLean.Adapters.NormalConeB4aClassChartDimension
import HodgeLean.Adapters.NormalConeB4aClassChartRegularity

/-! # Dimension detected by a holomorphic point chart

A nonempty holomorphic point chart on a fixed-dimensional smooth complex
scheme has the same complex dimension as the scheme.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters
open scoped Manifold ContDiff
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem smooth_dimension_eq_point_chart_dimension
    (X : Over (Spec ↧ℂ)) (m d : ℕ)
    [SmoothOfRelativeDimension m X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (x : ComplexPoint X) (hx : x ∈ (pointChart e).source) :
    m = d := by
  let l := chartAt (Fin m → ℂ) x
  let e' := pointChart e
  have hC : ContMDiffOn 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin d → ℂ) ω e' e'.source :=
    ((ContinuousLinearMap.snd ℂ (Fin 0 → ℂ) (Fin d → ℂ)).contMDiff.comp_contMDiffOn
      (a3b4a_classHolomorphicChart_contMDiffOn X m 0 d e he)).mono (fun _ h => h.1)
  let t := l.symm.trans e'
  have ht : AnalyticOnNhd ℂ t t.source := by
    intro z hz
    have hL : ContMDiffAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin m → ℂ) ω l.symm z :=
      (contMDiffOn_chart_symm (I := 𝓘(ℂ, Fin m → ℂ)) (n := ω) (x := x)).contMDiffAt
        (l.open_target.mem_nhds hz.1)
    have hE : ContMDiffAt 𝓘(ℂ, Fin m → ℂ) 𝓘(ℂ, Fin d → ℂ) ω e' (l.symm z) :=
      (hC _ hz.2).contMDiffAt (e'.open_source.mem_nhds hz.2)
    exact (hE.comp z hL).contDiffAt.analyticAt
  have hxl : x ∈ l.source := mem_chart_source _ x
  have hxt : l x ∈ t.source := by
    refine ⟨l.map_source hxl, ?_⟩
    change l.symm (l x) ∈ e'.source
    rwa [l.left_inv hxl]
  exact a3b4a_classAnalyticChart_dimensions t ht ⟨l x, hxt⟩

theorem exists_affine_of_point_chart_dimension
    (X : Over (Spec ↧ℂ)) [Smooth X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (x : ComplexPoint X) (hx : x ∈ (pointChart e).source) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ x.underlying ∈ U ∧
      SmoothOfRelativeDimension d (ComplexPoint.openScheme X U).hom := by
  obtain ⟨U, hU, hxU, m, hm⟩ := a3b4g_exists_affine_smoothOfRelativeDimension X x.underlying
  let Y := ComplexPoint.openScheme X U
  letI : IsAffine Y.left := hU
  letI : SmoothOfRelativeDimension m Y.hom := hm
  letI : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
  letI : QuasiCompact Y.hom := (quasiCompact_iff_compactSpace Y.hom).2 inferInstance
  letI : IsSeparated Y.hom := inferInstanceAs (IsSeparated (U.ι ≫ X.hom))
  let xU := ComplexPoint.asOpenPoint X U x hxU
  have hfx : Point.map (ComplexPoint.openInclusion X U) xU = x :=
    Over.OverMorphism.ext (ComplexPoint.liftToOpen_fac X U x hxU)
  letI : Nonempty (ComplexPoint Y) := ⟨xU⟩
  obtain ⟨a, ha, hasource, _⟩ := a3b4a_classHolomorphicChart_openPullback X U 0 d e he
  have hxa : xU ∈ a.source := by
    rw [hasource]
    change Point.map (ComplexPoint.openInclusion X U) xU ∈ e.source
    rw [hfx]
    exact hx.1
  have hdim := smooth_dimension_eq_point_chart_dimension Y m d a ha xU ⟨hxa, by trivial⟩
  exact ⟨U, hU, hxU, hdim ▸ hm⟩

theorem exists_affine_etale_point_coordinates
    (X : Over (Spec ↧ℂ)) [Smooth X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (x : ComplexPoint X) (hx : x ∈ (pointChart e).source) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ x.underlying ∈ U ∧
      letI : Algebra ℂ Γ(X.left, U) := overSpecAlgebra X U
      ∃ φ : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ(X.left, U), φ.toRingHom.Etale := by
  obtain ⟨U, hU, hxU, hs⟩ := Smooth.exists_affine_isStandardSmooth X.hom x.underlying
  obtain ⟨m, hm⟩ := RingHom.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension hs
  let Y := ComplexPoint.openScheme X U
  letI : IsAffine Y.left := hU
  letI : SmoothOfRelativeDimension m Y.hom :=
    smoothOfRelativeDimension_affineOpen_of_isStandardSmooth X.hom hU hm
  letI : LocallyOfFiniteType Y.hom := inferInstanceAs (LocallyOfFiniteType (U.ι ≫ X.hom))
  letI : QuasiCompact Y.hom := (quasiCompact_iff_compactSpace Y.hom).2 inferInstance
  letI : IsSeparated Y.hom := inferInstanceAs (IsSeparated (U.ι ≫ X.hom))
  let xU := ComplexPoint.asOpenPoint X U x hxU
  have hfx : Point.map (ComplexPoint.openInclusion X U) xU = x :=
    Over.OverMorphism.ext (ComplexPoint.liftToOpen_fac X U x hxU)
  letI : Nonempty (ComplexPoint Y) := ⟨xU⟩
  obtain ⟨a, ha, hasource, _⟩ := a3b4a_classHolomorphicChart_openPullback X U 0 d e he
  have hxa : xU ∈ a.source := by
    rw [hasource]
    change Point.map (ComplexPoint.openInclusion X U) xU ∈ e.source
    rw [hfx]
    exact hx.1
  have hdim := smooth_dimension_eq_point_chart_dimension Y m d a ha xU ⟨hxa, by trivial⟩
  letI : Algebra ℂ Γ(X.left, U) := overSpecAlgebra X U
  have hm' := hdim ▸ hm
  have hA := algebraMap_isStandardSmoothOfRelativeDimension (d := d) X hm'
  obtain ⟨φ, hC, hφ⟩ := hA.exists_etale_mvPolynomial
  exact ⟨U, hU, hxU, { toRingHom := φ, commutes' := fun c => DFunLike.congr_fun hC c }, hφ⟩

theorem exists_affine_of_point_chart_dimension_within
    (X : Over (Spec ↧ℂ)) [Smooth X.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin 0 → ℂ) × (Fin d → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (x : ComplexPoint X) (hx : x ∈ (pointChart e).source)
    (V : X.left.Opens) (hxV : x.underlying ∈ V) :
    ∃ W : X.left.Opens, IsAffineOpen W ∧ x.underlying ∈ W ∧ W ≤ V ∧
      SmoothOfRelativeDimension d (ComplexPoint.openScheme X W).hom := by
  obtain ⟨O, _hO, hxO, hdimO⟩ := exists_affine_of_point_chart_dimension X d e he x hx
  obtain ⟨W, hW, hxW, hsub⟩ := exists_isAffineOpen_mem_and_subset
    (U := O ⊓ V) (x := x.underlying) ⟨hxO, hxV⟩
  have hWO : W ≤ O := fun y hy => (hsub hy).1
  have hWV : W ≤ V := fun y hy => (hsub hy).2
  let Y := ComplexPoint.openScheme X O
  letI : SmoothOfRelativeDimension d Y.hom := hdimO
  have hi : SmoothOfRelativeDimension (0 + d) (X.left.homOfLE hWO ≫ Y.hom) := inferInstance
  have hcomp : X.left.homOfLE hWO ≫ Y.hom = (ComplexPoint.openScheme X W).hom := by
    change X.left.homOfLE hWO ≫ (O.ι ≫ X.hom) = W.ι ≫ X.hom
    rw [← Category.assoc, Scheme.homOfLE_ι]
  refine ⟨W, hW, hxW, hWV, ?_⟩
  simpa only [zero_add, hcomp] using hi

end AlgebraicGeometry.SingularCycles
