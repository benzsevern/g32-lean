import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicProperDegree
import HodgeLean.Foundations.QuotientDuality.ProperCycleFiniteEtaleRestriction
import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothGenericNeighborhood
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenHolomorphicChart

/-! # Actual intrinsic proper degree with singular projective target -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual proper generically finite map has the original intrinsic global degree even when its projective target has singular points; the finite etale test is made on a constructed smooth affine open and its chart is transported to the original target.
Source: Fulton, Intersection Theory, section 1.4; SGA 1, Expose I and Expose XII.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_proper_generic_degree
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    [IsProjective X.hom] [IsProjective Y.hom] (f : X ⟶ Y) [IsProper f.left]
    (d : ℕ) (hdimX : topologicalKrullDim X.left = (d : ℕ))
    (hdimY : topologicalKrullDim Y.left = (d : ℕ))
    (hg : f.left (genericPoint X.left) = genericPoint Y.left)
    (hdegree : 0 < a1p_degree f.left (genericPoint X.left)) :
    homologyMap ℚ (2 * d) (TopCat.ofHom (Point.continuousMap f))
      (properCycle_intrinsic_class X d hdimX) =
    (a1p_degree f.left (genericPoint X.left) : ℚ) • properCycle_intrinsic_class Y d hdimY := by
  have hdY : TopologicalSpace.dim Y.left = d := by
    unfold TopologicalSpace.dim
    rw [hdimY]
    rfl
  obtain ⟨U, _, hgU, hfinite, hetale⟩ :=
    properCycle_generically_finite_etale_affine_open f hg hdegree
  obtain ⟨W, hW, hgW, hWU, hsmooth⟩ := properCycle_smooth_affine_generic_neighborhood Y d hdY U hgU
  letI : IsFinite (f.left ∣_ U) := hfinite
  letI : Etale (f.left ∣_ U) := hetale
  obtain ⟨hfiniteW, hetaleW⟩ := properCycle_finite_etale_restriction_le f.left U W hWU
  letI : Nonempty W := ⟨⟨genericPoint Y.left, hgW⟩⟩
  letI : Nonempty (f.left ⁻¹ᵁ W) := ⟨⟨genericPoint X.left, by
    change f.left (genericPoint X.left) ∈ W
    rwa [hg]⟩⟩
  letI : IsFinite (f.left ∣_ W) := hfiniteW
  letI : Etale (f.left ∣_ W) := hetaleW
  let Z := openScheme Y W
  letI : Nonempty Z.left := inferInstanceAs (Nonempty W.toScheme)
  letI : IsAffine Z.left := hW
  letI : LocallyOfFiniteType Z.hom := by
    change LocallyOfFiniteType (W.ι ≫ Y.hom)
    infer_instance
  letI : QuasiCompact Z.hom := inferInstance
  letI : IsSeparated Z.hom := by
    change IsSeparated (W.ι ≫ Y.hom)
    infer_instance
  letI : SmoothOfRelativeDimension d Z.hom := hsmooth
  obtain ⟨y⟩ := s2t_nonempty_complexPoints Z
  letI : Nonempty (ComplexPoint Z) := ⟨y⟩
  let e := ComplexPoint.localChart Z d y
  obtain ⟨E, hE, hsource, _⟩ := properCycle_holomorphic_vector_chart_open_transport Y W d e
    (properCycle_smooth_local_chart_holomorphic Z d y)
  have hy : Point.map (openInclusion Y W) y ∈ E.source := by
    rw [hsource]
    exact ⟨y, ComplexPoint.mem_localChart_source Z d y, rfl⟩
  exact properCycle_intrinsic_generic_open_degree X Y f d hdimX hdimY hg W hW y E hy hE

end HodgeLean.Foundations.QuotientDuality
