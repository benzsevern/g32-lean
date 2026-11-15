import HodgeLean.Foundations.QuotientDuality.ProperCycleDimension

/-! # Actual zero-dimensional integral complex ambient schemes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Every point of a zero-dimensional integral finite-type complex scheme has coheight zero.
Source: EGA IV, 5.6.5, dimension formula over a field.
HC no distance; AV milestone no distance. -/
lemma properCycle_zero_dimension_coheight
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (hdim : TopologicalSpace.dim X.left = 0) (x : X.left) : Order.coheight x = 0 := by
  have h := a2r_height_add_coheight X x
  rw [properCycle_height_generic X, hdim, Nat.cast_zero] at h
  exact (add_eq_zero.mp h).2

/-- Every point of the actual zero-dimensional integral ambient scheme is its generic point.
Source: EGA IV, 5.6.5, strict specialization raises coheight.
HC no distance; AV milestone no distance. -/
lemma properCycle_zero_dimension_point_eq_generic
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (hdim : TopologicalSpace.dim X.left = 0) (x : X.left) : x = genericPoint X.left := by
  by_contra hn
  have hle : x ≤ genericPoint X.left := le_top
  have hlt : x < genericPoint X.left := lt_iff_le_not_ge.mpr ⟨hle, fun hge =>
    hn (((Scheme.le_iff_specializes.mp hge).antisymm
      (Scheme.le_iff_specializes.mp hle)).eq)⟩
  have h := Order.coheight_add_one_le hlt
  rw [properCycle_zero_dimension_coheight X hdim x,
    properCycle_zero_dimension_coheight X hdim (genericPoint X.left)] at h
  simp at h

/-- The actual zero-dimensional integral complex ambient scheme is smooth, by generic smoothness at its sole scheme point.
Source: EGA IV, 17.5.1, generic smoothness over a perfect field.
HC no distance; AV milestone no distance. -/
lemma properCycle_zero_dimension_smooth
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (hdim : TopologicalSpace.dim X.left = 0) : Smooth X.hom := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro x _
  rw [properCycle_zero_dimension_point_eq_generic X hdim x]
  exact X.hom.genericPoint_mem_smoothLocus_of_perfectField

/-- The actual complex-point space of the zero-dimensional integral ambient scheme has at most one point.
Source: Hilbert's Nullstellensatz, the closed-point equivalence over an algebraically closed field.
HC no distance; AV milestone no distance. -/
lemma properCycle_zero_dimension_complex_subsingleton
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (hdim : TopologicalSpace.dim X.left = 0) : Subsingleton (ComplexPoint X) := by
  constructor
  intro x y
  apply Over.OverMorphism.ext
  apply ext_of_apply_closedPoint_eq X.hom (Over.w x) (Over.w y)
  exact (properCycle_zero_dimension_point_eq_generic X hdim x.underlying).trans
    (properCycle_zero_dimension_point_eq_generic X hdim y.underlying).symm

/-- The actual complex-point space of a zero-dimensional integral finite-type complex scheme is nonempty.
Source: Hilbert's Nullstellensatz, existence of the rational point of the closed generic point.
HC no distance; AV milestone no distance. -/
lemma properCycle_zero_dimension_complex_nonempty
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (hdim : TopologicalSpace.dim X.left = 0) : Nonempty (ComplexPoint X) := by
  have he : ({genericPoint X.left} : Set X.left) = Set.univ := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact properCycle_zero_dimension_point_eq_generic X hdim x
  have hc : IsClosed ({genericPoint X.left} : Set X.left) := he ▸ isClosed_univ
  let p := (pointEquivClosedPoint X.hom).symm ⟨genericPoint X.left, hc⟩
  exact ⟨Over.homMk p.1 p.2⟩

/-- Every nonzero cycle on the actual zero-dimensional integral ambient scheme has whole analytic support.
Source: Fulton, Intersection Theory, section 1.5, cycle supports; EGA IV, 5.6.5.
HC no distance; AV milestone no distance. -/
lemma properCycle_zero_dimension_nonzero_support
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (hdim : TopologicalSpace.dim X.left = 0) (γ : AlgebraicCycle X.left ℚ) (hγ : γ ≠ 0) :
    a3b4_cycleSupport X.hom γ = Set.univ := by
  have hs : ∃ ξ, γ ξ ≠ 0 := by
    by_contra h
    apply hγ
    ext ξ
    exact not_ne_iff.mp (fun hn => h ⟨ξ, hn⟩)
  obtain ⟨ξ, hξ⟩ := hs
  apply Set.eq_univ_of_forall
  intro x
  refine Set.mem_iUnion₂.mpr ⟨ξ, hξ, ?_⟩
  apply specializes_iff_mem_closure.mp
  apply Scheme.le_iff_specializes.mp
  rw [properCycle_zero_dimension_point_eq_generic X hdim ξ]
  exact le_top

end HodgeLean.Foundations.QuotientDuality
