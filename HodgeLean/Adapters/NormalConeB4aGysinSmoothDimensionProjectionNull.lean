import HodgeLean.Adapters.NormalConeB4aGysinSmoothFiniteCover
import HodgeLean.Adapters.NormalConeB4aGysinSmoothProjectionNull
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry

/-- A smooth source of algebraic dimension below the parameter dimension has
null parameter image, allowing its relative dimension to vary between regions. -/
theorem a3b4a_gysin_smooth_dimension_parameter_image_null
    (X Y : Over (Spec (CommRingCat.of ℂ))) (n c : ℕ)
    [Smooth X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y)
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ) (hdim : topologicalKrullDim X.left < (n : ℕ)) :
    MeasureTheory.volume ((fun x => (Φ (Point.map f x)).1) ''
      (Point.map f ⁻¹' Φ.source)) = 0 := by
  classical
  obtain ⟨U, d, hU, J, hcover⟩ := a3b4a_gysin_smooth_finite_affine_dimension_cover X n hdim
  let A : X.left → Set (Fin n → ℂ) := fun j =>
    (fun z : ComplexPoint (ComplexPoint.openScheme X (U j)) =>
      (Φ (Point.map (ComplexPoint.openInclusion X (U j) ≫ f) z)).1) ''
      (Point.map (ComplexPoint.openInclusion X (U j) ≫ f) ⁻¹' Φ.source)
  have hnull : ∀ j, MeasureTheory.volume (A j) = 0 := by
    intro j
    let Xj := ComplexPoint.openScheme X (U j)
    let g : Xj ⟶ Y := ComplexPoint.openInclusion X (U j) ≫ f
    letI : IsAffine Xj.left := (hU j).1
    letI : SmoothOfRelativeDimension (d j) Xj.hom := (hU j).2.2.2
    letI : LocallyOfFiniteType Xj.hom :=
      inferInstanceAs (LocallyOfFiniteType ((U j).ι ≫ X.hom))
    letI : QuasiCompact Xj.hom := inferInstance
    letI : IsSeparated Xj.hom := inferInstance
    exact a3b4a_gysin_smooth_source_parameter_image_null Xj Y (d j) n c g Φ hΦ (hU j).2.2.1
  have hsubset : (fun x => (Φ (Point.map f x)).1) '' (Point.map f ⁻¹' Φ.source) ⊆
      ⋃ j ∈ J, A j := by
    rintro a ⟨x, hx, rfl⟩
    obtain ⟨j, hj, hxU⟩ := hcover x.underlying
    let xj := (ComplexPoint.openHomeomorph X (U j)).symm ⟨x, hxU⟩
    have hxmap : Point.map (ComplexPoint.openInclusion X (U j)) xj = x :=
      congrArg Subtype.val ((ComplexPoint.openHomeomorph X (U j)).apply_symm_apply ⟨x, hxU⟩)
    have hm : Point.map (ComplexPoint.openInclusion X (U j) ≫ f) xj = Point.map f x := by
      simpa only [Point.map, Category.assoc] using congrArg (Point.map f) hxmap
    apply Set.mem_iUnion₂.mpr
    refine ⟨j, hj, xj, ?_, ?_⟩
    · change Point.map (ComplexPoint.openInclusion X (U j) ≫ f) xj ∈ Φ.source
      rwa [hm]
    · change (Φ (Point.map (ComplexPoint.openInclusion X (U j) ≫ f) xj)).1 =
        (Φ (Point.map f x)).1
      rw [hm]
  apply MeasureTheory.measure_mono_null hsubset
  exact (MeasureTheory.measure_biUnion_null_iff J.countable_toSet).mpr (fun j _ => hnull j)

end HodgeLean.Adapters
