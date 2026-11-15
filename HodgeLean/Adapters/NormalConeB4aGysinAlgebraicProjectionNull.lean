import HodgeLean.Adapters.NormalConeB4aGysinRemainderProjectionNull

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- The parameter image of any smaller-dimensional algebraic source is null,
using its canonical smooth filtration and allowing singularities and nilpotents. -/
theorem a3b4a_gysin_algebraic_source_parameter_image_null
    (X Y : Over (Spec (CommRingCat.of ℂ))) [IsNoetherian X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (n c : ℕ) (hdim : topologicalKrullDim X.left < (n : ℕ))
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ) :
    MeasureTheory.volume ((fun x => (Φ (Point.map f x)).1) ''
      (Point.map f ⁻¹' Φ.source)) = 0 := by
  let T := fun k => reducedSmoothClosedFiltration X.hom ⊤ k
  let A := fun k => Over.mk (reducedClosedSmoothPieceι X.hom (T k) ≫ X.hom)
  let i : (k : ℕ) → A k ⟶ X := fun k =>
    Over.homMk (reducedClosedSmoothPieceι X.hom (T k)) rfl
  let B : ℕ → Set (Fin n → ℂ) := fun k =>
    (fun z => (Φ (Point.map (i k ≫ f) z)).1) '' (Point.map (i k ≫ f) ⁻¹' Φ.source)
  have hnull : ∀ k, MeasureTheory.volume (B k) = 0 := by
    intro k
    letI : NoetherianSpace (reducedClosedSubscheme (T k)) :=
      (reducedClosedSubschemeι (T k)).isClosedEmbedding.isInducing.noetherianSpace
    letI : NoetherianSpace (reducedClosedSmoothPiece X.hom (T k)) :=
      (reducedClosedStructureMap X.hom (T k)).smoothLocus.ι.isOpenEmbedding.isInducing.noetherianSpace
    letI : NoetherianSpace (A k).left :=
      inferInstanceAs (NoetherianSpace (reducedClosedSmoothPiece X.hom (T k)))
    letI : Smooth (A k).hom :=
      inferInstanceAs (Smooth (reducedClosedSmoothPieceι X.hom (T k) ≫ X.hom))
    letI : LocallyOfFiniteType (A k).hom :=
      inferInstanceAs (LocallyOfFiniteType (reducedClosedSmoothPieceι X.hom (T k) ≫ X.hom))
    letI : QuasiCompact (A k).hom := inferInstance
    letI : IsSeparated (A k).hom :=
      inferInstanceAs (IsSeparated (reducedClosedSmoothPieceι X.hom (T k) ≫ X.hom))
    exact a3b4a_gysin_smooth_dimension_parameter_image_null (A k) Y n c (i k ≫ f) Φ hΦ
      ((reducedClosedSmoothPieceι X.hom (T k)).isEmbedding.isInducing.topologicalKrullDim_le.trans_lt hdim)
  have hsubset : (fun x => (Φ (Point.map f x)).1) '' (Point.map f ⁻¹' Φ.source) ⊆
      ⋃ k, B k := by
    rintro a ⟨x, hxΦ, rfl⟩
    obtain ⟨k, hk, hknext⟩ := a3b4a_gysin_point_mem_smooth_filtration_layer
      X.hom ⊤ x.underlying (by trivial)
    letI : IsImmersion (i k).left :=
      inferInstanceAs (IsImmersion (reducedClosedSmoothPieceι X.hom (T k)))
    letI : LocallyOfFiniteType (A k).hom :=
      inferInstanceAs (LocallyOfFiniteType (reducedClosedSmoothPieceι X.hom (T k) ≫ X.hom))
    have hxrange : x ∈ Set.range (Point.map (i k)) := by
      rw [ComplexPoint.range_map_of_isImmersion_of_comm X (A k) (i k)]
      change x.underlying ∈ Set.range (reducedClosedSmoothPieceι X.hom (T k))
      rw [reducedClosedSmoothPiece_range]
      exact ⟨hk, hknext⟩
    obtain ⟨z, hz⟩ := hxrange
    have hm : Point.map (i k ≫ f) z = Point.map f x := by
      simpa only [Point.map, Category.assoc] using congrArg (Point.map f) hz
    apply Set.mem_iUnion.mpr
    refine ⟨k, z, ?_, ?_⟩
    · change Point.map (i k ≫ f) z ∈ Φ.source
      rwa [hm]
    · change (Φ (Point.map (i k ≫ f) z)).1 = (Φ (Point.map f x)).1
      rw [hm]
  exact MeasureTheory.measure_mono_null hsubset (MeasureTheory.measure_iUnion_null hnull)

end HodgeLean.Adapters
