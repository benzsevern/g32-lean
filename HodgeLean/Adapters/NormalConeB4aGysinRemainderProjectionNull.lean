import HodgeLean.Adapters.NormalConeB4aGysinLowerStratumProjectionNull
import HodgeLean.Adapters.NormalConeB4aGysinFiltrationPoint
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- The entire first closed remainder of a bounded support has null parameter
image in the ambient chart, by its actual countable smooth-layer cover. -/
theorem a3b4a_gysin_support_remainder_parameter_image_null
    (Y : Over (Spec (CommRingCat.of ℂ))) [IsNoetherian Y.left]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (S : Closeds Y.left) (n c : ℕ)
    (hdim : topologicalKrullDim (reducedClosedSubscheme S) ≤ (n : ℕ))
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ) :
    MeasureTheory.volume ((fun y : ComplexPoint Y => (Φ y).1) ''
      {y | y ∈ Φ.source ∧ y.underlying ∈ reducedClosedSingularRemainder Y.hom S}) = 0 := by
  let T := fun k => reducedSmoothClosedFiltration Y.hom S (k + 1)
  let A := fun k => Over.mk (reducedClosedSmoothPieceι Y.hom (T k) ≫ Y.hom)
  let f : (k : ℕ) → A k ⟶ Y := fun k =>
    Over.homMk (reducedClosedSmoothPieceι Y.hom (T k)) rfl
  let B : ℕ → Set (Fin n → ℂ) := fun k =>
    (fun z => (Φ (Point.map (f k) z)).1) '' (Point.map (f k) ⁻¹' Φ.source)
  have hnull : ∀ k, MeasureTheory.volume (B k) = 0 := fun k =>
    a3b4a_gysin_lower_stratum_parameter_image_null Y S n c hdim k Φ hΦ
  have hsubset : (fun y : ComplexPoint Y => (Φ y).1) ''
      {y | y ∈ Φ.source ∧ y.underlying ∈ reducedClosedSingularRemainder Y.hom S} ⊆
        ⋃ k, B k := by
    rintro a ⟨y, ⟨hyΦ, hyR⟩, rfl⟩
    obtain ⟨k, hk, hknext⟩ := a3b4a_gysin_point_mem_smooth_filtration_layer
      Y.hom (reducedClosedSingularRemainder Y.hom S) y.underlying hyR
    letI : IsImmersion (f k).left :=
      inferInstanceAs (IsImmersion (reducedClosedSmoothPieceι Y.hom (T k)))
    letI : LocallyOfFiniteType (A k).hom :=
      inferInstanceAs (LocallyOfFiniteType (reducedClosedSmoothPieceι Y.hom (T k) ≫ Y.hom))
    have hyrange : y ∈ Set.range (Point.map (f k)) := by
      rw [ComplexPoint.range_map_of_isImmersion_of_comm Y (A k) (f k)]
      change y.underlying ∈ Set.range (reducedClosedSmoothPieceι Y.hom (T k))
      rw [reducedClosedSmoothPiece_range]
      constructor
      · change y.underlying ∈ reducedSmoothClosedFiltration Y.hom S (k + 1)
        simpa only [reducedSmoothClosedFiltration_succ_start] using hk
      · change y.underlying ∉ reducedSmoothClosedFiltration Y.hom S ((k + 1) + 1)
        simpa only [reducedSmoothClosedFiltration_succ_start] using hknext
    obtain ⟨z, hz⟩ := hyrange
    apply Set.mem_iUnion.mpr
    refine ⟨k, z, ?_, ?_⟩
    · change Point.map (f k) z ∈ Φ.source
      rwa [hz]
    · change (Φ (Point.map (f k) z)).1 = (Φ y).1
      rw [hz]
  exact MeasureTheory.measure_mono_null hsubset (MeasureTheory.measure_iUnion_null hnull)

end HodgeLean.Adapters
