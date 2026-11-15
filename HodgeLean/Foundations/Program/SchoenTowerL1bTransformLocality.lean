import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs

/-! # Locality of the retained reduced transforms
Support comparisons for the base-coordinate induction.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A retained transform lies over its original divisor support. -/
theorem s2v_l1b_strictTransform_support_le {X Y : Scheme} (f : X ⟶ Y)
    (D K : Y.IdealSheafData) :
    (s2c_strictTransform f D K).support ≤ (D.comap f).support := by
  change closure (f ⁻¹' ((D.support : Set Y) \ (K.support : Set Y))) ⊆
    ((D.comap f).support : Set X)
  rw [Scheme.IdealSheafData.support_comap]
  exact closure_minimal (fun _ hx => hx.1) (D.support.isClosed.preimage f.continuous)

/-- Outside the centre, the retained transform and the divisor have the same support. -/
theorem s2v_l1b_strictTransform_support_off_center {X Y : Scheme} (f : X ⟶ Y)
    (D K : Y.IdealSheafData) (x : X) (hx : f x ∉ K.support) :
    x ∈ (s2c_strictTransform f D K).support ↔ f x ∈ D.support := by
  constructor
  · intro h
    have := s2v_l1b_strictTransform_support_le f D K h
    rw [Scheme.IdealSheafData.support_comap] at this
    exact this
  · intro h
    change x ∈ closure (f ⁻¹' ((D.support : Set Y) \ (K.support : Set Y)))
    exact subset_closure ⟨h, hx⟩

/-- On an affine open away from the centre, the retained transform has the radical pullback ideal. -/
theorem s2v_l1b_strictTransform_ideal_off_center {X Y : Scheme} (f : X ⟶ Y)
    (D K : Y.IdealSheafData) (U : X.affineOpens)
    (hU : ∀ x ∈ U.1, f x ∉ K.support) :
    (s2c_strictTransform f D K).ideal U = ((D.comap f).ideal U).radical := by
  have heq : (s2c_strictTransform f D K).ideal U =
      (Scheme.IdealSheafData.vanishingIdeal (D.comap f).support).ideal U := by
    rw [s2c_strictTransform, Scheme.IdealSheafData.vanishingIdeal_ideal,
      Scheme.IdealSheafData.vanishingIdeal_ideal]
    congr 1
    ext p
    change U.2.fromSpec p ∈ (s2c_strictTransform f D K).support ↔
      U.2.fromSpec p ∈ (D.comap f).support
    rw [s2v_l1b_strictTransform_support_off_center f D K _ (hU _ ?_)]
    · rw [Scheme.IdealSheafData.support_comap]
      rfl
    · have hp := Set.mem_range_self (f := U.2.fromSpec) p
      rw [U.2.range_fromSpec] at hp
      exact hp
  simpa only [Scheme.IdealSheafData.vanishingIdeal_support,
    Scheme.IdealSheafData.radical_ideal] using heq

/-- Open restriction preserves the reduced ideal of the retained transform. -/
theorem s2v_l1b_strictTransform_comap_radical {X Y V : Scheme} (f : X ⟶ Y)
    (D K : Y.IdealSheafData) (j : V ⟶ X) [IsOpenImmersion j] :
    ((s2c_strictTransform f D K).comap j).radical =
      (s2c_strictTransform f D K).comap j := by
  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    ← Ideal.comap_radical]
  congr 1
  rw [s2c_strictTransform, Scheme.IdealSheafData.vanishingIdeal_ideal]
  exact (PrimeSpectrum.isRadical_vanishingIdeal _).radical

/-- The retained reduced transform commutes with open restriction. -/
theorem s2v_l1b_strictTransform_comap_open {X Y V : Scheme} (f : X ⟶ Y)
    (D K : Y.IdealSheafData) (j : V ⟶ X) [IsOpenImmersion j] :
    (s2c_strictTransform f D K).comap j = s2c_strictTransform (j ≫ f) D K := by
  have hs : ((s2c_strictTransform f D K).comap j).support =
      (s2c_strictTransform (j ≫ f) D K).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change (⟨j ⁻¹' closure (f ⁻¹' ((D.support : Set Y) \ K.support)), _⟩ :
        TopologicalSpace.Closeds V) =
      ⟨closure ((j ≫ f) ⁻¹' ((D.support : Set Y) \ K.support)), _⟩
    apply TopologicalSpace.Closeds.ext
    exact j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage j.continuous _
  calc
    (s2c_strictTransform f D K).comap j =
        ((s2c_strictTransform f D K).comap j).radical :=
      (s2v_l1b_strictTransform_comap_radical f D K j).symm
    _ = (s2c_strictTransform (j ≫ f) D K).radical := by
      rw [← Scheme.IdealSheafData.vanishingIdeal_support,
        ← Scheme.IdealSheafData.vanishingIdeal_support, hs]
    _ = s2c_strictTransform (j ≫ f) D K := by
      simpa only [Scheme.IdealSheafData.comap_id] using
        s2v_l1b_strictTransform_comap_radical (j ≫ f) D K (𝟙 V)

end HodgeLean.Foundations.Program
