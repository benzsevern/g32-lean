import HodgeLean.Foundations.Program.G32Native.PairedC3CoordinateNormalization

/-! # The marked intersection in normalized coordinates -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Inverse images through an isomorphism retain their subscheme inclusions.
Source: Hartshorne, Algebraic Geometry, II.3. -/
theorem pairedC3_subscheme_iso_of_comap
    {X Y : Scheme} (a : X ⟶ Y) [IsIso a]
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (h : I = J.comap a) :
    ∃ e : I.subscheme ≅ J.subscheme,
      e.hom ≫ J.subschemeι = I.subschemeι ≫ a := by
  subst I
  let f := Scheme.IdealSheafData.subschemeMap (J.comap a) J a
    (Scheme.IdealSheafData.le_map_comap J a)
  have sq : CategoryTheory.IsPullback (J.comap a).subschemeι f a J.subschemeι := by
    apply isPullback_of_isClosedImmersion _ _ _ _
      (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
  have : IsIso f := sq.isIso_snd_of_isIso
  exact ⟨asIso f, sq.w.symm⟩

/-- A retained coordinate hyperplane maps isomorphically to the standard one,
with its equation over the explicit projective coordinate exchange.
Source: Hartshorne, Algebraic Geometry, II.2 and II.3. -/
theorem pairedC3_normalized_hyperplane (k : ℕ) (j : Fin (k + 1)) :
    ∃ e : (s2e_s2b_residueIdeal k j).subscheme ≅ (s2e_hyperplaneIdeal k).subscheme,
      e.hom ≫ (s2e_hyperplaneIdeal k).subschemeι =
        (s2e_s2b_residueIdeal k j).subschemeι ≫
          (s2e_linearProjectiveOverIso (pairedC3CoordinateSwap k j)).hom.left :=
  pairedC3_subscheme_iso_of_comap _ _ _ (pairedC3_coordinate_swap_hyperplane k j).symm

/-- The actual marked intersection has standard coordinates after recording
exactly the same coordinate exchange on its map into the slice.
Source: Hartshorne, Algebraic Geometry, II.2 and II.3. -/
theorem pairedC3_normalized_intersection
    (k : ℕ) {V : Over (Spec ↧ℂ)}
    (i : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ V)
    [IsClosedImmersion i.left] (J : V.left.IdealSheafData)
    (j : Fin (k + 1)) (hJ : J.comap i.left = s2e_s2b_residueIdeal k j) :
    ∃ e : (residualIntersection i J).left ≅ (s2e_hyperplaneIdeal k).subscheme,
      e.hom ≫ (s2e_hyperplaneIdeal k).subschemeι =
        (residualIntersectionFirst i J).left ≫
          (s2e_linearProjectiveOverIso (pairedC3CoordinateSwap k j)).hom.left := by
  obtain ⟨e₀, he₀⟩ := (residual_intersection_subscheme_iff i J _).mpr hJ
  obtain ⟨e₁, he₁⟩ := pairedC3_normalized_hyperplane k j
  refine ⟨e₀ ≪≫ e₁, ?_⟩
  rw [Iso.trans_hom, Category.assoc, he₁, ← Category.assoc, he₀]

#print axioms pairedC3_subscheme_iso_of_comap
#print axioms pairedC3_normalized_hyperplane
#print axioms pairedC3_normalized_intersection
end HodgeLean.Foundations.Program.G32Native
