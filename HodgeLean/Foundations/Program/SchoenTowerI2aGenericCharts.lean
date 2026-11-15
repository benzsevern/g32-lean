import HodgeLean.Foundations.Program.SchoenCartierUniversalFieldLift
import HodgeLean.Foundations.Program.SchoenTowerN1bcHelpers
import HodgeLean.Foundations.Program.SchoenTowerI2aNormalizationCharts

/-! # Generic field points of the retained modifications
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An ideal whose pullback is locally free of rank one on a nonempty scheme has proper support on a reduced base.
Source: Mathlib, Scheme.IdealSheafData.support_eq_top_iff and Scheme.IdealSheafData.comap_bot. -/
theorem s2v_i2a_center_support_ne_top
    {X Y : Scheme} [IsReduced X] [Nonempty Y]
    (f : Y ⟶ X) (I : X.IdealSheafData)
    (hcartier : ∀ x : Y, ∃ U : Y.affineOpens, x ∈ U.1 ∧
      Nonempty (((I.comap f).ideal U) ≃ₗ[Γ(Y, U)] Γ(Y, U))) :
    I.support ≠ ⊤ := by
  intro hI
  have hzero : I = ⊥ := Scheme.IdealSheafData.support_eq_top_iff.mp hI
  let x : Y := Classical.ofNonempty
  obtain ⟨U, hx, ⟨E⟩⟩ := hcartier x
  haveI : Nonempty U.1 := ⟨⟨x, hx⟩⟩
  rw [hzero, Scheme.IdealSheafData.comap_bot] at E
  change (⊥ : Ideal Γ(Y, U)) ≃ₗ[Γ(Y, U)] Γ(Y, U) at E
  have hz : E.symm 1 = 0 := Subsingleton.elim _ _
  have H : (1 : Γ(Y, U)) = 0 := by
    rw [← E.apply_symm_apply 1, hz, E.map_zero]
  exact one_ne_zero H

/-- The retained factorization of a dominant field point through a Cartier universal modification is dominant.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.14; Mathlib, uniqueness of the specified universal factorization. -/
theorem s2v_i2a_retained_field_lift_dominant
    (B' B : Over (Spec ↧ℂ)) [IsIntegral B'.left] [IsIntegral B.left]
    (b : B' ⟶ B) (I : B.left.IdealSheafData) (hI : I.support ≠ ⊤)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((I.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ B', u ≫ b = f)
    {K : Type} [Field K] (η : Spec ↧K ⟶ B.left) [IsDominant η]
    (θ : Spec ↧K ⟶ B'.left) (hθ : θ ≫ b.left = η) : IsDominant θ := by
  obtain ⟨δ, hδ, hδdom⟩ := s2_cartierUniversal_fieldLift B' B b I hI huniv η
  let T := Over.mk (η ≫ B.hom)
  let f : T ⟶ B := Over.homMk η
  let v : T ⟶ B' := Over.homMk θ (by
    rw [← Over.w b, ← Category.assoc, hθ]
    rfl)
  let w : T ⟶ B' := Over.homMk δ (by
    rw [← Over.w b, ← Category.assoc, hδ]
    rfl)
  obtain ⟨_, _, huniq⟩ := huniv T f (s2_dominant_fieldPoint_cartier η I hI)
  have he : θ = δ := congrArg Over.Hom.left
    ((huniq v (Over.OverMorphism.ext hθ)).trans
      (huniq w (Over.OverMorphism.ext hδ)).symm)
  rw [he]
  exact hδdom

/-- A dominant field point factors through every nonempty open of its integral target.
Source: Mathlib, IsGenericPoint.mem_open_set_iff and Scheme.Hom.denseRange. -/
theorem s2v_i2a_dominant_field_preimage
    {K : Type} [Field K] {Y : Scheme.{0}} [IsIntegral Y]
    (η : Spec ↧K ⟶ Y) [IsDominant η]
    (U : Y.Opens) [Nonempty U] : η ⁻¹ᵁ U = ⊤ := by
  obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty U›
  ext x
  change η x ∈ U ↔ True
  rw [Subsingleton.elim x (genericPoint (Spec ↧K)), s2_dominant_genericPoint η]
  exact iff_true_intro (((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
    ⟨y, by simpa using hy⟩)

/-- A dominant original-field point and a specified complex point share an affine open immersion with an actual field-point factorization.
Source: Mathlib, exists_isAffineOpen_mem_and_subset and IsOpenImmersion.lift_fac. -/
theorem s2v_i2a_affine_field_point_neighborhood
    {K : Type} [Field K] (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left]
    (η : Spec ↧K ⟶ Y.left) [IsDominant η] (x : ComplexPoint Y) :
    ∃ (U : Over (Spec ↧ℂ)) (hU : IsAffine U.left) (u : U ⟶ Y)
      (ηU : Spec ↧K ⟶ U.left),
      IsOpenImmersion u.left ∧ x ∈ Set.range (Point.map u) ∧ ηU ≫ u.left = η := by
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x.left (IsLocalRing.closedPoint ℂ) ∈ (⊤ : Y.left.Opens) from trivial)
  haveI : Nonempty V := ⟨⟨_, hxV⟩⟩
  have hpre := s2v_i2a_dominant_field_preimage η V
  let U : Over (Spec ↧ℂ) := Over.mk (V.ι ≫ Y.hom)
  let u : U ⟶ Y := Over.homMk V.ι
  have hηrange : Set.range η ⊆ Set.range V.ι := by
    rintro _ ⟨z, rfl⟩
    have hz : z ∈ η ⁻¹ᵁ V := by rw [hpre]; trivial
    exact ⟨⟨η z, hz⟩, rfl⟩
  haveI : Subsingleton ↥(Over.mk (𝟙 (Spec ↧ℂ))).left := by
    change Subsingleton (PrimeSpectrum ℂ)
    infer_instance
  have hxrange : Set.range x.left ⊆ Set.range V.ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨x.left z, ?_⟩, rfl⟩
    rw [show z = IsLocalRing.closedPoint ℂ from
      Subsingleton.elim (z : PrimeSpectrum ℂ) _]
    exact hxV
  let xU : ComplexPoint U := Over.homMk (IsOpenImmersion.lift V.ι x.left hxrange) (by
    change IsOpenImmersion.lift V.ι x.left hxrange ≫ (V.ι ≫ Y.hom) = 𝟙 _
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact Over.w x)
  refine ⟨U, hV, u, IsOpenImmersion.lift V.ι η hηrange,
    inferInstanceAs (IsOpenImmersion V.ι), ⟨xU, ?_⟩, IsOpenImmersion.lift_fac _ _ _⟩
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

end HodgeLean.Foundations.Program
