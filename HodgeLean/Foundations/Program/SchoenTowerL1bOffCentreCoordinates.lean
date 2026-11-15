import HodgeLean.Foundations.Program.SchoenTowerL1bRestrictedSectionIso
import HodgeLean.Foundations.Program.SchoenTowerL1bWeightedOffCentre
import HodgeLean.Foundations.Program.SchoenTowerL1bRegularTransform

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Coordinates and reduced branch equations transport over an entire isomorphic inverse image. -/
theorem s2v_l1b_off_centre_coordinates
    {X Y : Scheme.{0}} (f : X ⟶ Y) {J σ : Type}
    (D : J → Y.IdealSheafData) (K : Y.IdealSheafData)
    (U : Y.affineOpens) [IsIso (f ∣_ U.1)]
    {k : Type} [CommRing k] [IsDomain k]
    (c : k →+* Γ(Y, U)) (z : σ → Γ(Y, U))
    (het : (MvPolynomial.eval₂Hom c z).Etale)
    (hK : K.ideal U = ⊤)
    (hD : ∀ j, (D j).ideal U = ⊤ ∨ ∃ t, (D j).ideal U = Ideal.span {z t}) :
    ∃ (V : X.affineOpens) (hV : V.1 = f ⁻¹ᵁ U.1)
      (w : σ → Γ(X, V)),
      (MvPolynomial.eval₂Hom ((f.appLE U.1 V.1 (le_of_eq hV)).hom.comp c) w).Etale ∧
      (K.comap f).ideal V = ⊤ ∧
      (∀ j, (((D j).comap f).ideal V).IsRadical) ∧
      (∀ j, (s2c_strictTransform f (D j) K).ideal V = ((D j).comap f).ideal V) ∧
      (∀ t, (f.appLE U.1 V.1 (le_of_eq hV)).hom (z t) = w t) := by
  letI : IsAffine U.1.toScheme := U.2
  letI : IsAffine (f ⁻¹ᵁ U.1).toScheme := IsAffine.of_isIso (f ∣_ U.1)
  let V : X.affineOpens := ⟨f ⁻¹ᵁ U.1, show IsAffine (f ⁻¹ᵁ U.1).toScheme from inferInstance⟩
  let φ := f.appLE U.1 V.1 le_rfl
  haveI : IsIso φ := s2v_l1b_restricted_section_isIso f U.1
  have hφ : Function.Bijective φ.hom :=
    (ConcreteCategory.isIso_iff_bijective φ).mp inferInstance
  let w : σ → Γ(X, V) := fun t => φ.hom (z t)
  have hw : (MvPolynomial.eval₂Hom (φ.hom.comp c) w).Etale := by
    rw [← MvPolynomial.comp_eval₂Hom]
    exact RingHom.Etale.stableUnderComposition _ _ het (.of_bijective hφ)
  have hK' : (K.comap f).ideal V = ⊤ := by
    rw [s2v_l1b_comap_ideal_affine_charts f K U V le_rfl, hK, Ideal.map_top]
  have hred (j : J) : (((D j).comap f).ideal V).IsRadical := by
    rw [s2v_l1b_comap_ideal_affine_charts f (D j) U V le_rfl]
    rcases hD j with hj | ⟨t, hj⟩
    · rw [hj, Ideal.map_top]
      exact le_top
    · rw [hj, Ideal.map_span, Set.image_singleton]
      exact s2v_l1b_etale_coordinate_radical (φ.hom.comp c) w hw t
  refine ⟨V, rfl, w, hw, hK', hred, ?_, fun _ => rfl⟩
  intro j
  rw [s2v_l1b_strictTransform_off_centre_chart f (D j) K V hK', (hred j).radical]

end HodgeLean.Foundations.Program
