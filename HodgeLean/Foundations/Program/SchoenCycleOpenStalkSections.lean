import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Restrict
import HodgeLean.Foundations.Program.SchoenCycleUnramifiedStalks

/-! # Actual germs of sections transported from open subschemes -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The inclusion stalk map sends the germ of a transported ambient section
to its original germ on the open subscheme.
Source: Hartshorne, Algebraic Geometry, II.2, restrictions and stalks. -/
theorem s2e_open_section_stalk_pullback
    (X : Scheme) (U : X.Opens) (z : U.toScheme)
    (hz : U.ι z ∈ U.ι ''ᵁ (⊤ : U.toScheme.Opens)) (s : Γ(U.toScheme, ⊤)) :
    U.ι.stalkMap z (X.presheaf.germ (U.ι ''ᵁ ⊤) (U.ι z) hz ((U.ι.appIso ⊤).inv s)) =
      U.toScheme.presheaf.germ ⊤ z trivial s := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  let e : U.ι ⁻¹ᵁ U.ι ''ᵁ (⊤ : U.toScheme.Opens) = ⊤ := U.ι.preimage_image_eq ⊤
  have he : U.ι.app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv s) =
      U.toScheme.presheaf.map (eqToHom e).op s := by
    change ((U.ι.appIso ⊤).inv ≫ U.ι.app (U.ι ''ᵁ ⊤)) s = _
    rw [U.ι.appIso_inv_app]
  rw [he]
  exact U.toScheme.presheaf.germ_res_apply (eqToHom e) z hz s

/-- A regular section generating the maximal ideal on an open subscheme also
generates the ambient stalk maximal ideal after section transport.
Source: Hartshorne, Algebraic Geometry, II.2, open immersions and local rings. -/
theorem s2e_open_ambient_stalk_parameter
    (X : Scheme) (U : X.Opens) (z : U.toScheme)
    (hz : U.ι z ∈ U.ι ''ᵁ (⊤ : U.toScheme.Opens)) (s : Γ(U.toScheme, ⊤))
    (hs : IsLocalRing.maximalIdeal (U.toScheme.presheaf.stalk z) =
      Ideal.span {U.toScheme.presheaf.germ ⊤ z trivial s}) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk (U.ι z)) =
      Ideal.span {X.presheaf.germ (U.ι ''ᵁ ⊤) (U.ι z) hz ((U.ι.appIso ⊤).inv s)} := by
  have hf : Function.Bijective (U.ι.stalkMap z).hom :=
    (asIso (U.ι.stalkMap z)).commRingCatIsoToRingEquiv.bijective
  apply (Ideal.relIsoOfBijective (U.ι.stalkMap z).hom hf).symm.injective
  change (IsLocalRing.maximalIdeal (X.presheaf.stalk (U.ι z))).map (U.ι.stalkMap z).hom =
    (Ideal.span {X.presheaf.germ (U.ι ''ᵁ ⊤) (U.ι z) hz ((U.ι.appIso ⊤).inv s)}).map
      (U.ι.stalkMap z).hom
  rw [s2e_unramified_stalk_maximalIdeal U.ι z, hs, Ideal.map_span, Set.image_singleton,
    s2e_open_section_stalk_pullback]

/-- A section's maximal-ideal generator statement transports between equal
points together with their open-membership proofs.
Source: Hartshorne, Algebraic Geometry, II.1 and II.2, stalk transport. -/
theorem s2e_section_parameter_point_congr
    (X : Scheme) (U : X.Opens) (x y : X) (hx : x ∈ U) (hy : y ∈ U) (h : x = y)
    (s : Γ(X, U))
    (hs : IsLocalRing.maximalIdeal (X.presheaf.stalk x) =
      Ideal.span {X.presheaf.germ U x hx s}) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk y) = Ideal.span {X.presheaf.germ U y hy s} := by
  subst y
  exact hs

end HodgeLean.Foundations.Program
