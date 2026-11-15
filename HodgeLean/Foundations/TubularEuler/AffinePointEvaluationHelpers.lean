import HodgeLean.Foundations.BundleResolution.ModuleOpenRegularEvaluationHelpers
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

/-! # The actual value homomorphism in affine point coordinates

Recovering a point's ring map agrees with evaluating its original regular sections.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Foundations.BundleResolution

theorem affinePoint_preimage_evaluate {Q : Over (Spec ↧ℂ)}
    (U : Q.left.Opens) (hU : IsAffineOpen U) (x : ComplexPoint Q)
    (hx : x ∈ Point.overOpen U) (s : Γ(Q.left, U)) :
    Spec.preimage (ComplexPoint.liftToOpen Q U x hx ≫ hU.isoSpec.hom) s =
      Point.evaluate U s x := by
  let a := ComplexPoint.liftToOpen Q U x hx
  let b := a ≫ hU.isoSpec.hom
  let ψ := Spec.preimage b
  have hb : Spec.map ψ = b := Spec.map_preimage b
  have he : b.appTop ((Scheme.ΓSpecIso Γ(Q.left, U)).inv s) = a.appTop (U.topIso.inv s) := by
    dsimp only [b]
    rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop]
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  have hc := congrArg (fun f : Γ(Spec Γ(Q.left, U), ⊤) ⟶ CommRingCat.of ℂ =>
      f ((Scheme.ΓSpecIso Γ(Q.left, U)).inv s)) (Scheme.ΓSpecIso_naturality ψ)
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      ((Spec.map ψ).appTop ((Scheme.ΓSpecIso Γ(Q.left, U)).inv s)) =
    ψ ((Scheme.ΓSpecIso Γ(Q.left, U)).hom ((Scheme.ΓSpecIso Γ(Q.left, U)).inv s)) at hc
  rw [hb, he, Iso.inv_hom_id_apply] at hc
  exact hc.symm.trans (i1_openRegularEvaluation U s x hx)

theorem affineImmersion_preimage_evaluate
    (X Y : Over (Spec ↧ℂ)) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V)) (s : Γ(X.left, V)) :
    (j.left.app V ≫ Spec.preimage
      (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)) s =
        Point.evaluate V s (Point.map j x) := by
  change Spec.preimage
    (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)
      (j.left.app V s) = _
  rw [affinePoint_preimage_evaluate (j.left ⁻¹ᵁ V) (hV.preimage j.left) x hx]
  exact (Point.evaluate_map j V s x).symm

#print axioms affineImmersion_preimage_evaluate

#print axioms affinePoint_preimage_evaluate

end HodgeLean.Foundations.TubularEuler
