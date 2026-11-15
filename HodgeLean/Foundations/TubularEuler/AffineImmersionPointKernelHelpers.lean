import HodgeLean.Foundations.TubularEuler.AffineIdealDifferentialHelpers

/-! # The scalar map of the actual affine immersion point

The original point presentation is surjective on scalars and has the prime
ideal of the specified ambient point as its kernel.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Adapters

theorem affineImmersion_pointMap_surjective
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V)) :
    Function.Surjective (j.left.app V ≫ Spec.preimage
      (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom := by
  intro c
  refine ⟨a3b4a_gysin_sectionConst X.hom V c, ?_⟩
  rw [affineImmersion_preimage_evaluate X Y j V hV x hx]
  exact a3b4a_gysin_evaluate_sectionConst X.hom V (Point.map j x) hx c

theorem affineImmersion_pointMap_kernel
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V)) :
    RingHom.ker (j.left.app V ≫ Spec.preimage
      (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom =
        (hV.primeIdealOf ⟨(Point.map j x).underlying, hx⟩).asIdeal := by
  let P := Point.map j x
  have hP : P.underlying ∈ V := hx
  let S := X.left.presheaf.stalk P.underlying
  letI : Algebra Γ(X.left, V) S := (X.left.presheaf.germ V P.underlying hP).hom.toAlgebra
  let p := (hV.primeIdealOf ⟨P.underlying, hP⟩).asIdeal
  letI : IsLocalization.AtPrime S p := hV.isLocalization_stalk ⟨P.underlying, hP⟩
  have heval (r : Γ(X.left, V)) :
      P.stalkHom.hom ((X.left.presheaf.germ V P.underlying hP) r) =
      (j.left.app V ≫ Spec.preimage
        (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)) r :=
    (a3b4g_stalkHom_germ V r P hP).trans
      (affineImmersion_preimage_evaluate X Y j V hV x hx r).symm
  ext r
  constructor
  · intro hr
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff S p r).mp
    exact a3b4g_mem_of_stalkHom_eq_zero P _ ((heval r).trans hr)
  · intro hr
    change (j.left.app V ≫ Spec.preimage
      (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)) r = 0
    rw [← heval]
    exact a3b4g_stalkHom_eq_zero_of_mem P _
      ((IsLocalization.AtPrime.to_map_mem_maximal_iff S p r).mpr hr)

#print axioms affineImmersion_pointMap_kernel

#print axioms affineImmersion_pointMap_surjective

end HodgeLean.Foundations.TubularEuler
