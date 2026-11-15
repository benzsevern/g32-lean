import HodgeLean.Foundations.TubularEuler.AffinePointEvaluationHelpers
import HodgeLean.Foundations.TubularEuler.AnalyticConormalDifferentialHelpers

/-! # Analytic differentiation of the original affine immersion ideal

The scalar action is the map of the actual affine complex point.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Adapters

def affineIdealDifferential
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    let ρ := (j.left.app V ≫ Spec.preimage
      (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom
    letI := Module.compHom ((Fin d → ℂ) →L[ℂ] ℂ) ρ
    RingHom.ker (j.left.app V).hom →ₗ[Γ(X.left, V)] ((Fin d → ℂ) →L[ℂ] ℂ) := by
  let p := Point.map j x
  have hp : p.underlying ∈ V := hx
  let γ := (X.left.presheaf.germ V p.underlying hp).hom
  let ρ := (j.left.app V ≫ Spec.preimage
    (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom
  letI := Module.compHom ((Fin d → ℂ) →L[ℂ] ℂ) ρ
  have he (r : Γ(X.left, V)) : p.stalkHom.hom (γ r) = ρ r := by
    exact (a3b4g_stalkHom_germ V r p hp).trans
      (affineImmersion_preimage_evaluate X Y j V hV x hx r).symm
  have hu (u : RingHom.ker (j.left.app V).hom) : p.stalkHom.hom (γ u.val) = 0 := by
    rw [he]
    change Spec.preimage _ (j.left.app V u.val) = 0
    rw [u.property, map_zero]
  refine { toFun := fun u => actualStalkDifferential X d z p hz (γ u.val)
           map_add' := ?_
           map_smul' := ?_ }
  · intro u v
    change actualStalkDifferential X d z p hz (γ (u.val + v.val)) = _
    rw [map_add, actualStalkDifferential_add]
  · intro r u
    change actualStalkDifferential X d z p hz (γ (r * u.val)) =
      ρ r • actualStalkDifferential X d z p hz (γ u.val)
    rw [map_mul, actualStalkDifferential_mul, he, hu, zero_smul, add_zero]

theorem affineIdealDifferential_mul_zero
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (u v : RingHom.ker (j.left.app V).hom) :
    affineIdealDifferential X Y j d V hV x hx z hz (u * v) = 0 := by
  let p := Point.map j x
  have hp : p.underlying ∈ V := hx
  let γ := (X.left.presheaf.germ V p.underlying hp).hom
  have hu (w : RingHom.ker (j.left.app V).hom) : p.stalkHom.hom (γ w.val) = 0 := by
    rw [a3b4g_stalkHom_germ]
    rw [Point.evaluate_map]
    change Point.evaluate (j.left ⁻¹ᵁ V) (j.left.app V w.val) x = 0
    rw [w.property]
    simp [Point.evaluate]
  change actualStalkDifferential X d z p hz (γ (u.val * v.val)) = 0
  rw [map_mul, actualStalkDifferential_mul, hu, hu, zero_smul, zero_smul, add_zero]

def affineConormalDifferential
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    let ρ := (j.left.app V ≫ Spec.preimage
      (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom
    letI := Module.compHom ((Fin d → ℂ) →L[ℂ] ℂ) ρ
    (RingHom.ker (j.left.app V).hom).Cotangent →ₗ[Γ(X.left, V)] ((Fin d → ℂ) →L[ℂ] ℂ) := by
  let ρ := (j.left.app V ≫ Spec.preimage
    (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom
  letI := Module.compHom ((Fin d → ℂ) →L[ℂ] ℂ) ρ
  exact Ideal.Cotangent.lift (affineIdealDifferential X Y j d V hV x hx z hz)
    (affineIdealDifferential_mul_zero X Y j d V hV x hx z hz)

def affineConormalTensorDifferential
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    let ρ := (j.left.app V ≫ Spec.preimage
      (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom
    letI : Algebra Γ(X.left, V) ℂ := ρ.toAlgebra
    (ℂ ⊗[Γ(X.left, V)] (RingHom.ker (j.left.app V).hom).Cotangent) →ₗ[ℂ]
      ((Fin d → ℂ) →L[ℂ] ℂ) := by
  let ρ := (j.left.app V ≫ Spec.preimage
    (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom
  letI : Algebra Γ(X.left, V) ℂ := ρ.toAlgebra
  letI := Module.compHom ((Fin d → ℂ) →L[ℂ] ℂ) ρ
  letI : IsScalarTower Γ(X.left, V) ℂ ((Fin d → ℂ) →L[ℂ] ℂ) := {
    smul_assoc := by
      intro r c v
      change (ρ r * c) • v = ρ r • (c • v)
      exact mul_smul _ _ _ }
  exact (affineConormalDifferential X Y j d V hV x hx z hz).liftBaseChange ℂ

theorem affineConormalTensorDifferential_regular_section
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source)
    (u : RingHom.ker (j.left.app V).hom) (c : ℂ) :
    let ρ := (j.left.app V ≫ Spec.preimage
      (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom
    letI : Algebra Γ(X.left, V) ℂ := ρ.toAlgebra
    affineConormalTensorDifferential X Y j d V hV x hx z hz
      (c ⊗ₜ (RingHom.ker (j.left.app V).hom).toCotangent u) =
      c • fderiv ℂ (fun a : Fin d → ℂ =>
        Point.evaluate V u.val ((chartAt (Fin d → ℂ) z).symm a))
          ((chartAt (Fin d → ℂ) z) (Point.map j x)) := by
  change c • actualStalkDifferential X d z (Point.map j x) hz
    (X.left.presheaf.germ V (Point.map j x).underlying hx u.val) = _
  rw [actualStalkDifferential_eq_section]

#print axioms affineConormalTensorDifferential_regular_section

#print axioms affineConormalTensorDifferential

#print axioms affineConormalDifferential

#print axioms affineIdealDifferential_mul_zero

#print axioms affineIdealDifferential
end HodgeLean.Foundations.TubularEuler
