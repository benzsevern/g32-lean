import HodgeLean.Foundations.TubularEuler.AffineImmersionPointKernelHelpers
import HodgeLean.Foundations.TubularEuler.AffineSmoothSectionHelpers
import HodgeLean.Foundations.TubularEuler.ActualStalkCotangentComparisonHelpers
import HodgeLean.Foundations.TubularEuler.ConormalLocalizationComparisonHelpers

/-! # Faithfulness of the specified affine immersion differential

The retained regular-section differential is compared with the universal
conormal injection through the actual ambient local ring.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Adapters
attribute [local instance] overSpecAlgebra

theorem affineConormalTensorDifferential_injective
    (X Y : Over (Spec (CommRingCat.of ℂ))) (j : Y ⟶ X) [IsClosedImmersion j.left]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] [Smooth Y.hom]
    (V : X.left.Opens) (hV : IsAffineOpen V) (x : ComplexPoint Y)
    (hx : x ∈ Point.overOpen (j.left ⁻¹ᵁ V))
    (z : ComplexPoint X) (hz : Point.map j x ∈ (chartAt (Fin d → ℂ) z).source) :
    let ρ := (j.left.app V ≫ Spec.preimage
      (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom
    letI : Algebra Γ(X.left, V) ℂ := ρ.toAlgebra
    Function.Injective (affineConormalTensorDifferential X Y j d V hV x hx z hz) := by
  let ρ := (j.left.app V ≫ Spec.preimage
    (ComplexPoint.liftToOpen Y (j.left ⁻¹ᵁ V) x hx ≫ (hV.preimage j.left).isoSpec.hom)).hom
  let A := Γ(X.left, V)
  let B := Γ(Y.left, j.left ⁻¹ᵁ V)
  let P := Point.map j x
  have hP : P.underlying ∈ V := hx
  let S := X.left.presheaf.stalk P.underlying
  let γ := (X.left.presheaf.germ V P.underlying hP).hom
  let p := (hV.primeIdealOf ⟨P.underlying, hP⟩).asIdeal
  letI : Algebra A ℂ := ρ.toAlgebra
  letI : Algebra A B := (j.left.app V).hom.toAlgebra
  letI : Algebra A S := γ.toAlgebra
  letI : IsScalarTower ℂ A B := affineSectionMap_scalarTower X Y j V
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth d X.hom
  letI : Algebra.Smooth ℂ A := smoothAffineSections X V hV
  letI : Algebra.Smooth ℂ B := smoothAffineSections Y (j.left ⁻¹ᵁ V) (hV.preimage j.left)
  letI : p.IsPrime := inferInstance
  letI : IsLocalization.AtPrime S p := hV.isLocalization_stalk ⟨P.underlying, hP⟩
  have hker : RingHom.ker (algebraMap A ℂ) = p :=
    affineImmersion_pointMap_kernel X Y j V hV x hx
  let f := affineConormalTensorDifferential X Y j d V hV x hx z hz
  change Function.Injective f
  intro a b hab
  obtain ⟨w, hw⟩ := tensor_exists_one_tmul_of_surjective
    (affineImmersion_pointMap_surjective X Y j V hV x hx) (a - b)
  obtain ⟨u, rfl⟩ := (RingHom.ker (j.left.app V).hom).toCotangent_surjective w
  have hfzero : f ((1 : ℂ) ⊗ₜ[A] (RingHom.ker (j.left.app V).hom).toCotangent u) = 0 := by
    rw [← hw, map_sub, hab, sub_self]
  have hdiff : actualStalkDifferential X d z P hz (γ u.val) = 0 := by
    rw [affineConormalTensorDifferential_regular_section, one_smul] at hfzero
    rw [actualStalkDifferential_eq_section]
    exact hfzero
  have hu : ρ u.val = 0 := by
    change Spec.preimage _ (j.left.app V u.val) = 0
    rw [u.property, map_zero]
  have heval : P.stalkHom.hom (γ u.val) = ρ u.val :=
    (a3b4g_stalkHom_germ V u.val P hP).trans
      (affineImmersion_preimage_evaluate X Y j V hV x hx u.val).symm
  have hum : γ u.val ∈ IsLocalRing.maximalIdeal S :=
    a3b4g_mem_of_stalkHom_eq_zero P _ (heval.trans hu)
  have hsq := (actualStalkDifferential_zero_iff_mem_square X d z P hz (γ u.val) hum).mp hdiff
  have ht := smoothConormalTensor_generator_zero_of_local_square
    (R := ℂ) (A := A) (B := B) (K := ℂ) (S := S)
    (j.left.app_surjective V hV) p hker u hu hsq
  exact sub_eq_zero.mp (hw.trans ht)

#print axioms affineConormalTensorDifferential_injective

end HodgeLean.Foundations.TubularEuler
