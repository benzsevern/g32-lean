import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
open TensorProduct
namespace HodgeLean.Foundations.Program

theorem s2e_flat_of_faithfullyFlat_tower
    (R S T : Type*) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Module.FaithfullyFlat S T] [Module.Flat R T] : Module.Flat R S := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  change Function.Injective (f.baseChange S)
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective S T (f.baseChange S)).mp
  have hi := Module.Flat.lTensor_preserves_injective_linearMap (M := T) f hf
  let eN := AlgebraTensorModule.cancelBaseChange R S S T N
  let eP := AlgebraTensorModule.cancelBaseChange R S S T P
  have hnat : (f.lTensor T).restrictScalars R ∘ₗ eN.toLinearMap.restrictScalars R =
      eP.toLinearMap.restrictScalars R ∘ₗ ((f.baseChange S).lTensor T).restrictScalars R := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul t z =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [tmul_zero, map_zero]
      | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
      | tmul s n => rfl
  intro a b hab
  apply eN.injective
  apply hi
  have hh := congrArg eP hab
  exact (congrArg (fun h => h a) hnat).trans (hh.trans (congrArg (fun h => h b) hnat).symm)

theorem s2e_flat_of_completion_equiv
    (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing R] [IsNoetherianRing S] (f : R →+* S) [IsLocalHom f]
    (F : AdicCompletion (IsLocalRing.maximalIdeal R) R →+*
      AdicCompletion (IsLocalRing.maximalIdeal S) S)
    (hF : ∀ a, F (AdicCompletion.of (IsLocalRing.maximalIdeal R) R a) =
      AdicCompletion.of (IsLocalRing.maximalIdeal S) S (f a))
    (hbij : Function.Bijective F) :
    letI := f.toAlgebra
    Module.Flat R S := by
  letI := f.toAlgebra
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let B := AdicCompletion (IsLocalRing.maximalIdeal S) S
  letI hRB : Algebra R B := ((algebraMap S B).comp f).toAlgebra
  letI hTower : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  let E : A ≃+* B := RingEquiv.ofBijective F hbij
  let e : A ≃ₐ[R] B :=
    { __ := E
      commutes' := hF }
  letI hFlat : Module.Flat R B := Module.Flat.of_linearEquiv e.toLinearEquiv.symm
  letI : Module.FaithfullyFlat S B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact @s2e_flat_of_faithfullyFlat_tower R S B _ _ _ f.toAlgebra
    (inferInstance : Algebra S B) hRB hTower inferInstance hFlat

end HodgeLean.Foundations.Program
