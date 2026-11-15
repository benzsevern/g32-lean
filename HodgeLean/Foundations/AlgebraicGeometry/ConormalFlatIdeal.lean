import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Ideal.Maps

/-! # Scalar extension of ideal modules
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct

namespace AlgebraicGeometry.Conormal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The natural scalar extension map to the extended ideal. -/
def idealExtensionMap (I : Ideal R) :
    S ⊗[R] I →ₗ[S] I.map (algebraMap R S) :=
  (Algebra.idealMap S I).liftBaseChange S

lemma idealExtensionMap_tmul (I : Ideal R) (s : S) (x : I) :
    idealExtensionMap I (s ⊗ₜ[R] x) = s • Algebra.idealMap S I x := rfl

/-- Scalar extension generates the entire extended ideal. -/
lemma idealExtensionMap_surjective (I : Ideal R) :
    Function.Surjective (idealExtensionMap (S := S) I) := by
  rintro ⟨y, hy⟩
  change y ∈ Submodule.span S ((algebraMap R S) '' (I : Set R)) at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨1 ⊗ₜ[R] (⟨x, hx⟩ : I), Subtype.ext (one_smul S _)⟩
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy hx' hy' =>
    obtain ⟨a, ha⟩ := hx'
    obtain ⟨b, hb⟩ := hy'
    exact ⟨a + b, by rw [map_add, ha, hb]; rfl⟩
  | smul s x hx hx' =>
    obtain ⟨a, ha⟩ := hx'
    exact ⟨s • a, by rw [map_smul, ha]; rfl⟩

/-- Flat scalar extension embeds the original ideal module in the new ring. -/
lemma idealExtensionMap_injective [Module.Flat R S] (I : Ideal R) :
    Function.Injective (idealExtensionMap (S := S) I) := by
  have h : (I.map (algebraMap R S)).subtype ∘ₗ idealExtensionMap I =
      (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap ∘ₗ
        I.subtype.baseChange S := by
    ext x
    change (1 : S) • algebraMap R S x.val = x.val • (1 : S)
    rw [one_smul, Algebra.smul_def, mul_one]
  apply Function.Injective.of_comp (f := (I.map (algebraMap R S)).subtype)
  change Function.Injective ((I.map (algebraMap R S)).subtype ∘ₗ idealExtensionMap I)
  rw [h]
  exact (TensorProduct.AlgebraTensorModule.rid R S S).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap I.subtype I.injective_subtype)

/-- Flat scalar extension identifies an ideal module with the extended ideal. -/
def idealExtensionEquiv [Module.Flat R S] (I : Ideal R) :
    S ⊗[R] I ≃ₗ[S] I.map (algebraMap R S) :=
  LinearEquiv.ofBijective (idealExtensionMap I)
    ⟨idealExtensionMap_injective I, idealExtensionMap_surjective I⟩

end AlgebraicGeometry.Conormal
