import HodgeLean.Foundations.Program.SchoenTowerI2aReesFields
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.BaseChange

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

/-- Flat coefficient extension embeds the actual Rees fraction algebra into
the corresponding coefficient localization and preserves every specified ratio.
Source: Mathlib, `Module.Flat.lTensor_preserves_injective_linearMap`,
`IsLocalization.tensor` and `IsLocalization.algEquiv`. -/
theorem s2v_i2a_flat_rees_tensor_embedding
    (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (I : Ideal R) (x : R) :
    ∃ φ : S ⊗[R] s2t_reesChart I x →ₐ[S] Localization.Away (algebraMap R S x),
      Function.Injective φ ∧
      (∀ r, φ ((1 : S) ⊗ₜ[R] algebraMap R (s2t_reesChart I x) r) =
        algebraMap S _ (algebraMap R S r)) ∧
      ∀ y : I, φ ((1 : S) ⊗ₜ[R] s2v_i2a_reesFraction I x y) =
        algebraMap S _ (algebraMap R S y.val) * IsLocalization.Away.invSelf (algebraMap R S x) := by
  let C := s2t_reesChart I x
  let L := Localization.Away x
  let L' := Localization.Away (algebraMap R S x)
  let M := Algebra.algebraMapSubmonoid S (Submonoid.powers x)
  let e : S ⊗[R] L ≃ₐ[S] L' := IsLocalization.algEquiv M _ _
  let g : S ⊗[R] C →ₐ[S] S ⊗[R] L :=
    Algebra.TensorProduct.map (AlgHom.id S S) C.val
  have hg : Function.Injective g := by
    exact Module.Flat.lTensor_preserves_injective_linearMap C.val.toLinearMap Subtype.val_injective
  let φ := e.toAlgHom.comp g
  have hbase (r : R) : φ ((1 : S) ⊗ₜ[R] algebraMap R C r) =
      algebraMap S L' (algebraMap R S r) := by
    rw [← Algebra.TensorProduct.algebraMap_apply']
    exact (φ.restrictScalars R).commutes r
  refine ⟨φ, e.injective.comp hg, hbase, ?_⟩
  intro y
  let q : C →ₐ[R] L' := (φ.restrictScalars R).comp Algebra.TensorProduct.includeRight
  have hratio : s2v_i2a_reesFraction I x y * algebraMap R C x = algebraMap R C y.val := by
    apply Subtype.ext
    change (algebraMap R L y.val * IsLocalization.Away.invSelf x) * algebraMap R L x = _
    rw [mul_right_comm, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
    rfl
  have H := congrArg q hratio
  rw [map_mul] at H
  change φ ((1 : S) ⊗ₜ[R] s2v_i2a_reesFraction I x y) *
    φ ((1 : S) ⊗ₜ[R] algebraMap R C x) = φ ((1 : S) ⊗ₜ[R] algebraMap R C y.val) at H
  rw [hbase, hbase] at H
  apply (IsLocalization.Away.algebraMap_isUnit (algebraMap R S x)).mul_right_cancel
  rw [H, mul_right_comm, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]

end HodgeLean.Foundations.Program
