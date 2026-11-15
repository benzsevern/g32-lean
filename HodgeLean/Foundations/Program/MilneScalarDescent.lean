import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Tower

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem m2_ker_baseChange {K L V W : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    LinearMap.ker (f.baseChange L) = (LinearMap.ker f).baseChange L := by
  letI := Module.Free.of_divisionRing K L
  letI : Module.Flat K L := Module.Flat.of_free
  exact Module.Flat.ker_lTensor_eq L L f

theorem m2_ker_baseChange_preimage {K L V W : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    ((LinearMap.ker (f.baseChange L)).restrictScalars K).comap
      (TensorProduct.mk K L V 1) = LinearMap.ker f := by
  letI := Module.Free.of_divisionRing K W
  letI : Module.Flat K W := Module.Flat.of_free
  apply Submodule.ext
  intro x
  change f.baseChange L ((1 : L) ⊗ₜ[K] x) = 0 ↔ f x = 0
  rw [LinearMap.baseChange_tmul]
  constructor
  · intro h
    apply Module.Flat.tensorProduct_mk_injective K W L
    simpa only [TensorProduct.mk_apply, TensorProduct.tmul_zero] using h
  · intro h
    rw [h, TensorProduct.tmul_zero]

theorem m2_kernel_descends {K L V W : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    LinearMap.ker (f.baseChange L) =
      (((LinearMap.ker (f.baseChange L)).restrictScalars K).comap
        (TensorProduct.mk K L V 1)).baseChange L := by
  rw [m2_ker_baseChange_preimage, m2_ker_baseChange]

theorem m2_range_baseChange {K L V W : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    LinearMap.range (f.baseChange L) = (LinearMap.range f).baseChange L := by
  have hq : Function.Surjective (f.rangeRestrict.baseChange L) :=
    LinearMap.lTensor_surjective L f.surjective_rangeRestrict
  calc
    _ = LinearMap.range ((LinearMap.range f).subtype.baseChange L ∘ₗ
        f.rangeRestrict.baseChange L) := by
      rw [← LinearMap.baseChange_comp]
      rfl
    _ = LinearMap.range ((LinearMap.range f).subtype.baseChange L) := by
      rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hq, Submodule.map_top]
    _ = (LinearMap.range f).baseChange L := rfl

theorem m2_map_baseChange {K L V W : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p : Submodule K V) (f : V →ₗ[K] W) :
    (p.baseChange L).map (f.baseChange L) = (p.map f).baseChange L := by
  change (LinearMap.range (p.subtype.baseChange L)).map (f.baseChange L) = _
  rw [← LinearMap.range_comp, ← LinearMap.baseChange_comp, m2_range_baseChange,
    LinearMap.range_comp, Submodule.range_subtype]

theorem m2_baseChange_descends {K L V : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] (p : Submodule K V) :
    p.baseChange L = (((p.baseChange L).restrictScalars K).comap
      (TensorProduct.mk K L V 1)).baseChange L := by
  have hp : p.baseChange L = LinearMap.ker (p.mkQ.baseChange L) := by
    rw [m2_ker_baseChange, Submodule.ker_mkQ]
  rw [hp]
  exact m2_kernel_descends p.mkQ

end HodgeLean.Foundations.Program
