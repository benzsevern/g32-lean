import HodgeLean.Foundations.GeometricIntegrality
import Mathlib.RingTheory.Unramified.Field
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
open Module
namespace HodgeLean.Foundations.Program

theorem m2_tensor_coordinate_map {K A B L ι : Type*} [Field K]
    [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [AddCommGroup L] [Module K L] [DecidableEq ι] (e : Basis ι K L) (φ : A →ₐ[K] B)
    (z : A ⊗[K] L) (i : ι) :
    TensorProduct.equivFinsuppOfBasisRight e
      (TensorProduct.map φ.toLinearMap LinearMap.id z) i =
      φ (TensorProduct.equivFinsuppOfBasisRight e z i) := by
  classical
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul a b =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]

theorem m2_tensor_reduced_finite_separable {K A L : Type*} [Field K]
    [CommRing A] [Algebra K A] [IsReduced A] [Field L] [Algebra K L]
    [Module.Finite K L] [Algebra.IsSeparable K L] : IsReduced (A ⊗[K] L) := by
  classical
  letI := Module.Free.of_divisionRing K L
  let e := Module.Free.chooseBasis K L
  constructor
  intro z hz
  apply (TensorProduct.equivFinsuppOfBasisRight e).injective
  ext i
  simp only [map_zero, Finsupp.zero_apply]
  apply IsNilpotent.eq_zero
  apply nilpotent_iff_mem_prime.mpr
  intro p hp
  letI : p.IsPrime := hp
  let f : A →ₐ[K] p.ResidueField := IsScalarTower.toAlgHom K A p.ResidueField
  letI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  letI : IsReduced (p.ResidueField ⊗[K] L) :=
    Algebra.FormallyUnramified.isReduced_of_field p.ResidueField (p.ResidueField ⊗[K] L)
  have hm : TensorProduct.map f.toLinearMap LinearMap.id z = 0 :=
    IsNilpotent.eq_zero (hz.map (Algebra.TensorProduct.map f (AlgHom.id K L)))
  apply (p.algebraMap_residueField_eq_zero).mp
  change f (TensorProduct.equivFinsuppOfBasisRight e z i) = 0
  rw [← m2_tensor_coordinate_map e f z i, hm, map_zero, Finsupp.zero_apply]

theorem m2_tensor_reduced_algebraic {K A L : Type*} [Field K] [PerfectField K]
    [CommRing A] [Algebra K A] [IsReduced A] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] : IsReduced (A ⊗[K] L) := by
  letI := Module.Free.of_divisionRing K A
  letI : Module.Flat K A := Module.Flat.of_free
  apply IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  letI : Field B := (B.isField_of_algebraic).toField
  letI : Algebra.FiniteType K B := B.fg_iff_finiteType.mp hB
  letI : Module.Finite K B := finite_of_finite_type_of_isJacobsonRing K B
  exact m2_tensor_reduced_finite_separable

theorem m2_tensor_reduced_algClosed {K A L : Type*} [Field K] [IsAlgClosed K]
    [CommRing A] [Algebra K A] [IsReduced A] [Algebra.FiniteType K A]
    [Field L] [Algebra K L] : IsReduced (A ⊗[K] L) := by
  classical
  letI := Module.Free.of_divisionRing K L
  let e := Module.Free.chooseBasis K L
  constructor
  intro z hz
  apply (TensorProduct.equivFinsuppOfBasisRight e).injective
  ext i
  simp only [map_zero, Finsupp.zero_apply]
  apply IsNilpotent.eq_zero
  apply nilpotent_iff_mem_prime.mpr
  intro p hp
  letI : p.IsPrime := hp
  let f : A →ₐ[K] A ⧸ p := Ideal.Quotient.mkₐ K p
  letI : IsDomain ((A ⧸ p) ⊗[K] L) :=
    HodgeLean.Foundations.isDomain_tensorProduct_of_isAlgClosed K (A ⧸ p) L
  have hm : TensorProduct.map f.toLinearMap LinearMap.id z = 0 :=
    IsNilpotent.eq_zero (hz.map (Algebra.TensorProduct.map f (AlgHom.id K L)))
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change f (TensorProduct.equivFinsuppOfBasisRight e z i) = 0
  rw [← m2_tensor_coordinate_map e f z i, hm, map_zero, Finsupp.zero_apply]

theorem m2_tensor_reduced_perfect {K A L : Type*} [Field K] [PerfectField K]
    [CommRing A] [Algebra K A] [IsReduced A] [Algebra.FiniteType K A]
    [Field L] [IsAlgClosed L] [Algebra K L] : IsReduced (A ⊗[K] L) := by
  let F := AlgebraicClosure K
  let f : F →ₐ[K] L := IsAlgClosed.lift
  letI : Algebra F L := f.toRingHom.toAlgebra
  letI : IsScalarTower K F L := IsScalarTower.of_algHom f
  letI : IsReduced (A ⊗[K] F) := m2_tensor_reduced_algebraic
  letI : IsReduced (F ⊗[K] A) := isReduced_of_injective
    (Algebra.TensorProduct.comm K F A) (Algebra.TensorProduct.comm K F A).injective
  letI : IsReduced ((F ⊗[K] A) ⊗[F] L) := m2_tensor_reduced_algClosed
  let e : (A ⊗[K] L) ≃+* ((F ⊗[K] A) ⊗[F] L) :=
    (Algebra.TensorProduct.comm K A L).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange K F F L A).symm.toRingEquiv.trans
        (Algebra.TensorProduct.comm F L (F ⊗[K] A)).toRingEquiv)
  exact isReduced_of_injective e e.injective

def m2_scalarEval {K A L : Type*} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L] (φ : A →ₐ[K] L) : (L ⊗[K] A) →ₐ[L] L :=
  Algebra.TensorProduct.lift (AlgHom.id L L) φ (fun _ _ => Commute.all _ _)

theorem m2_scalarEval_tmul {K A L : Type*} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L] (φ : A →ₐ[K] L) (c : L) (a : A) :
    m2_scalarEval φ (c ⊗ₜ[K] a) = c * φ a := by
  simp only [m2_scalarEval, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply]

end HodgeLean.Foundations.Program
