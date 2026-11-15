import Mathlib.LinearAlgebra.Matrix.ToLin
import HodgeLean.Foundations.Program.MilneReducedBaseChange
import HodgeLean.Foundations.Program.MilneScalarDescent
import HodgeLean.Foundations.GeometricIntegralityC

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

theorem m2_scalarPoints_eq_zero {K A L : Type*} [Field K] [PerfectField K]
    [CommRing A] [Algebra K A] [IsReduced A] [Algebra.FiniteType K A]
    [Field L] [IsAlgClosed L] [Algebra K L] (z : L ⊗[K] A)
    (h : ∀ φ : A →ₐ[K] L, m2_scalarEval φ z = 0) : z = 0 := by
  letI : IsReduced (A ⊗[K] L) := m2_tensor_reduced_perfect
  letI : IsReduced (L ⊗[K] A) := isReduced_of_injective
    (Algebra.TensorProduct.comm K L A) (Algebra.TensorProduct.comm K L A).injective
  apply HodgeLean.Foundations.spec_g3b_eq_zero_of_forall_algHom (k := L) z
  intro ψ
  let φ : A →ₐ[K] L := (ψ.restrictScalars K).comp Algebra.TensorProduct.includeRight
  have he : ψ = m2_scalarEval φ := by
    apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · simp only [m2_scalarEval, Algebra.TensorProduct.lift_comp_includeRight]
      rfl
  rw [he]
  exact h φ

def m2_pointTensorEval {K A L W : Type*} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L] [AddCommGroup W] [Module K W] (φ : A →ₐ[K] L) :
    L ⊗[K] (A ⊗[K] W) →ₗ[L] L ⊗[K] W :=
  TensorProduct.AlgebraTensorModule.rTensor K W (m2_scalarEval φ).toLinearMap ∘ₗ
    (TensorProduct.AlgebraTensorModule.assoc K K L L A W).symm.toLinearMap

theorem m2_pointTensorEval_tmul {K A L W : Type*} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L] [AddCommGroup W] [Module K W]
    (φ : A →ₐ[K] L) (c : L) (a : A) (w : W) :
    m2_pointTensorEval φ (c ⊗ₜ[K] (a ⊗ₜ[K] w)) = (c * φ a) ⊗ₜ[K] w := by
  simp only [m2_pointTensorEval, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    TensorProduct.AlgebraTensorModule.assoc_symm_tmul,
    TensorProduct.AlgebraTensorModule.rTensor_tmul, AlgHom.toLinearMap_apply,
    m2_scalarEval_tmul]

theorem m2_pointTensorEval_detects_zero {K A L W : Type*} [Field K] [PerfectField K]
    [CommRing A] [Algebra K A] [IsReduced A] [Algebra.FiniteType K A]
    [Field L] [IsAlgClosed L] [Algebra K L] [AddCommGroup W] [Module K W]
    (z : L ⊗[K] (A ⊗[K] W))
    (h : ∀ φ : A →ₐ[K] L, m2_pointTensorEval φ z = 0) : z = 0 := by
  classical
  letI := Module.Free.of_divisionRing K W
  let e := Module.Free.chooseBasis K W
  let a := TensorProduct.AlgebraTensorModule.assoc K K L L A W
  apply a.symm.injective
  apply (TensorProduct.equivFinsuppOfBasisRight e).injective
  ext i
  simp only [map_zero, Finsupp.zero_apply]
  apply m2_scalarPoints_eq_zero
  intro φ
  have hm := h φ
  change TensorProduct.map ((m2_scalarEval φ).restrictScalars K).toLinearMap
    LinearMap.id (a.symm z) = 0 at hm
  have hc := congrArg (fun t => TensorProduct.equivFinsuppOfBasisRight e t i) hm
  rw [m2_tensor_coordinate_map] at hc
  simp only [map_zero, Finsupp.zero_apply] at hc
  exact hc

theorem m2_point_constraint_kernel {K A L V W : Type*} [Field K] [PerfectField K]
    [CommRing A] [Algebra K A] [IsReduced A] [Algebra.FiniteType K A]
    [Field L] [IsAlgClosed L] [Algebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] A ⊗[K] W) :
    (⨅ φ : A →ₐ[K] L, LinearMap.ker (m2_pointTensorEval φ ∘ₗ f.baseChange L)) =
      LinearMap.ker (f.baseChange L) := by
  apply Submodule.ext
  intro z
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · exact m2_pointTensorEval_detects_zero _
  · intro h φ
    rw [h, map_zero]

theorem m2_point_constraints_descend {K A L V W : Type*} [Field K] [PerfectField K]
    [CommRing A] [Algebra K A] [IsReduced A] [Algebra.FiniteType K A]
    [Field L] [IsAlgClosed L] [Algebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] A ⊗[K] W) :
    (⨅ φ : A →ₐ[K] L, LinearMap.ker (m2_pointTensorEval φ ∘ₗ f.baseChange L)) =
      ((((⨅ φ : A →ₐ[K] L, LinearMap.ker (m2_pointTensorEval φ ∘ₗ f.baseChange L)) :
        Submodule L (L ⊗[K] V)).restrictScalars K).comap
          (TensorProduct.mk K L V 1)).baseChange L := by
  rw [m2_point_constraint_kernel]
  exact m2_kernel_descends f

theorem m2_image_point_constraints_descend {K A L V W Y : Type*} [Field K] [PerfectField K]
    [CommRing A] [Algebra K A] [IsReduced A] [Algebra.FiniteType K A]
    [Field L] [IsAlgClosed L] [Algebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup Y] [Module K Y]
    (f : V →ₗ[K] A ⊗[K] W) (g : V →ₗ[K] Y) :
    ((⨅ φ : A →ₐ[K] L, LinearMap.ker (m2_pointTensorEval φ ∘ₗ f.baseChange L)).map
      (g.baseChange L)) =
      ((((⨅ φ : A →ₐ[K] L, LinearMap.ker (m2_pointTensorEval φ ∘ₗ f.baseChange L)).map
        (g.baseChange L)).restrictScalars K).comap
          (TensorProduct.mk K L Y 1)).baseChange L := by
  rw [m2_point_constraint_kernel, m2_ker_baseChange, m2_map_baseChange]
  exact m2_baseChange_descends _

def m2_coefficientMap {K A V ι : Type*} [Field K] [CommRing A] [Algebra K A]
    [AddCommGroup V] [Module K V] [Fintype ι] (b : Module.Basis ι K V)
    (M : Matrix ι ι A) : V →ₗ[K] A ⊗[K] V :=
  b.constr K fun j => ∑ i, M i j ⊗ₜ[K] b i

theorem m2_coefficientMap_point_basis {K A L V ι : Type*} [Field K]
    [CommRing A] [Algebra K A] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [Fintype ι]
    (b : Module.Basis ι K V) (M : Matrix ι ι A) (φ : A →ₐ[K] L) (j : ι) :
    m2_pointTensorEval φ ((m2_coefficientMap b M).baseChange L ((1 : L) ⊗ₜ[K] b j)) =
      ∑ i, φ (M i j) ⊗ₜ[K] b i := by
  simp only [LinearMap.baseChange_tmul, m2_coefficientMap, Module.Basis.constr_basis,
    TensorProduct.tmul_sum, map_sum, m2_pointTensorEval_tmul, one_mul]

theorem m2_coefficientMap_point_matrix {K A L V ι : Type*} [Field K]
    [CommRing A] [Algebra K A] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (M : Matrix ι ι A) (φ : A →ₐ[K] L) :
    m2_pointTensorEval φ ∘ₗ (m2_coefficientMap b M).baseChange L =
      Matrix.toLin (b.baseChange L) (b.baseChange L) (M.map φ) := by
  apply (b.baseChange L).ext
  intro j
  rw [LinearMap.comp_apply, Matrix.toLin_self]
  simp only [Module.Basis.baseChange_apply, m2_coefficientMap_point_basis,
    Matrix.map_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem m2_scalarEmbedding_point {K A L V : Type*} [Field K]
    [CommRing A] [Algebra K A] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] (φ : A →ₐ[K] L) :
    m2_pointTensorEval φ ∘ₗ (TensorProduct.mk K A V 1).baseChange L = LinearMap.id := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c v
  simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, TensorProduct.mk_apply,
    m2_pointTensorEval_tmul, map_one, mul_one, LinearMap.id_apply]

def m2_operatorConstraint {K A V ι : Type*} [Field K] [CommRing A] [Algebra K A]
    [AddCommGroup V] [Module K V] [Fintype ι] (b : Module.Basis ι K V)
    (M : Matrix ι ι A) : V →ₗ[K] A ⊗[K] V :=
  m2_coefficientMap b M - TensorProduct.mk K A V 1

theorem m2_operatorConstraint_point {K A L V ι : Type*} [Field K]
    [CommRing A] [Algebra K A] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (M : Matrix ι ι A) (φ : A →ₐ[K] L) :
    m2_pointTensorEval φ ∘ₗ (m2_operatorConstraint b M).baseChange L =
      Matrix.toLin (b.baseChange L) (b.baseChange L) (M.map φ) - LinearMap.id := by
  simp only [m2_operatorConstraint, LinearMap.baseChange_sub, LinearMap.comp_sub,
    m2_coefficientMap_point_matrix, m2_scalarEmbedding_point]

theorem m2_matrix_invariant_images_descend {K A L V Y ι : Type*}
    [Field K] [PerfectField K] [CommRing A] [Algebra K A] [IsReduced A]
    [Algebra.FiniteType K A] [Field L] [IsAlgClosed L] [Algebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup Y] [Module K Y]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (M : Matrix ι ι A) (g : V →ₗ[K] Y) :
    ((⨅ φ : A →ₐ[K] L, LinearMap.eqLocus
      (Matrix.toLin (b.baseChange L) (b.baseChange L) (M.map φ)) LinearMap.id).map
        (g.baseChange L)) =
      ((((⨅ φ : A →ₐ[K] L, LinearMap.eqLocus
        (Matrix.toLin (b.baseChange L) (b.baseChange L) (M.map φ)) LinearMap.id).map
          (g.baseChange L)).restrictScalars K).comap
            (TensorProduct.mk K L Y 1)).baseChange L := by
  simpa only [m2_operatorConstraint_point, ← LinearMap.eqLocus_eq_ker_sub]
    using m2_image_point_constraints_descend (L := L) (m2_operatorConstraint b M) g

end HodgeLean.Foundations.Program
