import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Nullstellensatz
import HodgeLean.Foundations.Program.MilnePolynomialPoints

noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

theorem m2_isUnit_of_form_preserving {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] (E : LinearMap.BilinForm K V) (hE : E.Nondegenerate)
    (u : Module.End K V) (hu : ∀ x y, E (u x) (u y) = E x y) : IsUnit u := by
  apply (Module.End.isUnit_iff u).mpr
  have hi : Function.Injective u := by
    intro x y h
    apply sub_eq_zero.mp
    apply hE.1
    intro z
    rw [← hu, map_sub, h, sub_self, map_zero, LinearMap.zero_apply]
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

def m2_pointMatrix {L d : Type*} (x : d × d → L) : Matrix d d L := fun i j => x (i, j)

def m2_commutatorPolynomial {K d : Type*} [Field K] [Fintype d]
    (T : Matrix d d K) (i j : d) : MvPolynomial (d × d) K :=
  (∑ k, MvPolynomial.X (i, k) * MvPolynomial.C (T k j)) -
    ∑ k, MvPolynomial.C (T i k) * MvPolynomial.X (k, j)

theorem m2_commutatorPolynomial_eval {K L d : Type*} [Field K] [Field L] [Algebra K L]
    [Fintype d] (T : Matrix d d K) (x : d × d → L) (i j : d) :
    MvPolynomial.aeval x (m2_commutatorPolynomial T i j) =
      (m2_pointMatrix x * T.map (algebraMap K L) -
        T.map (algebraMap K L) * m2_pointMatrix x) i j := by
  simp only [m2_commutatorPolynomial, map_sub, map_sum, map_mul,
    MvPolynomial.aeval_X, MvPolynomial.aeval_C, Matrix.sub_apply,
    Matrix.mul_apply, Matrix.map_apply, m2_pointMatrix]

def m2_isometryPolynomial {K d : Type*} [Field K] [Fintype d]
    (E : Matrix d d K) (i j : d) : MvPolynomial (d × d) K :=
  (∑ k, (∑ l, MvPolynomial.X (l, i) * MvPolynomial.C (E l k)) *
    MvPolynomial.X (k, j)) - MvPolynomial.C (E i j)

theorem m2_isometryPolynomial_eval {K L d : Type*} [Field K] [Field L] [Algebra K L]
    [Fintype d] (E : Matrix d d K) (x : d × d → L) (i j : d) :
    MvPolynomial.aeval x (m2_isometryPolynomial E i j) =
      ((m2_pointMatrix x).transpose * E.map (algebraMap K L) * m2_pointMatrix x -
        E.map (algebraMap K L)) i j := by
  simp only [m2_isometryPolynomial, map_sub, map_sum, map_mul,
    MvPolynomial.aeval_X, MvPolynomial.aeval_C, Matrix.sub_apply,
    Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, m2_pointMatrix]

def m2_matrixCoordinateIdeal {K d ι : Type*} [Field K] [Fintype d]
    (E : Matrix d d K) (T : ι → Matrix d d K) : Ideal (MvPolynomial (d × d) K) :=
  (Ideal.span (Set.range (fun q : ι × d × d =>
    m2_commutatorPolynomial (T q.1) q.2.1 q.2.2) ∪
      Set.range (fun q : d × d => m2_isometryPolynomial E q.1 q.2))).radical

theorem m2_commutatorPolynomial_mem {K d ι : Type*} [Field K] [Fintype d]
    (E : Matrix d d K) (T : ι → Matrix d d K) (s : ι) (i j : d) :
    m2_commutatorPolynomial (T s) i j ∈ m2_matrixCoordinateIdeal E T := by
  apply Ideal.le_radical
  apply Ideal.subset_span
  exact Or.inl ⟨(s, i, j), rfl⟩

theorem m2_isometryPolynomial_mem {K d ι : Type*} [Field K] [Fintype d]
    (E : Matrix d d K) (T : ι → Matrix d d K) (i j : d) :
    m2_isometryPolynomial E i j ∈ m2_matrixCoordinateIdeal E T := by
  apply Ideal.le_radical
  apply Ideal.subset_span
  exact Or.inr ⟨(i, j), rfl⟩

theorem m2_matrixCoordinate_reduced {K d ι : Type*} [Field K] [Fintype d]
    (E : Matrix d d K) (T : ι → Matrix d d K) :
    IsReduced (MvPolynomial (d × d) K ⧸ m2_matrixCoordinateIdeal E T) := by
  apply (Ideal.isRadical_iff_quotient_reduced _).mp
  exact Ideal.radical_isRadical _

theorem m2_matrixCoordinatePoint_commutes {K L d ι : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype d] (E : Matrix d d K) (T : ι → Matrix d d K)
    (φ : (MvPolynomial (d × d) K ⧸ m2_matrixCoordinateIdeal E T) →ₐ[K] L) (s : ι) :
    m2_pointMatrix (m2_coordinatePoint (m2_matrixCoordinateIdeal E T) φ) *
      (T s).map (algebraMap K L) =
    (T s).map (algebraMap K L) *
      m2_pointMatrix (m2_coordinatePoint (m2_matrixCoordinateIdeal E T) φ) := by
  ext i j
  have h := m2_coordinatePoint_mem_zeroLocus (m2_matrixCoordinateIdeal E T) φ
    (m2_commutatorPolynomial (T s) i j) (m2_commutatorPolynomial_mem E T s i j)
  rw [m2_commutatorPolynomial_eval] at h
  exact sub_eq_zero.mp h

theorem m2_matrixCoordinatePoint_isometry {K L d ι : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype d] (E : Matrix d d K) (T : ι → Matrix d d K)
    (φ : (MvPolynomial (d × d) K ⧸ m2_matrixCoordinateIdeal E T) →ₐ[K] L) :
    (m2_pointMatrix (m2_coordinatePoint (m2_matrixCoordinateIdeal E T) φ)).transpose *
      E.map (algebraMap K L) *
        m2_pointMatrix (m2_coordinatePoint (m2_matrixCoordinateIdeal E T) φ) =
      E.map (algebraMap K L) := by
  ext i j
  have h := m2_coordinatePoint_mem_zeroLocus (m2_matrixCoordinateIdeal E T) φ
    (m2_isometryPolynomial E i j) (m2_isometryPolynomial_mem E T i j)
  rw [m2_isometryPolynomial_eval] at h
  exact sub_eq_zero.mp h

theorem m2_matrixPoint_mem_zeroLocus {K L d ι : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype d] (E : Matrix d d K) (T : ι → Matrix d d K)
    (x : d × d → L)
    (hcomm : ∀ s, m2_pointMatrix x * (T s).map (algebraMap K L) =
      (T s).map (algebraMap K L) * m2_pointMatrix x)
    (hiso : (m2_pointMatrix x).transpose * E.map (algebraMap K L) * m2_pointMatrix x =
      E.map (algebraMap K L)) :
    x ∈ MvPolynomial.zeroLocus L (m2_matrixCoordinateIdeal E T) := by
  have hspan : Ideal.span (Set.range (fun q : ι × d × d =>
      m2_commutatorPolynomial (T q.1) q.2.1 q.2.2) ∪
      Set.range (fun q : d × d => m2_isometryPolynomial E q.1 q.2)) ≤
      RingHom.ker (MvPolynomial.aeval x) := by
    apply Ideal.span_le.mpr
    rintro p (⟨q, rfl⟩ | ⟨q, rfl⟩)
    · change MvPolynomial.aeval x (m2_commutatorPolynomial (T q.1) q.2.1 q.2.2) = 0
      rw [m2_commutatorPolynomial_eval, hcomm, sub_self, Matrix.zero_apply]
    · change MvPolynomial.aeval x (m2_isometryPolynomial E q.1 q.2) = 0
      rw [m2_isometryPolynomial_eval, hiso, sub_self, Matrix.zero_apply]
  rintro p ⟨n, hn⟩
  have hp : MvPolynomial.aeval x (p ^ n) = 0 := hspan hn
  exact IsNilpotent.eq_zero ⟨n, by simpa only [map_pow] using hp⟩

theorem m2_formMatrix_baseChange {K L V ι : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (E : LinearMap.BilinForm K V) :
    LinearMap.BilinForm.toMatrix (b.baseChange L) (E.baseChange L) =
      (LinearMap.BilinForm.toMatrix b E).map (algebraMap K L) := by
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, Module.Basis.baseChange_apply,
    LinearMap.BilinForm.baseChange_tmul, Matrix.map_apply, one_mul,
    Algebra.smul_def, mul_one]

theorem m2_linearMatrix_baseChange {K L V ι : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (f : V →ₗ[K] V) :
    LinearMap.toMatrix (b.baseChange L) (b.baseChange L) (f.baseChange L) =
      (LinearMap.toMatrix b b f).map (algebraMap K L) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Basis.baseChange_apply,
    LinearMap.baseChange_tmul, Module.Basis.baseChange_repr_tmul,
    Matrix.map_apply, Algebra.smul_def, mul_one]

def m2_formCoordinateIdeal {K V d ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype d] [DecidableEq d] (b : Module.Basis d K V) (E : LinearMap.BilinForm K V)
    (T : ι → Module.End K V) : Ideal (MvPolynomial (d × d) K) :=
  m2_matrixCoordinateIdeal (LinearMap.BilinForm.toMatrix b E)
    (fun s => LinearMap.toMatrix b b (T s))

def m2_coordinateEnd {K L V d ι : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [Fintype d] [DecidableEq d]
    (b : Module.Basis d K V) (E : LinearMap.BilinForm K V) (T : ι → Module.End K V)
    (φ : (MvPolynomial (d × d) K ⧸ m2_formCoordinateIdeal b E T) →ₐ[K] L) :
    Module.End L (L ⊗[K] V) :=
  Matrix.toLin (b.baseChange L) (b.baseChange L)
    (m2_pointMatrix (m2_coordinatePoint (m2_formCoordinateIdeal b E T) φ))

theorem m2_coordinateEnd_matrix {K L V d ι : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [Fintype d] [DecidableEq d]
    (b : Module.Basis d K V) (E : LinearMap.BilinForm K V) (T : ι → Module.End K V)
    (φ : (MvPolynomial (d × d) K ⧸ m2_formCoordinateIdeal b E T) →ₐ[K] L) :
    LinearMap.toMatrix (b.baseChange L) (b.baseChange L) (m2_coordinateEnd b E T φ) =
      m2_pointMatrix (m2_coordinatePoint (m2_formCoordinateIdeal b E T) φ) := by
  simp only [m2_coordinateEnd, LinearMap.toMatrix_toLin]

theorem m2_coordinateEnd_commutes {K L V d ι : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [Fintype d] [DecidableEq d]
    (b : Module.Basis d K V) (E : LinearMap.BilinForm K V) (T : ι → Module.End K V)
    (φ : (MvPolynomial (d × d) K ⧸ m2_formCoordinateIdeal b E T) →ₐ[K] L) (s : ι) :
    m2_coordinateEnd b E T φ ∘ₗ (T s).baseChange L =
      (T s).baseChange L ∘ₗ m2_coordinateEnd b E T φ := by
  apply (LinearMap.toMatrix (b.baseChange L) (b.baseChange L)).injective
  simp only [LinearMap.toMatrix_comp (b.baseChange L) (b.baseChange L) (b.baseChange L),
    m2_coordinateEnd_matrix, m2_linearMatrix_baseChange]
  exact m2_matrixCoordinatePoint_commutes (LinearMap.BilinForm.toMatrix b E)
    (fun t => LinearMap.toMatrix b b (T t)) φ s

theorem m2_coordinateEnd_isometry {K L V d ι : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [Fintype d] [DecidableEq d]
    (b : Module.Basis d K V) (E : LinearMap.BilinForm K V) (T : ι → Module.End K V)
    (φ : (MvPolynomial (d × d) K ⧸ m2_formCoordinateIdeal b E T) →ₐ[K] L) :
    ∀ x y, E.baseChange L (m2_coordinateEnd b E T φ x) (m2_coordinateEnd b E T φ y) =
      E.baseChange L x y := by
  have he : (E.baseChange L).comp (m2_coordinateEnd b E T φ)
      (m2_coordinateEnd b E T φ) = E.baseChange L := by
    apply (LinearMap.BilinForm.toMatrix (b.baseChange L)).injective
    rw [LinearMap.BilinForm.toMatrix_comp (b.baseChange L) (b.baseChange L),
      m2_coordinateEnd_matrix, m2_formMatrix_baseChange]
    exact m2_matrixCoordinatePoint_isometry (LinearMap.BilinForm.toMatrix b E)
      (fun t => LinearMap.toMatrix b b (T t)) φ
  intro x y
  exact congrArg (fun B : LinearMap.BilinForm L (L ⊗[K] V) => B x y) he

theorem m2_coordinateEnd_isUnit {K L V d ι : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [Fintype d] [DecidableEq d]
    (b : Module.Basis d K V) (E : LinearMap.BilinForm K V) (T : ι → Module.End K V)
    (hE : (E.baseChange L).Nondegenerate)
    (φ : (MvPolynomial (d × d) K ⧸ m2_formCoordinateIdeal b E T) →ₐ[K] L) :
    IsUnit (m2_coordinateEnd b E T φ) := by
  letI : Module.Finite L (L ⊗[K] V) := Module.Finite.of_basis (b.baseChange L)
  exact m2_isUnit_of_form_preserving _ hE _ (m2_coordinateEnd_isometry b E T φ)

theorem m2_exists_coordinateEnd {K L V d ι : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [Fintype d] [DecidableEq d]
    (b : Module.Basis d K V) (E : LinearMap.BilinForm K V) (T : ι → Module.End K V)
    (u : Module.End L (L ⊗[K] V))
    (hcomm : ∀ s, u ∘ₗ (T s).baseChange L = (T s).baseChange L ∘ₗ u)
    (hiso : ∀ x y, E.baseChange L (u x) (u y) = E.baseChange L x y) :
    ∃ φ : (MvPolynomial (d × d) K ⧸ m2_formCoordinateIdeal b E T) →ₐ[K] L,
      m2_coordinateEnd b E T φ = u := by
  let bL := b.baseChange L
  let x : d × d → L := fun ij => LinearMap.toMatrix bL bL u ij.1 ij.2
  have hxcomm (s : ι) : m2_pointMatrix x *
      (LinearMap.toMatrix b b (T s)).map (algebraMap K L) =
      (LinearMap.toMatrix b b (T s)).map (algebraMap K L) * m2_pointMatrix x := by
    have h := congrArg (LinearMap.toMatrix bL bL) (hcomm s)
    dsimp [bL] at h
    simp only [LinearMap.toMatrix_comp (b.baseChange L) (b.baseChange L) (b.baseChange L), m2_linearMatrix_baseChange] at h
    exact h
  have he : (E.baseChange L).comp u u = E.baseChange L := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact hiso v w
  have hxiso : (m2_pointMatrix x).transpose *
      (LinearMap.BilinForm.toMatrix b E).map (algebraMap K L) * m2_pointMatrix x =
      (LinearMap.BilinForm.toMatrix b E).map (algebraMap K L) := by
    have h := congrArg (LinearMap.BilinForm.toMatrix bL) he
    dsimp [bL] at h
    simp only [LinearMap.BilinForm.toMatrix_comp (b.baseChange L) (b.baseChange L), m2_formMatrix_baseChange] at h
    exact h
  have hx := m2_matrixPoint_mem_zeroLocus (LinearMap.BilinForm.toMatrix b E)
    (fun s => LinearMap.toMatrix b b (T s)) x hxcomm hxiso
  refine ⟨m2_quotientEval _ x hx, ?_⟩
  apply (LinearMap.toMatrix bL bL).injective
  rw [m2_coordinateEnd_matrix]
  exact congrArg m2_pointMatrix (m2_quotientEval_coordinates _ x hx)


end HodgeLean.Foundations.Program
