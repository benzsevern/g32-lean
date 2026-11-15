import HodgeLean.Foundations.Program.MilnePolynomialPoints
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.Algebra.MvPolynomial.Eval

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

def m2_piBasis {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {d : ℕ}
    (b : Module.Basis (Fin d) K V) (r : ℕ) : Module.Basis (Fin (d * r)) K (Fin r → V) :=
  ((b.tensorProduct (Pi.basisFun K (Fin r))).map
    (TensorProduct.piScalarRight K K V (Fin r))).reindex finProdFinEquiv

theorem m2_piBasis_apply {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {d : ℕ}
    (b : Module.Basis (Fin d) K V) (r : ℕ) (j : Fin (d * r)) :
    m2_piBasis b r j = Pi.single (finProdFinEquiv.symm j).2 (b (finProdFinEquiv.symm j).1) := by
  classical
  simp only [m2_piBasis, Module.Basis.reindex_apply, Module.Basis.map_apply,
    Module.Basis.tensorProduct_apply, Pi.basisFun_apply]
  ext i
  simp [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Pi.single_apply]

def m2_diagonalMatrixPolynomial {K : Type*} [Field K] (d r : ℕ) :
    Matrix (Fin (d * r)) (Fin (d * r)) (MvPolynomial (Fin d × Fin d) K) :=
  fun i j => if (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm j).2 then
    MvPolynomial.X ((finProdFinEquiv.symm i).1, (finProdFinEquiv.symm j).1) else 0

theorem m2_diagonalMatrixPolynomial_eval {K L : Type*} [Field K] [Field L] [Algebra K L]
    (d r : ℕ) (x : Fin d × Fin d → L) (i j : Fin (d * r)) :
    MvPolynomial.aeval x (m2_diagonalMatrixPolynomial (K := K) d r i j) =
      if (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm j).2 then
        x ((finProdFinEquiv.symm i).1, (finProdFinEquiv.symm j).1) else 0 := by
  unfold m2_diagonalMatrixPolynomial
  split_ifs <;> simp only [MvPolynomial.aeval_X, map_zero]

def m2_diagonalMatrix {R : Type*} [Zero R] (d r : ℕ)
    (U : Matrix (Fin d) (Fin d) R) : Matrix (Fin (d * r)) (Fin (d * r)) R :=
  fun i j => if (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm j).2 then
    U (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 else 0

theorem m2_diagonalMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d r : ℕ) (U : Matrix (Fin d) (Fin d) R) :
    (m2_diagonalMatrix d r U).map f = m2_diagonalMatrix d r (U.map f) := by
  ext i j
  simp only [Matrix.map_apply, m2_diagonalMatrix]
  split_ifs <;> simp only [map_zero]

def m2_exteriorMatrix {R : Type*} [CommRing R] (d r n : ℕ)
    (U : Matrix (Fin d) (Fin d) R) :
    Matrix (Set.powersetCard (Fin (d * r)) n) (Set.powersetCard (Fin (d * r)) n) R :=
  fun s t => Matrix.det (fun i j : Fin n => m2_diagonalMatrix d r U
    (Set.powersetCard.ofFinEmbEquiv.symm s j) (Set.powersetCard.ofFinEmbEquiv.symm t i))

theorem m2_exteriorMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (d r n : ℕ) (U : Matrix (Fin d) (Fin d) R) :
    (m2_exteriorMatrix d r n U).map f = m2_exteriorMatrix d r n (U.map f) := by
  ext s t
  let M : Matrix (Fin n) (Fin n) R := fun i j => m2_diagonalMatrix d r U
    (Set.powersetCard.ofFinEmbEquiv.symm s j) (Set.powersetCard.ofFinEmbEquiv.symm t i)
  have hm : M.map f = (fun i j : Fin n => m2_diagonalMatrix d r (U.map f)
      (Set.powersetCard.ofFinEmbEquiv.symm s j) (Set.powersetCard.ofFinEmbEquiv.symm t i)) := by
    ext i j
    exact congrFun (congrFun (m2_diagonalMatrix_map f d r U)
      (Set.powersetCard.ofFinEmbEquiv.symm s j)) (Set.powersetCard.ofFinEmbEquiv.symm t i)
  exact (f.map_det M).trans (congrArg Matrix.det hm)

theorem m2_piBasis_coordinate {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {d : ℕ}
    (b : Module.Basis (Fin d) K V) (r : ℕ) (v : Fin r → V) (i : Fin (d * r)) :
    (m2_piBasis b r).repr v i =
      b.repr (v (finProdFinEquiv.symm i).2) (finProdFinEquiv.symm i).1 := by
  classical
  let c : (Fin r → V) →ₗ[K] K := b.coord (finProdFinEquiv.symm i).1 ∘ₗ
    LinearMap.proj (finProdFinEquiv.symm i).2
  have hc : c = (m2_piBasis b r).coord i := by
    apply (m2_piBasis b r).ext
    intro j
    change c (m2_piBasis b r j) = (m2_piBasis b r).repr (m2_piBasis b r j) i
    rw [Module.Basis.repr_self]
    simp only [c, LinearMap.comp_apply, LinearMap.proj_apply, m2_piBasis_apply,
      Module.Basis.coord_apply, Pi.single_apply]
    by_cases hji : j = i
    · subst j
      simp only [ite_true, Module.Basis.repr_self, Finsupp.single_eq_same]
    · by_cases hm : (finProdFinEquiv.symm j).2 = (finProdFinEquiv.symm i).2
      · by_cases hb : (finProdFinEquiv.symm j).1 = (finProdFinEquiv.symm i).1
        · exact (hji (finProdFinEquiv.symm.injective (Prod.ext hb hm))).elim
        · rw [if_pos hm.symm]
          simp only [Module.Basis.repr_self, Finsupp.single_apply,
            if_neg hb, if_neg (Ne.symm hb), if_neg hji, if_neg (Ne.symm hji)]
      · rw [if_neg (Ne.symm hm)]
        simp only [map_zero, Finsupp.zero_apply, Finsupp.single_apply,
          if_neg hji, if_neg (Ne.symm hji)]
  exact (LinearMap.congr_fun hc v).symm

def m2_diagonalEnd {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (r : ℕ) (u : Module.End K V) : Module.End K (Fin r → V) :=
  LinearMap.pi fun i => u ∘ₗ LinearMap.proj i

theorem m2_diagonalEnd_matrix {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {d : ℕ}
    (b : Module.Basis (Fin d) K V) (r : ℕ) (u : Module.End K V) :
    LinearMap.toMatrix (m2_piBasis b r) (m2_piBasis b r) (m2_diagonalEnd r u) =
      m2_diagonalMatrix d r (LinearMap.toMatrix b b u) := by
  ext i j
  rw [LinearMap.toMatrix_apply, m2_piBasis_coordinate, m2_piBasis_apply]
  simp only [m2_diagonalEnd, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, m2_diagonalMatrix, Pi.single_apply]
  split_ifs <;> simp only [LinearMap.toMatrix_apply, map_zero, Finsupp.zero_apply]

theorem m2_exteriorEnd_matrix {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {d : ℕ}
    (b : Module.Basis (Fin d) K V) (r n : ℕ) (u : Module.End K V) :
    LinearMap.toMatrix ((m2_piBasis b r).exteriorPower n) ((m2_piBasis b r).exteriorPower n)
      (exteriorPower.map n (m2_diagonalEnd r u)) =
      m2_exteriorMatrix d r n (LinearMap.toMatrix b b u) := by
  ext s t
  rw [LinearMap.toMatrix_apply, exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family]
  simp only [exteriorPower.ιMulti_family, Function.comp_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  change Matrix.det (fun i j : Fin n => (m2_piBasis b r).coord
    (Set.powersetCard.ofFinEmbEquiv.symm s j)
    (m2_diagonalEnd r u (m2_piBasis b r (Set.powersetCard.ofFinEmbEquiv.symm t i)))) = _
  apply congrArg (fun M : Matrix (Fin n) (Fin n) K => M.det)
  ext i j
  exact (LinearMap.toMatrix_apply (m2_piBasis b r) (m2_piBasis b r) (m2_diagonalEnd r u)
    (Set.powersetCard.ofFinEmbEquiv.symm s j) (Set.powersetCard.ofFinEmbEquiv.symm t i)).symm.trans
      (congrFun (congrFun (m2_diagonalEnd_matrix b r u)
        (Set.powersetCard.ofFinEmbEquiv.symm s j)) (Set.powersetCard.ofFinEmbEquiv.symm t i))

def m2_exteriorMatrixPolynomial {K : Type*} [Field K] (d r n : ℕ) :
    Matrix (Set.powersetCard (Fin (d * r)) n) (Set.powersetCard (Fin (d * r)) n)
      (MvPolynomial (Fin d × Fin d) K) :=
  m2_exteriorMatrix d r n (fun i j => MvPolynomial.X (i, j))

theorem m2_exteriorMatrixPolynomial_eval {K L : Type*} [Field K] [Field L] [Algebra K L]
    (d r n : ℕ) (x : Fin d × Fin d → L) :
    (m2_exteriorMatrixPolynomial (K := K) d r n).map (MvPolynomial.aeval x) =
      m2_exteriorMatrix d r n (fun i j => x (i, j)) := by
  exact (m2_exteriorMatrix_map (MvPolynomial.aeval (R := K) x).toRingHom d r n
    (fun i j => MvPolynomial.X (i, j))).trans (by congr 1; ext i j; exact MvPolynomial.aeval_X x (i, j))

theorem m2_basisEquiv_intertwines {K V W ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (c : Module.Basis ι K W)
    (M : Matrix ι ι K) :
    (b.equiv c (Equiv.refl ι)).toLinearMap ∘ₗ Matrix.toLin b b M =
      Matrix.toLin c c M ∘ₗ (b.equiv c (Equiv.refl ι)).toLinearMap := by
  apply (LinearMap.toMatrix b c).injective
  simp only [LinearMap.toMatrix_comp b b c, LinearMap.toMatrix_comp b c c,
    LinearMap.toMatrix_basis_equiv, LinearMap.toMatrix_toLin, Matrix.one_mul, Matrix.mul_one]


theorem m2_exteriorMatrixQuotient_eval {K L : Type*} [Field K] [Field L] [Algebra K L]
    (d r n : ℕ) (I : Ideal (MvPolynomial (Fin d × Fin d) K))
    (φ : (MvPolynomial (Fin d × Fin d) K ⧸ I) →ₐ[K] L) :
    ((m2_exteriorMatrixPolynomial (K := K) d r n).map (Ideal.Quotient.mkₐ K I)).map φ =
      m2_exteriorMatrix d r n (fun i j => m2_coordinatePoint I φ (i, j)) := by
  have h : ((m2_exteriorMatrixPolynomial (K := K) d r n).map
      (Ideal.Quotient.mkₐ K I)).map φ =
      (m2_exteriorMatrixPolynomial (K := K) d r n).map
        (MvPolynomial.aeval (m2_coordinatePoint I φ)) := by
    rw [m2_coordinatePoint_eval]
    rfl
  exact h.trans (m2_exteriorMatrixPolynomial_eval d r n _)


end HodgeLean.Foundations.Program
