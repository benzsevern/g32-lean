import HodgeLean.Foundations.Program.FoundationVocabDefs
import HodgeLean.Foundations.PowersVocabularyDefs

/-! # Matrix algebraic groups: vanishing ideal, Lie algebra, identity component (definitions)

Everything here is constructed from the point set of a `MatrixAlgGroup`; nothing is stored.
The Lie algebra is cut out by the differentials at `1` of **all** polynomials vanishing on the
group (not of the presenting equations), and the identity component is the connected component
of `1` in the Zariski topology on `GL_n(k)`.
-/

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations

open MvPolynomial Matrix HodgeLean.Foundations.Program

variable {k : Type*} [Field k] {n : ℕ}

/-- The matrix coordinates `(i, j) ↦ g i j` of an invertible matrix.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6 (`GL_n` as an affine variety). -/
def g1_coords (g : Matrix.GeneralLinearGroup (Fin n) k) : Fin n × Fin n → k :=
  fun ij ↦ (g : Matrix (Fin n) (Fin n) k) ij.1 ij.2

example (g : Matrix.GeneralLinearGroup (Fin n) k) (i j : Fin n) :
    g1_coords g (i, j) = (g : Matrix (Fin n) (Fin n) k) i j := rfl

/-- The ideal of all polynomials in the matrix entries vanishing on a set of invertible matrices.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1 (the ideal `I(S)`). -/
def g1_vanishingIdealSet (S : Set (Matrix.GeneralLinearGroup (Fin n) k)) :
    Ideal (MvPolynomial (Fin n × Fin n) k) :=
  MvPolynomial.vanishingIdeal k (g1_coords '' S)

example (S : Set (Matrix.GeneralLinearGroup (Fin n) k)) (f : MvPolynomial (Fin n × Fin n) k)
    (hf : f ∈ g1_vanishingIdealSet S) (g : Matrix.GeneralLinearGroup (Fin n) k) (hg : g ∈ S) :
    eval (g1_coords g) f = 0 :=
  (mem_vanishingIdeal_iff.mp hf) _ ⟨g, hg, rfl⟩

/-- The vanishing ideal of a matrix algebraic group: all polynomials vanishing on its points.
It contains the presenting equations and their radical.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1 and §1.1. -/
def g1_vanishingIdeal (G : MatrixAlgGroup k n) : Ideal (MvPolynomial (Fin n × Fin n) k) :=
  g1_vanishingIdealSet (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k))

example (G : MatrixAlgGroup k n) : G.equations ≤ g1_vanishingIdeal G := by
  intro f hf
  refine mem_vanishingIdeal_iff.mpr ?_
  rintro _ ⟨g, hg, rfl⟩
  exact (G.equations_iff g).mp hg f hf

/-- The differential at the identity matrix of a polynomial in the matrix entries, as a linear
form on matrices: `X ↦ Σ_{ij} (∂f/∂x_{ij})(1) X_{ij}`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1 and §3.3 (`d_e f`). -/
def g1_differential (f : MvPolynomial (Fin n × Fin n) k) :
    Matrix (Fin n) (Fin n) k →ₗ[k] k :=
  ∑ ij : Fin n × Fin n,
    eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) (pderiv ij f) •
      Matrix.entryLinearMap k k ij.1 ij.2

example (X : Matrix (Fin n) (Fin n) k) : g1_differential (C (1 : k)) X = 0 := by
  simp [g1_differential]

/-- The tangent space at `1` of a set of invertible matrices: the common kernel of the
differentials at `1` of all polynomials vanishing on the set.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.2 (tangent space `T(V)_e`). -/
def g1_lieOfSet (S : Set (Matrix.GeneralLinearGroup (Fin n) k)) :
    Submodule k (Matrix (Fin n) (Fin n) k) :=
  ⨅ f ∈ g1_vanishingIdealSet S, LinearMap.ker (g1_differential f)

example (X : Matrix (Fin n) (Fin n) k) : X ∈ g1_lieOfSet (∅ : Set (Matrix.GeneralLinearGroup
    (Fin n) k)) ↔ ∀ f ∈ g1_vanishingIdealSet (∅ : Set (Matrix.GeneralLinearGroup (Fin n) k)),
      g1_differential f X = 0 := by
  simp [g1_lieOfSet]

/-- The Lie algebra of a matrix algebraic group: the tangent space at `1` cut out by the
differentials of its **vanishing ideal** `g1_vanishingIdeal G`, not of the presenting equations.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.3 and §3.5 (`L(G) = T(G)_e`). -/
def g1_lieAlgebra (G : MatrixAlgGroup k n) : Submodule k (Matrix (Fin n) (Fin n) k) :=
  g1_lieOfSet (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k))

example (G : MatrixAlgGroup k n) (X : Matrix (Fin n) (Fin n) k) :
    X ∈ g1_lieAlgebra G ↔ ∀ f ∈ g1_vanishingIdeal G, g1_differential f X = 0 := by
  simp [g1_lieAlgebra, g1_lieOfSet, g1_vanishingIdeal]

set_option warn.classDefReducibility false in
/-- The Zariski topology on `GL_n(k)`: the closed sets are the common zero sets of ideals of
polynomials in the matrix entries (induced from the prime spectrum through `pointToPoint`).
It is a `def`, not an instance, so it never meets the analytic topology on `GL_n(ℂ)`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1 and §1.6. -/
def g1_zariski (k : Type*) [Field k] (n : ℕ) :
    TopologicalSpace (Matrix.GeneralLinearGroup (Fin n) k) :=
  TopologicalSpace.induced
    (fun g ↦ (MvPolynomial.pointToPoint (k := k) (g1_coords g) :
      PrimeSpectrum (MvPolynomial (Fin n × Fin n) k)))
    inferInstance

example (k : Type*) [Field k] (n : ℕ) :
    @IsClosed _ (g1_zariski k n) (Set.univ : Set (Matrix.GeneralLinearGroup (Fin n) k)) :=
  @isClosed_univ _ (g1_zariski k n)

/-- The identity component of a matrix algebraic group, constructed as the connected component
of `1` inside the group in the Zariski topology `g1_zariski`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.2 (`G°`). -/
def g1_identityComponent (G : MatrixAlgGroup k n) : Set (Matrix.GeneralLinearGroup (Fin n) k) :=
  @connectedComponentIn _ (g1_zariski k n) (G.carrier : Set _) 1

example (G : MatrixAlgGroup k n) : (1 : Matrix.GeneralLinearGroup (Fin n) k) ∈
    g1_identityComponent G :=
  @mem_connectedComponentIn _ (g1_zariski k n) _ _ G.carrier.one_mem

/-- A matrix algebraic group is connected when its point set is connected in the Zariski
topology `g1_zariski`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.2. -/
def g1_IsConnected (G : MatrixAlgGroup k n) : Prop :=
  @IsConnected _ (g1_zariski k n) (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k))

example (G : MatrixAlgGroup k n) : g1_IsConnected G ↔
    @IsConnected _ (g1_zariski k n) (G.carrier : Set (Matrix.GeneralLinearGroup (Fin n) k)) :=
  Iff.rfl

/-- The matrices commuting with every element of a set of invertible matrices.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §3.11 (`𝔷_𝔤(S)` inside `𝔤𝔩_n`). -/
def g1_lieCentralizer (S : Set (Matrix.GeneralLinearGroup (Fin n) k)) :
    Submodule k (Matrix (Fin n) (Fin n) k) :=
  Subalgebra.toSubmodule (Subalgebra.centralizer k ((↑) '' S))

example (S : Set (Matrix.GeneralLinearGroup (Fin n) k)) :
    (1 : Matrix (Fin n) (Fin n) k) ∈ g1_lieCentralizer S :=
  (Subalgebra.centralizer k _).one_mem

/-- A matrix algebraic group from a set of equations and a subgroup that is exactly their zero
set.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.1. -/
def g1_ofEquations (S : Set (MvPolynomial (Fin n × Fin n) k))
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) k))
    (hH : ∀ g, g ∈ H ↔ ∀ f ∈ S, eval (g1_coords g) f = 0) : MatrixAlgGroup k n where
  equations := Ideal.span S
  carrier := H
  equations_iff g := by
    rw [hH g]
    constructor
    · intro h f hf
      have hle : Ideal.span S ≤ RingHom.ker (eval (g1_coords g)) :=
        (Ideal.span_le).mpr fun f hf ↦ (RingHom.mem_ker).mpr (h f hf)
      exact (RingHom.mem_ker).mp (hle hf)
    · exact fun h f hf ↦ h f (Ideal.subset_span hf)

example (S : Set (MvPolynomial (Fin n × Fin n) k))
    (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) k))
    (hH : ∀ g, g ∈ H ↔ ∀ f ∈ S, eval (g1_coords g) f = 0) :
    (g1_ofEquations S H hH).carrier = H := rfl

/-- The general linear group `GL_n`, with no equations.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6. -/
def g1_GL (k : Type*) [Field k] (n : ℕ) : MatrixAlgGroup k n :=
  g1_ofEquations ∅ ⊤ (by simp)

example : (g1_GL k n).carrier = ⊤ := rfl

/-- The one-point group `{1} ⊆ GL_1` presented by the single non-reduced equation
`(x - 1)²`.  Its presenting equation has zero differential at `1`; its vanishing ideal does not.
Source: the counterexample (a) to the first draft `parked/g1alg-v1`; Borel, AG.1.1. -/
def g1_squareGroup (k : Type*) [Field k] : MatrixAlgGroup k 1 :=
  g1_ofEquations {(X (0, 0) - 1) ^ 2} ⊥ (by
    intro g
    simp only [Subgroup.mem_bot, Set.mem_singleton_iff, forall_eq, map_pow, map_sub, eval_X,
      map_one, g1_coords, pow_eq_zero_iff two_ne_zero, sub_eq_zero]
    constructor
    · rintro rfl
      rfl
    · intro h
      ext i j
      fin_cases i; fin_cases j
      simpa using h)

example : (g1_squareGroup k).carrier = ⊥ := rfl

/-- The one-point group is finite.
Source: the definition `g1_squareGroup`. -/
instance g1_squareGroup_finite : Finite (g1_squareGroup k).carrier := by
  change Finite (⊥ : Subgroup (Matrix.GeneralLinearGroup (Fin 1) k))
  infer_instance

example : (g1_squareGroup k).equations = Ideal.span {(X (0, 0) - 1) ^ 2} := rfl

/-- The diagonal torus `D_n ⊆ GL_n`, presented by the vanishing of the off-diagonal entries.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6 and §8.2. -/
def g1_diagTorus (k : Type*) [Field k] (n : ℕ) : MatrixAlgGroup k n :=
  g1_ofEquations {f | ∃ i j : Fin n, i ≠ j ∧ f = X (i, j)}
    { carrier := {g | (g : Matrix (Fin n) (Fin n) k).IsDiag}
      one_mem' := Matrix.isDiag_one
      mul_mem' := fun {a b} ha hb ↦ by
        change ((a : Matrix (Fin n) (Fin n) k) * b).IsDiag
        rw [← ha.diagonal_diag, ← hb.diagonal_diag, Matrix.diagonal_mul_diagonal]
        exact Matrix.isDiag_diagonal _
      inv_mem' := fun {a} ha ↦ by
        have h := ha.diagonal_diag.symm
        change ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k).IsDiag
        rw [Matrix.coe_units_inv, h, Matrix.inv_diagonal]
        exact Matrix.isDiag_diagonal _ }
    (by
      intro g
      simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq,
        forall_exists_index, and_imp]
      constructor
      · rintro h f i j hij rfl
        simpa [g1_coords] using h hij
      · intro h i j hij
        simpa [g1_coords] using h _ i j hij rfl)

example : (1 : Matrix.GeneralLinearGroup (Fin n) k) ∈ (g1_diagTorus k n).carrier :=
  (g1_diagTorus k n).carrier.one_mem

/-- The matrix of coordinate variables `(x_{ij})`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6. -/
def g1_varMatrix (k : Type*) [Field k] (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k) :=
  Matrix.of fun a b ↦ X (a, b)

/-- Evaluating the coordinate-variable matrix at the coordinates of `g` returns `g`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6. -/
theorem g1_mapMatrix_eval_varMatrix (g : Matrix.GeneralLinearGroup (Fin n) k) :
    (eval (g1_coords g)).mapMatrix (g1_varMatrix k n) = (g : Matrix (Fin n) (Fin n) k) := by
  ext i j
  simp [g1_varMatrix, g1_coords]

example (g : Matrix.GeneralLinearGroup (Fin n) k) (i j : Fin n) :
    eval (g1_coords g) (g1_varMatrix k n i j) = (g : Matrix (Fin n) (Fin n) k) i j := by
  simp [g1_varMatrix, g1_coords]

/-- The special linear group `SL_n`, presented by `det(x) - 1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6. -/
def g1_SL (k : Type*) [Field k] (n : ℕ) : MatrixAlgGroup k n :=
  g1_ofEquations {(g1_varMatrix k n).det - 1} (Matrix.GeneralLinearGroup.det).ker (by
    intro g
    rw [MonoidHom.mem_ker, Units.ext_iff]
    simp only [Set.mem_singleton_iff, forall_eq, map_sub, map_one, RingHom.map_det,
      g1_mapMatrix_eval_varMatrix, sub_eq_zero, Matrix.GeneralLinearGroup.val_det_apply,
      Units.val_one])

example (g : Matrix.GeneralLinearGroup (Fin n) k) :
    g ∈ (g1_SL k n).carrier ↔ (g : Matrix (Fin n) (Fin n) k).det = 1 := by
  simp [g1_SL, g1_ofEquations, Units.ext_iff]

/-- The isometry subgroup `{g | gᵀ Ω g = Ω}` of a bilinear form with Gram matrix `Ω`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6 (classical groups). -/
def g1_isometrySubgroup (Ω : Matrix (Fin n) (Fin n) k) :
    Subgroup (Matrix.GeneralLinearGroup (Fin n) k) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) k)ᵀ * Ω * (g : Matrix (Fin n) (Fin n) k) = Ω}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb ↦ by
    change ((a : Matrix (Fin n) (Fin n) k) * (b : Matrix (Fin n) (Fin n) k))ᵀ * Ω *
      ((a : Matrix (Fin n) (Fin n) k) * (b : Matrix (Fin n) (Fin n) k)) = Ω
    change (a : Matrix (Fin n) (Fin n) k)ᵀ * Ω * (a : Matrix (Fin n) (Fin n) k) = Ω at ha
    change (b : Matrix (Fin n) (Fin n) k)ᵀ * Ω * (b : Matrix (Fin n) (Fin n) k) = Ω at hb
    rw [Matrix.transpose_mul]
    set A : Matrix (Fin n) (Fin n) k := (a : Matrix (Fin n) (Fin n) k)
    set B : Matrix (Fin n) (Fin n) k := (b : Matrix (Fin n) (Fin n) k)
    calc Bᵀ * Aᵀ * Ω * (A * B) = Bᵀ * (Aᵀ * Ω * A) * B := by simp only [Matrix.mul_assoc]
      _ = Ω := by rw [ha, hb]
  inv_mem' := fun {a} ha ↦ by
    change (a : Matrix (Fin n) (Fin n) k)ᵀ * Ω * (a : Matrix (Fin n) (Fin n) k) = Ω at ha
    change ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k)ᵀ * Ω *
      ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) = Ω
    set A : Matrix (Fin n) (Fin n) k := (a : Matrix (Fin n) (Fin n) k)
    set B : Matrix (Fin n) (Fin n) k := ((a⁻¹ : Matrix.GeneralLinearGroup (Fin n) k) :
      Matrix (Fin n) (Fin n) k)
    have hAB : A * B = 1 := by simp [A, B]
    calc Bᵀ * Ω * B = Bᵀ * (Aᵀ * Ω * A) * B := by rw [ha]
      _ = (A * B)ᵀ * Ω * (A * B) := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Ω := by rw [hAB]; simp

/-- The matrix of polynomials `xᵀ Ω x - Ω` whose entries present the isometry group of `Ω`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6. -/
def g1_isometryEquations (Ω : Matrix (Fin n) (Fin n) k) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k) :=
  (g1_varMatrix k n)ᵀ * Ω.map C * g1_varMatrix k n - Ω.map C

example (Ω : Matrix (Fin n) (Fin n) k) : g1_isometryEquations Ω =
    (g1_varMatrix k n)ᵀ * Ω.map C * g1_varMatrix k n - Ω.map C := rfl

/-- The isometry group of a bilinear form with Gram matrix `Ω`, presented by the entries of
`xᵀ Ω x - Ω`. For the standard alternating `Ω` on `Fin (2g)` this is `Sp_{2g}`; for `Ω = 1` it
is `O_n`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6 (classical groups). -/
def g1_isometryGroup (Ω : Matrix (Fin n) (Fin n) k) : MatrixAlgGroup k n :=
  g1_ofEquations
    {f | ∃ i j : Fin n, f = g1_isometryEquations Ω i j}
    (g1_isometrySubgroup Ω)
    (by
      intro g
      have hmap : (eval (g1_coords g)).mapMatrix (g1_isometryEquations Ω) =
          (g : Matrix (Fin n) (Fin n) k)ᵀ * Ω * (g : Matrix (Fin n) (Fin n) k) - Ω := by
        have hΩ : (eval (g1_coords g)).mapMatrix (Ω.map C) = Ω := by
          ext i j; simp
        have hT : (eval (g1_coords g)).mapMatrix (g1_varMatrix k n)ᵀ =
            (g : Matrix (Fin n) (Fin n) k)ᵀ := by
          rw [← g1_mapMatrix_eval_varMatrix g]; rfl
        rw [g1_isometryEquations, map_sub, map_mul, map_mul, hΩ, hT,
          g1_mapMatrix_eval_varMatrix]
      have key : ∀ i j : Fin n, eval (g1_coords g) (g1_isometryEquations Ω i j) =
          ((g : Matrix (Fin n) (Fin n) k)ᵀ * Ω * (g : Matrix (Fin n) (Fin n) k) - Ω) i j := by
        intro i j
        rw [← hmap]
        rfl
      change (g : Matrix (Fin n) (Fin n) k)ᵀ * Ω * (g : Matrix (Fin n) (Fin n) k) = Ω ↔ _
      rw [← sub_eq_zero]
      constructor
      · rintro h f ⟨i, j, rfl⟩
        rw [key, h]
        rfl
      · intro h
        ext i j
        rw [← key]
        exact h _ ⟨i, j, rfl⟩)

example (Ω : Matrix (Fin n) (Fin n) k) :
    (g1_isometryGroup Ω).carrier = g1_isometrySubgroup Ω := rfl

/-- The symplectic group `Sp_{2g}`: the isometry group of Mathlib's standard alternating form
`Matrix.J`, reindexed to `Fin (g + g)`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6 and §23.3. -/
def g1_Sp (k : Type*) [Field k] (g : ℕ) : MatrixAlgGroup k (g + g) :=
  g1_isometryGroup (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.J (Fin g) k))

example (g : ℕ) : (1 : Matrix.GeneralLinearGroup (Fin (g + g)) k) ∈ (g1_Sp k g).carrier :=
  (g1_Sp k g).carrier.one_mem

end HodgeLean.Foundations
