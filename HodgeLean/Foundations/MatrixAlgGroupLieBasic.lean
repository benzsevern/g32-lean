import HodgeLean.Foundations.MatrixAlgGroupLieDefs

/-! # Matrix algebraic groups: shared helper lemmas

Lemmas used by several of the helper files of `MatrixAlgGroupLie.lean`: monotonicity of the
tangent space, the differential at `1` as a sum and its product rule, points of the prime
spectrum, left multiplication on the coordinate ring and its Zariski continuity, and left
translates of polynomials.
-/

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations

open MvPolynomial Matrix HodgeLean.Foundations.Program

variable {k : Type*} [Field k] {n : ℕ}

/-- A larger set of invertible matrices has a larger tangent space at `1`. -/
theorem g1_lieOfSet_mono {S T : Set (Matrix.GeneralLinearGroup (Fin n) k)} (h : S ⊆ T) :
    g1_lieOfSet S ≤ g1_lieOfSet T := by
  intro X hX
  simp only [g1_lieOfSet, Submodule.mem_iInf, LinearMap.mem_ker] at hX ⊢
  intro f hf
  exact hX f (vanishingIdeal_anti_mono (Set.image_mono h) hf)

/-! ## The differential at `1` -/

/-- The differential at `1` as a sum over the matrix entries.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1. -/
theorem g1_differential_apply (f : MvPolynomial (Fin n × Fin n) k)
    (X : Matrix (Fin n) (Fin n) k) :
    g1_differential f X = ∑ ij : Fin n × Fin n,
      eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) (pderiv ij f) * X ij.1 ij.2 := by
  simp [g1_differential]

/-- The differential at `1`, written as a sum over the matrix entries with the direction first.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.16.1 and §3.3. -/
theorem g1_differential_apply_dir (f : MvPolynomial (Fin n × Fin n) k)
    (Y : Matrix (Fin n) (Fin n) k) :
    g1_differential f Y =
      ∑ ij, Y ij.1 ij.2 * eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k))
        (pderiv ij f) := by
  simp [g1_differential, mul_comm]

/-- The product rule for the differential at `1`. -/
theorem g1_differential_mul (f g : MvPolynomial (Fin n × Fin n) k)
    (X : Matrix (Fin n) (Fin n) k) :
    g1_differential (f * g) X =
      eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) f * g1_differential g X +
      eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k)) g * g1_differential f X := by
  simp only [g1_differential_apply, Derivation.leibniz, smul_eq_mul, map_add, map_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-! ## Points of the prime spectrum -/

/-- The point of the prime spectrum attached to `g` is the ideal of polynomials vanishing at `g`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1. -/
theorem g1_mem_pointToPoint_iff (g : Matrix.GeneralLinearGroup (Fin n) k)
    (f : MvPolynomial (Fin n × Fin n) k) :
    f ∈ (MvPolynomial.pointToPoint (k := k) (g1_coords g) :
      PrimeSpectrum (MvPolynomial (Fin n × Fin n) k)).asIdeal ↔ eval (g1_coords g) f = 0 :=
  mem_vanishingIdeal_singleton_iff _ _

/-- The point of the prime spectrum attached to a point of coordinates `x` is the kernel of
evaluation at `x`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1 and AG.3.1 (points as maximal
ideals). -/
theorem g1_mem_pointToPoint_coords_iff (x : Fin n × Fin n → k)
    (f : MvPolynomial (Fin n × Fin n) k) :
    f ∈ (MvPolynomial.pointToPoint (k := k) x).asIdeal ↔ eval x f = 0 := by
  change f ∈ MvPolynomial.vanishingIdeal k {x} ↔ _
  rw [mem_vanishingIdeal_singleton_iff]
  rfl

/-! ## Left multiplication -/

/-- The entries of `h * x` as polynomials in the entries of `x`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6 (multiplication is a morphism). -/
def g1_leftMulPoly (h : Matrix.GeneralLinearGroup (Fin n) k) :
    Fin n × Fin n → MvPolynomial (Fin n × Fin n) k :=
  fun ij ↦ ∑ l, C ((h : Matrix (Fin n) (Fin n) k) ij.1 l) * X (l, ij.2)

/-- Substituting the entries of `h * x` and evaluating at `g` is evaluation at `h * g`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6. -/
theorem g1_eval_bind₁_leftMulPoly (h g : Matrix.GeneralLinearGroup (Fin n) k)
    (f : MvPolynomial (Fin n × Fin n) k) :
    eval (g1_coords g) (bind₁ (g1_leftMulPoly h) f) = eval (g1_coords (h * g)) f := by
  change aeval (g1_coords g) (bind₁ (g1_leftMulPoly h) f) = aeval (g1_coords (h * g)) f
  rw [aeval_bind₁]
  congr 2
  funext ij
  simp [g1_leftMulPoly, g1_coords, Matrix.mul_apply]

/-- Left multiplication by `a` on matrix coordinates, as an algebra map of the coordinate ring:
`x_ij ↦ Σ_l a_il x_lj`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6 (translations are morphisms). -/
def g1_leftMulAlgHom (a : Matrix.GeneralLinearGroup (Fin n) k) :
    MvPolynomial (Fin n × Fin n) k →ₐ[k] MvPolynomial (Fin n × Fin n) k :=
  aeval fun ij ↦ ∑ l, C ((a : Matrix (Fin n) (Fin n) k) ij.1 l) * X (l, ij.2)

/-- Evaluating the translated polynomial at `g` is evaluating the polynomial at `a * g`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6. -/
theorem g1_eval_leftMulAlgHom (a g : Matrix.GeneralLinearGroup (Fin n) k)
    (f : MvPolynomial (Fin n × Fin n) k) :
    eval (g1_coords g) (g1_leftMulAlgHom a f) = eval (g1_coords (a * g)) f := by
  have h : (eval (g1_coords g)).comp (g1_leftMulAlgHom a).toRingHom =
      eval (g1_coords (a * g)) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun ij ↦ ?_)
    · simp
    · simp [g1_leftMulAlgHom, g1_coords, Matrix.mul_apply]
  exact RingHom.congr_fun h f

/-- Left translations of `GL_n(k)` are continuous for the Zariski topology.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.6 and §1.2. -/
theorem g1_continuous_mul_left (a : Matrix.GeneralLinearGroup (Fin n) k) :
    @Continuous _ _ (g1_zariski k n) (g1_zariski k n) (fun g ↦ a * g) := by
  let _ := g1_zariski k n
  have hφ : Continuous (fun g : Matrix.GeneralLinearGroup (Fin n) k ↦
      (MvPolynomial.pointToPoint (k := k) (g1_coords g) :
        PrimeSpectrum (MvPolynomial (Fin n × Fin n) k))) := continuous_induced_dom
  refine continuous_induced_rng.mpr ?_
  have heq : (fun g : Matrix.GeneralLinearGroup (Fin n) k ↦
      (MvPolynomial.pointToPoint (k := k) (g1_coords (a * g)) :
        PrimeSpectrum (MvPolynomial (Fin n × Fin n) k))) =
      PrimeSpectrum.comap (g1_leftMulAlgHom a).toRingHom ∘
        (fun g ↦ MvPolynomial.pointToPoint (k := k) (g1_coords g)) := by
    funext g
    ext f
    rw [Function.comp_apply, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap,
      g1_mem_pointToPoint_coords_iff, g1_mem_pointToPoint_coords_iff]
    change _ ↔ eval (g1_coords g) (g1_leftMulAlgHom a f) = 0
    rw [g1_eval_leftMulAlgHom]
  change Continuous (fun g : Matrix.GeneralLinearGroup (Fin n) k ↦
      (MvPolynomial.pointToPoint (k := k) (g1_coords (a * g)) :
        PrimeSpectrum (MvPolynomial (Fin n × Fin n) k)))
  rw [heq]
  exact (PrimeSpectrum.continuous_comap _).comp hφ

/-! ## Left translates of polynomials -/

/-- Left translation by `g` on polynomials in the matrix entries: `f ↦ (x ↦ f(g x))`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.9 and §3.4 (translations `λ_g` on
`k[G]`). -/
def g1_leftTranslate (g : Matrix.GeneralLinearGroup (Fin n) k) :
    MvPolynomial (Fin n × Fin n) k →ₐ[k] MvPolynomial (Fin n × Fin n) k :=
  aeval fun ij ↦ ((g : Matrix (Fin n) (Fin n) k).map C * g1_varMatrix k n :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k)) ij.1 ij.2

example (g : Matrix.GeneralLinearGroup (Fin n) k) (c : k) : g1_leftTranslate g (C c) = C c :=
  (g1_leftTranslate g).commutes c

/-- Evaluating a left translate at `h` is evaluating at `g h`. -/
theorem g1_eval_leftTranslate (g h : Matrix.GeneralLinearGroup (Fin n) k)
    (f : MvPolynomial (Fin n × Fin n) k) :
    eval (g1_coords h) (g1_leftTranslate g f) = eval (g1_coords (g * h)) f := by
  have hc : ∀ ij : Fin n × Fin n, eval (g1_coords h)
      (((g : Matrix (Fin n) (Fin n) k).map C * g1_varMatrix k n :
        Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k)) ij.1 ij.2) =
        g1_coords (g * h) ij := by
    intro ij
    have hm : (eval (g1_coords h)).mapMatrix
        (((g : Matrix (Fin n) (Fin n) k).map C * g1_varMatrix k n :
          Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k))) =
          ((g * h : Matrix.GeneralLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      rw [map_mul, g1_mapMatrix_eval_varMatrix, Units.val_mul]
      congr 1
      ext a b
      simp
    exact congrArg (fun M : Matrix (Fin n) (Fin n) k ↦ M ij.1 ij.2) hm
  induction f using MvPolynomial.induction_on with
  | C a => simp [g1_leftTranslate]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ij hp =>
    simp only [map_mul, hp, g1_leftTranslate, aeval_X, eval_X] at hp ⊢
    rw [hc ij]

/-- The left translate `x ↦ f(g x)` of a polynomial in the matrix entries, by substitution.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.9 (translations `λ_g`). -/
def g1_leftTranslateBind (g : Matrix.GeneralLinearGroup (Fin n) k)
    (f : MvPolynomial (Fin n × Fin n) k) : MvPolynomial (Fin n × Fin n) k :=
  bind₁ (fun ij ↦ ∑ l, C ((g : Matrix (Fin n) (Fin n) k) ij.1 l) * X (l, ij.2)) f

example (g : Matrix.GeneralLinearGroup (Fin n) k) (a : k) :
    g1_leftTranslateBind g (C a) = C a := by
  simp [g1_leftTranslateBind]

/-- Evaluating the left translate by `g` at `h` is evaluating at `g h`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.9. -/
theorem g1_eval_leftTranslateBind (g h : Matrix.GeneralLinearGroup (Fin n) k)
    (f : MvPolynomial (Fin n × Fin n) k) :
    eval (g1_coords h) (g1_leftTranslateBind g f) = eval (g1_coords (g * h)) f := by
  have hb := aeval_bind₁ (g1_coords h) (fun ij ↦ ∑ l, C ((g : Matrix (Fin n) (Fin n) k) ij.1 l) *
    X (l, ij.2)) f
  change aeval (g1_coords h) (bind₁ _ f) = _
  rw [hb]
  change eval _ f = _
  congr 2
  funext ij
  simp [g1_coords, Matrix.mul_apply]

end HodgeLean.Foundations
