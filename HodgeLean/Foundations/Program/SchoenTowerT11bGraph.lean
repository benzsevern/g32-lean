import HodgeLean.Foundations.Program.SchoenTowerT11bDefs
import Mathlib.Algebra.MvPolynomial.Monad

/-! Polynomial descriptions of a distance graph.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Substitute polynomials in a Boolean polynomial description.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, polynomial inverse-image case. -/
def s2v_t11b_Formula.subst {n m : ℕ}
    (σ : Fin n → MvPolynomial (Fin m) ℝ) : s2v_t11b_Formula n → s2v_t11b_Formula m
  | .nonneg p => .nonneg (MvPolynomial.bind₁ σ p)
  | .compl f => .compl (f.subst σ)
  | .inter f g => .inter (f.subst σ) (g.subst σ)

/-- Realization commutes with polynomial substitution.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, polynomial inverse-image case. -/
theorem s2v_t11b_realize_subst {n m : ℕ}
    (σ : Fin n → MvPolynomial (Fin m) ℝ) (f : s2v_t11b_Formula n)
    (y : EuclideanSpace ℝ (Fin m)) :
    y ∈ (f.subst σ).realize ↔
      (WithLp.toLp 2 (fun i => MvPolynomial.eval (fun j => y j) (σ i))) ∈ f.realize := by
  induction f with
  | nonneg p => simp only [s2v_t11b_Formula.subst, s2v_t11b_Formula.realize, Set.mem_ofPred_eq,
      MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
  | compl f ih => exact not_congr ih
  | inter f g ihf ihg => exact and_congr ihf ihg

/-- A Boolean polynomial description of a polynomial zero locus.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, algebraic-set case. -/
def s2v_t11b_zeroFormula {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    s2v_t11b_Formula n := .inter (.nonneg p) (.nonneg (-p))

/-- The paired inequalities describe precisely the polynomial zero locus.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, algebraic-set case. -/
theorem s2v_t11b_realize_zeroFormula {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ (s2v_t11b_zeroFormula p).realize ↔ MvPolynomial.eval (fun i => y i) p = 0 := by
  simp only [s2v_t11b_zeroFormula, s2v_t11b_Formula.realize, Set.mem_inter_iff,
    Set.mem_ofPred_eq, map_neg, neg_nonneg]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

/-- The squared-distance equation in n spatial coordinates and one radius coordinate.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.19, distance-map construction. -/
def s2v_t11b_distancePolynomial {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    MvPolynomial (Fin (n + 1)) ℝ :=
  (∑ i : Fin n, (MvPolynomial.X i.castSucc - MvPolynomial.C (x i)) ^ 2) -
    MvPolynomial.X (Fin.last n) ^ 2

/-- Evaluation of the distance equation uses the Euclidean norm on spatial coordinates.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.19, distance-map construction. -/
theorem s2v_t11b_eval_distancePolynomial {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin (n + 1))) :
    MvPolynomial.eval (fun i => y i) (s2v_t11b_distancePolynomial x) =
      dist (WithLp.toLp 2 (fun i : Fin n => y i.castSucc)) x ^ 2 - y (Fin.last n) ^ 2 := by
  simp only [s2v_t11b_distancePolynomial, map_sub, map_sum, map_pow,
    MvPolynomial.eval_X, MvPolynomial.eval_C, dist_eq_norm,
    EuclideanSpace.real_norm_sq_eq]
  rfl

/-- A Boolean polynomial description of the graph of distance restricted to a Boolean set.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.19. -/
def s2v_t11b_distanceGraphFormula {n : ℕ} (f : s2v_t11b_Formula n)
    (x : EuclideanSpace ℝ (Fin n)) : s2v_t11b_Formula (n + 1) :=
  .inter (f.subst (fun i => MvPolynomial.X i.castSucc))
    (.inter (.nonneg (MvPolynomial.X (Fin.last n)))
      (s2v_t11b_zeroFormula (s2v_t11b_distancePolynomial x)))

/-- The distance graph description retains exactly the original spatial set and radius.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.19. -/
theorem s2v_t11b_realize_distanceGraphFormula {n : ℕ} (f : s2v_t11b_Formula n)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin (n + 1))) :
    y ∈ (s2v_t11b_distanceGraphFormula f x).realize ↔
      WithLp.toLp 2 (fun i : Fin n => y i.castSucc) ∈ f.realize ∧
        y (Fin.last n) = dist (WithLp.toLp 2 (fun i : Fin n => y i.castSucc)) x := by
  simp only [s2v_t11b_distanceGraphFormula, s2v_t11b_Formula.realize,
    Set.mem_inter_iff, s2v_t11b_realize_subst, MvPolynomial.eval_X,
    Set.mem_ofPred_eq, s2v_t11b_realize_zeroFormula, s2v_t11b_eval_distancePolynomial,
    sub_eq_zero]
  constructor
  · rintro ⟨hy, ht, heq⟩
    exact ⟨hy, (sq_eq_sq₀ ht dist_nonneg).mp heq.symm⟩
  · rintro ⟨hy, heq⟩
    exact ⟨hy, heq ▸ dist_nonneg, by rw [heq]⟩

/-- The original Boolean set is homeomorphic to its distance graph in one extra coordinate.
Source: Coste, Real Algebraic Sets (2005), Theorems 1.1 and 1.19. -/
def s2v_t11b_distanceGraphHomeomorph {n : ℕ} (f : s2v_t11b_Formula n)
    (x : EuclideanSpace ℝ (Fin n)) :
    f.realize ≃ₜ (s2v_t11b_distanceGraphFormula f x).realize where
  toFun y := ⟨WithLp.toLp 2 (Fin.snoc (fun i => y.val i) (dist y.val x)), by
    rw [s2v_t11b_realize_distanceGraphFormula]
    simpa only [WithLp.ofLp_toLp, Fin.snoc_castSucc, WithLp.toLp_ofLp, Fin.snoc_last]
      using And.intro y.property (rfl : dist y.val x = dist y.val x)⟩
  invFun z := ⟨WithLp.toLp 2 (fun i : Fin n => z.val i.castSucc),
    ((s2v_t11b_realize_distanceGraphFormula f x z.val).mp z.property).1⟩
  left_inv y := by
    apply Subtype.ext
    ext i
    simp only [Fin.snoc_castSucc]
  right_inv z := by
    apply Subtype.ext
    apply WithLp.ofLp_injective
    change Fin.snoc (fun i : Fin n => z.val i.castSucc)
      (dist (WithLp.toLp 2 (fun i : Fin n => z.val i.castSucc)) x) = WithLp.ofLp z.val
    rw [← ((s2v_t11b_realize_distanceGraphFormula f x z.val).mp z.property).2]
    exact Fin.snoc_init_self _
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp
    exact (((PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ)).comp
      continuous_subtype_val).finSnoc (continuous_subtype_val.dist continuous_const))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
    exact continuous_pi fun i => (PiLp.continuous_apply 2 _ i.castSucc).comp
      continuous_subtype_val

end HodgeLean.Foundations.Program
