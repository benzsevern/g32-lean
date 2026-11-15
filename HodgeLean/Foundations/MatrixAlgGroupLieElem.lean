import HodgeLean.Foundations.MatrixAlgGroupLieBasic

/-! # Matrix algebraic groups: elementary lemmas

Helper lemmas for the elementary statements of `MatrixAlgGroupLie.lean`: monotonicity of the
tangent space, the vanishing ideal of `GL_n` over an infinite field, the equations of a
centralizer, finite groups, and the bracket of left-invariant derivations.
-/

noncomputable section

namespace HodgeLean.Foundations

open MvPolynomial HodgeLean.Foundations.Program

variable {k : Type*} [Field k] {n : ℕ}

/-- Evaluating the entries of `x s - s x` at `g` gives the entries of `g s - s g`. -/
theorem g1_eval_commEq (g s : Matrix.GeneralLinearGroup (Fin n) k) (i j : Fin n) :
    eval (g1_coords g) ((g1_varMatrix k n * (s : Matrix (Fin n) (Fin n) k).map C -
      (s : Matrix (Fin n) (Fin n) k).map C * g1_varMatrix k n :
        Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) k)) i j) =
      ((g : Matrix (Fin n) (Fin n) k) * s - s * g : Matrix (Fin n) (Fin n) k) i j := by
  have hs : (eval (g1_coords g)).mapMatrix ((s : Matrix (Fin n) (Fin n) k).map C) = s := by
    ext a b; simp
  have h : (eval (g1_coords g)).mapMatrix
      (g1_varMatrix k n * (s : Matrix (Fin n) (Fin n) k).map C -
        (s : Matrix (Fin n) (Fin n) k).map C * g1_varMatrix k n) =
      (g : Matrix (Fin n) (Fin n) k) * (s : Matrix (Fin n) (Fin n) k) -
        (s : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) := by
    rw [map_sub, map_mul, map_mul, hs, g1_mapMatrix_eval_varMatrix]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) k ↦ M i j) h

/-- Evaluating the determinant of the coordinate matrix at `x`. -/
theorem g1_eval_det_varMatrix (x : Fin n × Fin n → k) :
    eval x (g1_varMatrix k n).det = (Matrix.of fun a b ↦ x (a, b)).det := by
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [g1_varMatrix]

/-- Over an infinite field no nonzero polynomial vanishes on `GL_n(k)`. -/
theorem g1_vanishingIdeal_GL [Infinite k] : g1_vanishingIdeal (g1_GL k n) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  rw [Ideal.mem_bot]
  have hdet : (g1_varMatrix k n).det * f = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero, g1_eval_det_varMatrix]
    by_cases hx : (Matrix.of fun a b ↦ x (a, b)).det = 0
    · rw [hx, zero_mul]
    · have h0 := (mem_vanishingIdeal_iff.mp hf) x
        ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hx, Subgroup.mem_top _, rfl⟩
      rw [show eval x f = 0 from h0, mul_zero]
  have hne : (g1_varMatrix k n).det ≠ 0 := by
    intro h
    have := congrArg (eval (g1_coords (1 : Matrix.GeneralLinearGroup (Fin n) k))) h
    rw [RingHom.map_det, g1_mapMatrix_eval_varMatrix] at this
    simp at this
  exact (mul_eq_zero.mp hdet).resolve_left hne


/-- The differential at `1` of a coordinate minus a constant. -/
theorem g1_differential_X_sub_C (ij : Fin n × Fin n) (c : k) (X : Matrix (Fin n) (Fin n) k) :
    g1_differential (MvPolynomial.X ij - C c) X = X ij.1 ij.2 := by
  simp [g1_differential_apply, pderiv_X, Pi.single_apply]

/-- A matrix other than `1` differs from `1` in some coordinate. -/
theorem g1_exists_coord_ne {g : Matrix.GeneralLinearGroup (Fin n) k} (hg : g ≠ 1) :
    ∃ ij : Fin n × Fin n, g1_coords g ij ≠ g1_coords 1 ij := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hg
  ext i j
  exact h (i, j)

open Classical in
/-- For `p ≠ 1`, a coordinate difference `x_ij - p_ij` vanishing at `p` and not at `1`; for
`p = 1`, the constant `1`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.1.1 and §3.5 (the polynomials
`x_ij - p_ij` defining a point). -/
def g1_separator (p : Matrix.GeneralLinearGroup (Fin n) k) : MvPolynomial (Fin n × Fin n) k :=
  if hp : p = 1 then 1 else
    MvPolynomial.X (g1_exists_coord_ne hp).choose - C (g1_coords p (g1_exists_coord_ne hp).choose)

example : g1_separator (1 : Matrix.GeneralLinearGroup (Fin n) k) = 1 := by
  simp [g1_separator]

/-- The separator of `p` vanishes at `p`. -/
theorem g1_eval_separator_self {p : Matrix.GeneralLinearGroup (Fin n) k} (hp : p ≠ 1) :
    eval (g1_coords p) (g1_separator p) = 0 := by
  simp [g1_separator, hp]

/-- The separator of `p` does not vanish at `1`. -/
theorem g1_eval_separator_one (p : Matrix.GeneralLinearGroup (Fin n) k) :
    eval (g1_coords 1) (g1_separator p) ≠ 0 := by
  unfold g1_separator
  split_ifs with hp
  · simp
  · simpa [sub_eq_zero] using ((g1_exists_coord_ne hp).choose_spec).symm

/-- A finite set of invertible matrices has zero tangent space at `1`. -/
theorem g1_lieOfSet_eq_bot_of_finite (S : Set (Matrix.GeneralLinearGroup (Fin n) k))
    (hS : S.Finite) : g1_lieOfSet S = ⊥ := by
  classical
  rw [eq_bot_iff]
  intro X hX
  simp only [g1_lieOfSet, Submodule.mem_iInf, LinearMap.mem_ker] at hX
  rw [Submodule.mem_bot]
  set q : MvPolynomial (Fin n × Fin n) k := ∏ p ∈ hS.toFinset, g1_separator p with hq
  have hq1 : eval (g1_coords 1) q ≠ 0 := by
    rw [hq, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun p _ ↦ g1_eval_separator_one p
  ext i j
  have hmem : (MvPolynomial.X (i, j) - C (g1_coords 1 (i, j))) * q ∈ g1_vanishingIdealSet S := by
    refine mem_vanishingIdeal_iff.mpr ?_
    rintro _ ⟨g, hg, rfl⟩
    change eval (g1_coords g) _ = 0
    by_cases h1 : g = 1
    · subst h1; simp
    · rw [map_mul, hq, map_prod, Finset.prod_eq_zero (hS.mem_toFinset.mpr hg)
        (g1_eval_separator_self h1), mul_zero]
  have := hX _ hmem
  rw [g1_differential_mul, g1_differential_X_sub_C] at this
  simp only [map_sub, eval_X, eval_C, sub_self, zero_mul, zero_add] at this
  exact (mul_eq_zero.mp this).resolve_left hq1

/-- Each point of `GL_n(k)` is an `IsClosed` set for `g1_zariski`. -/
theorem g1_isClosed_singleton (g : Matrix.GeneralLinearGroup (Fin n) k) :
    @IsClosed _ (g1_zariski k n) {g} := by
  let _ := g1_zariski k n
  have hmax : (MvPolynomial.pointToPoint (k := k) (g1_coords g) :
      PrimeSpectrum (MvPolynomial (Fin n × Fin n) k)).asIdeal.IsMaximal := by
    change (vanishingIdeal k {g1_coords g}).IsMaximal
    infer_instance
  have hcl := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hmax
  refine isClosed_induced_iff.mpr ⟨_, hcl, ?_⟩
  ext g'
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h
    ext i j
    have hI := congrArg PrimeSpectrum.asIdeal h
    have hx : MvPolynomial.X (i, j) - C (g1_coords g (i, j)) ∈
        (MvPolynomial.pointToPoint (k := k) (g1_coords g) :
          PrimeSpectrum (MvPolynomial (Fin n × Fin n) k)).asIdeal := by
      change _ ∈ vanishingIdeal k {g1_coords g}
      rw [mem_vanishingIdeal_singleton_iff]
      simp
    rw [← hI] at hx
    change _ ∈ vanishingIdeal k {g1_coords g'} at hx
    rw [mem_vanishingIdeal_singleton_iff] at hx
    simpa [sub_eq_zero, g1_coords] using hx
  · rintro rfl; rfl

/-- The Zariski topology on `GL_n(k)` is `T1`. -/
theorem g1_t1Space : @T1Space _ (g1_zariski k n) :=
  @T1Space.mk _ (g1_zariski k n) g1_isClosed_singleton

end HodgeLean.Foundations
