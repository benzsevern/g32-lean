import HodgeLean.Foundations.Program.MilneTensorPolynomial

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ] {n : ℕ}

omit [Fintype ι] in
theorem m1b_reflection_multilinear_coefficient
    (f : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ) (w : ι → κ) (k : κ)
    (hf : ∀ v, f (fun i j => if w j = k then -(v i j) else v i j) = f v)
    (a : Fin n → ι) (ha : Odd (Finset.univ.filter (fun i => w (a i) = k)).card) :
    f (fun i => Pi.single (a i) 1) = 0 := by
  classical
  have hv (i : Fin n) :
      (fun j => if w j = k then -(Pi.single (a i) (1 : ℂ) j) else Pi.single (a i) 1 j) =
      (if w (a i) = k then (-1 : ℂ) else 1) • Pi.single (a i) 1 := by
    funext j
    by_cases hj : j = a i
    · subst j
      simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, mul_one]
    · simp [Pi.single_eq_of_ne hj, Pi.smul_apply]
  have hp : (∏ i : Fin n, if w (a i) = k then (-1 : ℂ) else 1) = -1 := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, one_pow, mul_one]
    exact ha.neg_one_pow
  have h := hf (fun i => Pi.single (a i) 1)
  have hv' := congrArg f (funext hv)
  rw [f.map_smul_univ, hp, neg_one_smul] at hv'
  have he : -f (fun i => Pi.single (a i) 1) = f (fun i => Pi.single (a i) 1) :=
    hv'.symm.trans h
  have hz : (2 : ℂ) * f (fun i => Pi.single (a i) 1) = 0 := by
    linear_combination -he
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

variable [Fintype κ]

omit [Fintype ι] [DecidableEq ι] in
theorem m1b_weight_product (w : ι → κ) (a : Fin n → ι) (s : κ → ℂ) :
    (∏ i, s (w (a i))) = ∏ k, s k ^ (Finset.univ.filter (fun i => w (a i) = k)).card := by
  simpa only [Finset.prod_const] using
    (Finset.prod_fiberwise' Finset.univ (fun i => w (a i)) s).symm

def m1b_diagonalExtensionPolynomial
    (f : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ) (w : ι → κ) :
    MvPolynomial (κ ⊕ (Fin n × ι)) ℂ :=
  ∑ a : Fin n → ι, MvPolynomial.C (f (fun i => Pi.single (a i) 1)) *
    ((∏ k, MvPolynomial.X (Sum.inl k) ^
      ((Finset.univ.filter (fun i => w (a i) = k)).card / 2)) *
      ∏ i, MvPolynomial.X (Sum.inr (i, a i)))

theorem m1b_diagonalExtensionPolynomial_eval
    (f : MultilinearMap ℂ (fun _ : Fin n => ι → ℂ) ℂ) (w : ι → κ)
    (hf : ∀ k v, f (fun i j => if w j = k then -(v i j) else v i j) = f v)
    (s : κ → ℂ) (v : Fin n → ι → ℂ) :
    MvPolynomial.eval (Sum.elim (fun k => s k ^ 2) (fun p : Fin n × ι => v p.1 p.2))
      (m1b_diagonalExtensionPolynomial f w) = f (fun i j => s (w j) * v i j) := by
  classical
  rw [m1b_multilinear_coordinate_expansion f (fun i j => s (w j) * v i j)]
  simp only [m1b_diagonalExtensionPolynomial, map_sum, map_mul, map_prod, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hc : f (fun i => Pi.single (a i) 1) = 0
  · simp only [hc, zero_mul, mul_zero]
  · have heven (k : κ) : Even (Finset.univ.filter (fun i => w (a i) = k)).card := by
      by_contra hn
      exact hc (m1b_reflection_multilinear_coefficient f w k (hf k) a
        (Nat.not_even_iff_odd.mp hn))
    have hs : (∏ k, (s k ^ 2) ^ ((Finset.univ.filter (fun i => w (a i) = k)).card / 2)) =
        ∏ k, s k ^ (Finset.univ.filter (fun i => w (a i) = k)).card := by
      apply Finset.prod_congr rfl
      intro k _
      rw [← pow_mul]
      congr 1
      obtain ⟨m, hm⟩ := heven k
      omega
    rw [hs, Finset.prod_mul_distrib, m1b_weight_product w a s]
    ring

def m1b_coordinateReflection (k : ι) : Module.End ℂ (ι → ℂ) :=
  LinearMap.piMap (fun i => (if i = k then (-1 : ℂ) else 1) • LinearMap.id)

omit [Fintype ι] in
theorem m1b_coordinateReflection_square (k : ι) :
    m1b_coordinateReflection k * m1b_coordinateReflection k = 1 := by
  apply LinearMap.ext
  intro x
  funext i
  change (if i = k then (-1 : ℂ) else 1) * ((if i = k then (-1 : ℂ) else 1) * x i) = x i
  by_cases h : i = k <;> simp [h]

theorem m1b_coordinateReflection_isometry (k : ι) :
    m1b_coordinateReflection k ∈ m1b_isometries (Matrix.toBilin' (1 : Matrix ι ι ℂ)) := by
  refine ⟨⟨⟨m1b_coordinateReflection k, m1b_coordinateReflection k,
    m1b_coordinateReflection_square k, m1b_coordinateReflection_square k⟩, rfl⟩, ?_⟩
  intro x y
  simp only [Matrix.toBilin'_apply', Matrix.one_mulVec]
  apply Finset.sum_congr rfl
  intro i _
  change ((if i = k then (-1 : ℂ) else 1) * x i) *
    ((if i = k then (-1 : ℂ) else 1) * y i) = x i * y i
  by_cases h : i = k <;> simp [h]

def m1b_copyCoordinates (r : ℕ) : ((Fin r × ι) → ℂ) →ₗ[ℂ] (Fin r → ι → ℂ) :=
  LinearMap.pi (fun a => LinearMap.pi (fun b => LinearMap.proj (a, b)))

theorem m1b_orthogonal_diagonal_polynomial {r : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ι → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries (Matrix.toBilin' (1 : Matrix ι ι ℂ)), ∀ v,
      f (fun j => m1b_copies r u (v j)) = f v) :
    ∃ P : MvPolynomial (ι ⊕ (Fin n × (Fin r × ι))) ℂ,
      ∀ (s : ι → ℂ) (v : Fin n → Fin r → ι → ℂ),
      MvPolynomial.eval (Sum.elim (fun k => s k ^ 2)
        (fun p : Fin n × (Fin r × ι) => v p.1 p.2.1 p.2.2)) P =
        f (fun j a b => s b * v j a b) := by
  let g := f.compLinearMap (fun _ => m1b_copyCoordinates (ι := ι) r)
  have hg : ∀ k v, g (fun j p => if p.2 = k then -(v j p) else v j p) = g v := by
    intro k v
    have h := hf (m1b_coordinateReflection k) (m1b_coordinateReflection_isometry k)
      (fun j a b => v j (a, b))
    change f (fun j a b => (if b = k then (-1 : ℂ) else 1) * v j (a, b)) =
      f (fun j a b => v j (a, b)) at h
    change f (fun j a b => if b = k then -(v j (a, b)) else v j (a, b)) =
      f (fun j a b => v j (a, b))
    simpa only [ite_mul, neg_one_mul, one_mul] using h
  refine ⟨m1b_diagonalExtensionPolynomial g Prod.snd, ?_⟩
  intro s v
  exact m1b_diagonalExtensionPolynomial_eval g Prod.snd hg s (fun j p => v j p.1 p.2)

end HodgeLean.Foundations.Program
