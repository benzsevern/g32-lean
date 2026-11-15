import HodgeLean.Foundations.Program.MilneTensorComplement
import HodgeLean.Foundations.Program.MilneTensorPolynomial

noncomputable section
namespace HodgeLean.Foundations.Program

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup W] [Module ℂ W]

theorem m1b_complementCoefficient_coordinates {n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => (ι → ℂ) × W) ℂ)
    (s : Finset (Fin n)) (x : Fin s.card → ι → ℂ) :
    m1b_complementCoefficient f s x = ∑ a : Fin s.card → ι,
      (∏ i, x i (a i)) • m1b_complementCoefficient f s (fun i => Pi.single (a i) 1) := by
  let F := (MultilinearMap.compLinearMapₗ
    (fun _ : Fin sᶜ.card => LinearMap.inr ℂ (ι → ℂ) W)).compMultilinearMap
      ((MultilinearMap.curryFinFinset ℂ ℂ ((ι → ℂ) × W) (s := s) rfl rfl f).compLinearMap (fun _ => LinearMap.inl ℂ (ι → ℂ) W))
  exact m1b_multilinear_coordinate_expansion_module F x

def m1b_complementPolynomial {σ κ : Type*} {n : ℕ}
    (P : (s : Finset (Fin n)) → (Fin s.card → ι) →
      MvPolynomial (σ ⊕ (Fin sᶜ.card × κ)) ℂ) :
    MvPolynomial ((Unit ⊕ σ) ⊕ (Fin n × (ι ⊕ κ))) ℂ :=
  ∑ s : Finset (Fin n), MvPolynomial.X (Sum.inl (Sum.inl ())) ^ (s.card / 2) *
    ∑ a : Fin s.card → ι,
      (∏ j, MvPolynomial.X (Sum.inr (s.orderEmbOfFin rfl j, Sum.inl (a j)))) *
        MvPolynomial.rename
          (Sum.elim (fun q => Sum.inl (Sum.inr q))
            (fun q => Sum.inr (sᶜ.orderEmbOfFin rfl q.1, Sum.inr q.2))) (P s a)

theorem m1b_complementPolynomial_eval {σ κ : Type*} {n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => (ι → ℂ) × (κ → ℂ)) ℂ)
    (hf : ∀ v, f (fun i => (-(v i).1, (v i).2)) = f v)
    (P : (s : Finset (Fin n)) → (Fin s.card → ι) →
      MvPolynomial (σ ⊕ (Fin sᶜ.card × κ)) ℂ)
    (z : σ → ℂ) (t : ℂ) (x : Fin n → ι → ℂ) (y v : Fin n → κ → ℂ)
    (hP : ∀ s a, MvPolynomial.eval
      (Sum.elim z (fun q => y (sᶜ.orderEmbOfFin rfl q.1) q.2)) (P s a) =
        m1b_complementCoefficient f s (fun j => Pi.single (a j) 1)
          (fun j => v (sᶜ.orderEmbOfFin rfl j))) :
    MvPolynomial.eval
      (Sum.elim (Sum.elim (fun _ : Unit => t ^ 2) z)
        (fun q => Sum.elim (x q.1) (y q.1) q.2)) (m1b_complementPolynomial P) =
      f (fun i => (t • x i, v i)) := by
  classical
  rw [m1b_complement_even_scale_expansion f hf]
  simp only [m1b_complementPolynomial, map_sum, map_mul, map_pow, map_prod,
    MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr, MvPolynomial.eval_rename]
  apply Finset.sum_congr rfl
  intro s _
  congr 1
  rw [m1b_complementCoefficient_coordinates]
  simp only [sum_apply, smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  convert hP s a using 1
  congr 1
  congr 1
  funext q
  cases q <;> rfl

def m1b_weightedComplementPolynomial {σ κ : Type*} {n : ℕ} (w : ι → ℕ)
    (P : (s : Finset (Fin n)) → (Fin s.card → ι) →
      MvPolynomial (σ ⊕ (Fin sᶜ.card × κ)) ℂ) :
    MvPolynomial ((Unit ⊕ σ) ⊕ (Fin n × (ι ⊕ κ))) ℂ :=
  ∑ s : Finset (Fin n), ∑ a : Fin s.card → ι,
    MvPolynomial.X (Sum.inl (Sum.inl ())) ^ (∑ j, w (a j)) *
      (∏ j, MvPolynomial.X (Sum.inr (s.orderEmbOfFin rfl j, Sum.inl (a j)))) *
        MvPolynomial.rename
          (Sum.elim (fun q => Sum.inl (Sum.inr q))
            (fun q => Sum.inr (sᶜ.orderEmbOfFin rfl q.1, Sum.inr q.2))) (P s a)

theorem m1b_weightedComplementPolynomial_eval {σ κ : Type*} {n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => (ι → ℂ) × (κ → ℂ)) ℂ) (w : ι → ℕ)
    (P : (s : Finset (Fin n)) → (Fin s.card → ι) →
      MvPolynomial (σ ⊕ (Fin sᶜ.card × κ)) ℂ)
    (z : σ → ℂ) (t : ℂ) (x : Fin n → ι → ℂ) (y v : Fin n → κ → ℂ)
    (hP : ∀ s a, MvPolynomial.eval
      (Sum.elim z (fun q => y (sᶜ.orderEmbOfFin rfl q.1) q.2)) (P s a) =
        m1b_complementCoefficient f s (fun j => Pi.single (a j) 1)
          (fun j => v (sᶜ.orderEmbOfFin rfl j))) :
    MvPolynomial.eval
      (Sum.elim (Sum.elim (fun _ : Unit => t) z)
        (fun q => Sum.elim (x q.1) (y q.1) q.2)) (m1b_weightedComplementPolynomial w P) =
      f (fun i => ((fun j => t ^ w j * x i j), v i)) := by
  classical
  rw [m1b_complementCoefficient_expansion]
  simp only [m1b_weightedComplementPolynomial, map_sum, map_mul, map_pow, map_prod,
    MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr, MvPolynomial.eval_rename]
  apply Finset.sum_congr rfl
  intro s _
  rw [m1b_complementCoefficient_coordinates]
  simp only [sum_apply, smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  convert hP s a using 1
  congr 1
  congr 1
  funext q
  cases q <;> rfl

end HodgeLean.Foundations.Program
