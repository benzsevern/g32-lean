import HodgeLean.Foundations.Program.MilneTensorCoefficientPolynomial
import HodgeLean.Foundations.Program.MilneTensorDiagonal

noncomputable section
namespace HodgeLean.Foundations.Program

def m1b_scalarSplitCopies (r d : ℕ) :
    ((Fin r → ℂ) × ((Fin r × Fin d) → ℂ)) →ₗ[ℂ] (Fin r → ℂ × (Fin d → ℂ)) where
  toFun v i := (v.1 i, fun j => v.2 (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem m1b_scalar_split_polynomial {d r n : ℕ}
    (A : LinearMap.BilinForm ℂ ℂ) (B : LinearMap.BilinForm ℂ (Fin d → ℂ))
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ℂ × (Fin d → ℂ)) ℂ)
    (hf : ∀ u ∈ m1b_isometries (m1b_prodBilin A B),
      ∀ v, f (fun i => m1b_copies r u (v i)) = f v)
    (hsmall : ∀ m (g : MultilinearMap ℂ (fun _ : Fin m => Fin r → Fin d → ℂ) ℂ),
      (∀ u ∈ m1b_isometries B, ∀ v, g (fun i => m1b_copies r u (v i)) = g v) →
      ∃ P : MvPolynomial ((Fin d × Fin d) ⊕ (Fin m × (Fin r × Fin d))) ℂ,
        ∀ (e : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)) (v : Fin m → Fin r → Fin d → ℂ),
          MvPolynomial.eval (Sum.elim
            (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
            (fun ij => v ij.1 ij.2.1 ij.2.2)) P = g (fun i j => e.symm (v i j))) :
    ∃ P : MvPolynomial ((Unit ⊕ (Fin d × Fin d)) ⊕
        (Fin n × (Fin r ⊕ (Fin r × Fin d)))) ℂ,
      ∀ (e : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)) (t : ℂ)
        (x : Fin n → Fin r → ℂ) (y : Fin n → Fin r → Fin d → ℂ),
        MvPolynomial.eval (Sum.elim
          (Sum.elim (fun _ => t ^ 2)
            (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1)))
          (fun jc => Sum.elim (x jc.1) (fun ci => y jc.1 ci.1 ci.2) jc.2)) P =
          f (fun i j => (t * x i j, e.symm (y i j))) := by
  classical
  let F := f.compLinearMap (fun _ => m1b_scalarSplitCopies r d)
  let g (s : Finset (Fin n)) (a : Fin s.card → Fin r) :=
    m1b_complementCoefficient (f.compLinearMap (fun _ => m1b_splitCopies r)) s
      (fun j => Pi.single (a j) 1)
  have hg (s : Finset (Fin n)) (a : Fin s.card → Fin r) :
      ∀ u ∈ m1b_isometries B, ∀ v,
        g s a (fun i => m1b_copies r u (v i)) = g s a v := by
    intro u hu v
    exact m1b_complementCoefficient_isometry A B f hf s _ u hu v
  choose P hP using fun s a => hsmall sᶜ.card (g s a) (hg s a)
  refine ⟨m1b_complementPolynomial P, ?_⟩
  intro e t x y
  have hF : ∀ v, F (fun i => (-(v i).1, (v i).2)) = F v := by
    intro v
    exact hf ((-LinearMap.id).prodMap LinearMap.id) (m1b_prod_reflection_isometry A B)
      (fun i => m1b_scalarSplitCopies r d (v i))
  apply m1b_complementPolynomial_eval F hF P
    (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1)) t x
    (fun i ci => y i ci.1 ci.2) (fun i ci => e.symm (y i ci.1) ci.2)
  intro s a
  rw [hP s a e (fun j => y (sᶜ.orderEmbOfFin rfl j))]
  dsimp only [g]
  rw [m1b_complementCoefficient_apply, m1b_complementCoefficient_apply]
  apply congrArg f
  funext i j
  dsimp only
  cases h : (finSumEquivOfFinset (s := s) rfl rfl).symm i <;> rfl

def m1b_pairedSplitCopies (r d : ℕ) :
    (((Fin r × Fin 2) → ℂ) × ((Fin r × Fin d) → ℂ)) →ₗ[ℂ]
      (Fin r → (Fin 2 → ℂ) × (Fin d → ℂ)) where
  toFun v i := ((fun j => v.1 (i, j)), fun j => v.2 (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem m1b_paired_split_polynomial {d r n : ℕ}
    (A : LinearMap.BilinForm ℂ (Fin 2 → ℂ)) (B : LinearMap.BilinForm ℂ (Fin d → ℂ))
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → (Fin 2 → ℂ) × (Fin d → ℂ)) ℂ)
    (hf : ∀ u ∈ m1b_isometries (m1b_prodBilin A B),
      ∀ v, f (fun i => m1b_copies r u (v i)) = f v)
    (hsmall : ∀ m (g : MultilinearMap ℂ (fun _ : Fin m => Fin r → Fin d → ℂ) ℂ),
      (∀ u ∈ m1b_isometries B, ∀ v, g (fun i => m1b_copies r u (v i)) = g v) →
      ∃ P : MvPolynomial ((Fin d × Fin d) ⊕ (Fin m × (Fin r × Fin d))) ℂ,
        ∀ (e : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)) (v : Fin m → Fin r → Fin d → ℂ),
          MvPolynomial.eval (Sum.elim
            (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
            (fun ij => v ij.1 ij.2.1 ij.2.2)) P = g (fun i j => e.symm (v i j))) :
    ∃ P : MvPolynomial ((Unit ⊕ (Fin d × Fin d)) ⊕
        (Fin n × ((Fin r × Fin 2) ⊕ (Fin r × Fin d)))) ℂ,
      ∀ (e : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)) (t : ℂ)
        (x : Fin n → Fin r → Fin 2 → ℂ) (y : Fin n → Fin r → Fin d → ℂ),
        MvPolynomial.eval (Sum.elim
          (Sum.elim (fun _ => t)
            (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1)))
          (fun jc => Sum.elim (fun ci => x jc.1 ci.1 ci.2)
            (fun ci => y jc.1 ci.1 ci.2) jc.2)) P =
          f (fun i j => ((fun k => (if k = 0 then t else 1) * x i j k), e.symm (y i j))) := by
  classical
  let F := f.compLinearMap (fun _ => m1b_pairedSplitCopies r d)
  let g (s : Finset (Fin n)) (a : Fin s.card → Fin r × Fin 2) :=
    m1b_complementCoefficient (f.compLinearMap (fun _ => m1b_splitCopies r)) s
      (fun j c k => (Pi.single (a j) (1 : ℂ) : (Fin r × Fin 2) → ℂ) (c, k))
  have hg (s : Finset (Fin n)) (a : Fin s.card → Fin r × Fin 2) :
      ∀ u ∈ m1b_isometries B, ∀ v,
        g s a (fun i => m1b_copies r u (v i)) = g s a v := by
    intro u hu v
    exact m1b_complementCoefficient_isometry A B f hf s _ u hu v
  choose P hP using fun s a => hsmall sᶜ.card (g s a) (hg s a)
  let w : Fin r × Fin 2 → ℕ := fun ci => if ci.2 = 0 then 1 else 0
  refine ⟨m1b_weightedComplementPolynomial w P, ?_⟩
  intro e t x y
  have h := m1b_weightedComplementPolynomial_eval F w P
    (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1)) t
    (fun i ci => x i ci.1 ci.2) (fun i ci => y i ci.1 ci.2)
    (fun i ci => e.symm (y i ci.1) ci.2) (by
      intro s a
      rw [hP s a e (fun j => y (sᶜ.orderEmbOfFin rfl j))]
      dsimp only [g]
      rw [m1b_complementCoefficient_apply, m1b_complementCoefficient_apply]
      apply congrArg f
      funext i j
      dsimp only
      cases h : (finSumEquivOfFinset (s := s) rfl rfl).symm i <;> rfl)
  rw [h]
  apply congrArg f
  funext i j
  apply Prod.ext
  · funext k
    change t ^ (if k = 0 then 1 else 0) * x i j k =
      (if k = 0 then t else 1) * x i j k
    by_cases hk : k = 0 <;> simp only [hk, ite_true, ite_false, pow_one, pow_zero]
  · rfl

theorem m1b_zero_form_polynomial {r n : ℕ}
    (B : LinearMap.BilinForm ℂ (Fin 0 → ℂ))
    (g : MultilinearMap ℂ (fun _ : Fin n => Fin r → Fin 0 → ℂ) ℂ) :
    ∃ P : MvPolynomial ((Fin 0 × Fin 0) ⊕ (Fin n × (Fin r × Fin 0))) ℂ,
      ∀ (e : (Fin 0 → ℂ) ≃ₗ[ℂ] (Fin 0 → ℂ)) (v : Fin n → Fin r → Fin 0 → ℂ),
        MvPolynomial.eval (Sum.elim
          (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
          (fun ij => v ij.1 ij.2.1 ij.2.2)) P = g (fun i j => e.symm (v i j)) := by
  refine ⟨MvPolynomial.C (g 0), ?_⟩
  intro e v
  rw [MvPolynomial.eval_C]
  exact congrArg g (Subsingleton.elim _ _)

end HodgeLean.Foundations.Program
