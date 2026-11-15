import HodgeLean.Foundations.Program.MilneTensorDiagonal
import HodgeLean.Foundations.Program.MilneTensorOrbit

noncomputable section
namespace HodgeLean.Foundations.Program

def m1b_weightedJ (k : ℕ) (s : Fin k → ℂ) :
    Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℂ :=
  Matrix.fromBlocks 0 (Matrix.diagonal s) (-Matrix.diagonal s) 0

def m1b_leftScaleMatrix (k : ℕ) (s : Fin k → ℂ) :
    Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℂ :=
  Matrix.fromBlocks (Matrix.diagonal s) 0 0 1

theorem m1b_leftScale_congruence (k : ℕ) (s : Fin k → ℂ) :
    (m1b_leftScaleMatrix k s).transpose * m1b_J k * m1b_leftScaleMatrix k s =
      m1b_weightedJ k s := by
  simp [m1b_leftScaleMatrix, m1b_J, m1b_weightedJ, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply]

def m1b_leftScaleUnit (k : ℕ) (s : Fin k → ℂˣ) :
    (Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℂ)ˣ where
  val := m1b_leftScaleMatrix k (fun i => (s i).val)
  inv := m1b_leftScaleMatrix k (fun i => (s i).inv)
  val_inv := by
    simp [m1b_leftScaleMatrix, Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal]
  inv_val := by
    simp [m1b_leftScaleMatrix, Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal]

def m1b_leftScaleEquiv (k : ℕ) (s : Fin k → ℂˣ) :
    (Fin k ⊕ Fin k → ℂ) ≃ₗ[ℂ] (Fin k ⊕ Fin k → ℂ) :=
  Matrix.toLin'OfInv (m1b_leftScaleUnit k s).inv_val (m1b_leftScaleUnit k s).val_inv

theorem m1b_weightedJ_transport (k : ℕ) (s : Fin k → ℂˣ) :
    m1b_formTransport (m1b_J k).toBilin' (m1b_leftScaleEquiv k s).symm =
      (m1b_weightedJ k (fun i => (s i).val)).toBilin' := by
  change (m1b_J k).toBilin'.comp
    (m1b_leftScaleMatrix k (fun i => (s i).val)).toLin'
    (m1b_leftScaleMatrix k (fun i => (s i).val)).toLin' = _
  rw [Matrix.toBilin'_comp, m1b_leftScale_congruence]

theorem m1b_leftScaleEquiv_apply (k : ℕ) (s : Fin k → ℂˣ)
    (x : Fin k ⊕ Fin k → ℂ) (p : Fin k ⊕ Fin k) :
    m1b_leftScaleEquiv k s x p = Sum.elim (fun i => (s i).val) (fun _ => 1) p * x p := by
  change (m1b_leftScaleMatrix k (fun i => (s i).val)).mulVec x p = _
  cases p <;> simp [m1b_leftScaleMatrix, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Matrix.one_apply]

def m1b_pairedDiagonalPolynomial {k r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → Fin k ⊕ Fin k → ℂ) ℂ) :
    MvPolynomial (Fin k ⊕ (Fin n × (Fin r × (Fin k ⊕ Fin k)))) ℂ :=
  let g := f.compLinearMap (fun _ => m1b_copyCoordinates (ι := Fin k ⊕ Fin k) r)
  ∑ a : Fin n → Fin r × (Fin k ⊕ Fin k),
    MvPolynomial.C (g (fun i => Pi.single (a i) 1)) *
      ∏ i, Sum.elim (fun j => MvPolynomial.X (Sum.inl j)) (fun _ => 1) (a i).2 *
        MvPolynomial.X (Sum.inr (i, a i))

theorem m1b_pairedDiagonalPolynomial_eval {k r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → Fin k ⊕ Fin k → ℂ) ℂ)
    (s : Fin k → ℂ) (v : Fin n → Fin r → Fin k ⊕ Fin k → ℂ) :
    MvPolynomial.eval (Sum.elim s
      (fun p : Fin n × (Fin r × (Fin k ⊕ Fin k)) => v p.1 p.2.1 p.2.2))
      (m1b_pairedDiagonalPolynomial f) =
      f (fun i a p => Sum.elim s (fun _ => 1) p * v i a p) := by
  let g := f.compLinearMap (fun _ => m1b_copyCoordinates (ι := Fin k ⊕ Fin k) r)
  let ev := MvPolynomial.eval (Sum.elim s
    (fun p : Fin n × (Fin r × (Fin k ⊕ Fin k)) => v p.1 p.2.1 p.2.2))
  have hC (c : ℂ) : ev (MvPolynomial.C c) = c := by simp [ev]
  have hX (i : Fin n) (a : Fin r × (Fin k ⊕ Fin k)) :
      ev (MvPolynomial.X (Sum.inr (i, a))) = v i a.1 a.2 := by simp [ev]
  have hs (p : Fin k ⊕ Fin k) :
      ev (Sum.elim (fun j => MvPolynomial.X (Sum.inl j)) (fun _ => 1) p) =
        Sum.elim s (fun _ => 1) p := by
    cases p <;> simp [ev]
  change ev (m1b_pairedDiagonalPolynomial f) =
    g (fun i a => Sum.elim s (fun _ => 1) a.2 * v i a.1 a.2)
  rw [m1b_multilinear_coordinate_expansion]
  simp only [m1b_pairedDiagonalPolynomial, map_sum, map_mul, map_prod, hC, hX, hs]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem m1b_symplectic_diagonal_extension {k r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → Fin k ⊕ Fin k → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries (m1b_J k).toBilin', ∀ v,
      f (fun j => m1b_copies r u (v j)) = f v)
    (s : Fin k → ℂˣ) (v : Fin n → Fin r → Fin k ⊕ Fin k → ℂ) :
    MvPolynomial.eval (Sum.elim (fun i => (s i).val)
      (fun p : Fin n × (Fin r × (Fin k ⊕ Fin k)) => v p.1 p.2.1 p.2.2))
      (m1b_pairedDiagonalPolynomial f) =
      m1b_orbitExtension (m1b_J k).toBilin' f
        ⟨(m1b_weightedJ k (fun i => (s i).val)).toBilin',
          ⟨(m1b_leftScaleEquiv k s).symm, m1b_weightedJ_transport k s⟩⟩ v := by
  rw [m1b_pairedDiagonalPolynomial_eval,
    m1b_orbitExtension_eval (m1b_J k).toBilin' f hf _
      (m1b_leftScaleEquiv k s).symm (m1b_weightedJ_transport k s)]
  change f (fun i a p => Sum.elim (fun j => (s j).val) (fun _ => 1) p * v i a p) =
    f (fun i a => m1b_leftScaleEquiv k s (v i a))
  apply congrArg f
  funext i a p
  exact (m1b_leftScaleEquiv_apply k s (v i a) p).symm

end HodgeLean.Foundations.Program
