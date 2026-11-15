import HodgeLean.Foundations.Program.MilneTensorPairedDiagonal

noncomputable section
namespace HodgeLean.Foundations.Program

theorem m1b_plane_weighted_form
    (B : LinearMap.BilinForm ℂ (Fin 1 ⊕ Fin 1 → ℂ)) (ha : ∀ x, B x x = 0) :
    B = (m1b_weightedJ 1 (fun _ => B (Pi.single (Sum.inl 0) 1)
      (Pi.single (Sum.inr 0) 1))).toBilin' := by
  apply LinearMap.BilinForm.toMatrix'.injective
  rw [LinearMap.BilinForm.toMatrix'_toBilin']
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      fin_cases i
      fin_cases j
      simpa [LinearMap.BilinForm.toMatrix'_apply, m1b_weightedJ,
        Matrix.fromBlocks_apply₁₁, Matrix.zero_apply] using ha (Pi.single (Sum.inl 0) 1)
    | inr j =>
      fin_cases i
      fin_cases j
      simp [LinearMap.BilinForm.toMatrix'_apply, m1b_weightedJ,
        Matrix.fromBlocks_apply₁₂, Matrix.diagonal_apply_eq]
  | inr i =>
    cases j with
    | inl j =>
      fin_cases i
      fin_cases j
      simpa [LinearMap.BilinForm.toMatrix'_apply, m1b_weightedJ,
        Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, Matrix.diagonal_apply_eq] using
        (LinearMap.BilinForm.IsAlt.neg_eq ha (Pi.single (Sum.inl 0) 1)
          (Pi.single (Sum.inr 0) 1)).symm
    | inr j =>
      fin_cases i
      fin_cases j
      simpa [LinearMap.BilinForm.toMatrix'_apply, m1b_weightedJ,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply] using ha (Pi.single (Sum.inr 0) 1)

theorem m1b_plane_pivot_ne_zero
    (B : LinearMap.BilinForm ℂ (Fin 1 ⊕ Fin 1 → ℂ)) (ha : ∀ x, B x x = 0)
    (hB : B.Nondegenerate) : B (Pi.single (Sum.inl 0) 1) (Pi.single (Sum.inr 0) 1) ≠ 0 := by
  intro h
  have hz : B = 0 := by
    rw [m1b_plane_weighted_form B ha, h]
    simp only [m1b_weightedJ, Matrix.diagonal_zero, neg_zero, Matrix.fromBlocks_zero, map_zero]
  have he : (Pi.single (Sum.inl (0 : Fin 1)) (1 : ℂ) : Fin 1 ⊕ Fin 1 → ℂ) = 0 :=
    hB.1 _ (fun y => by rw [hz]; rfl)
  have hh := congrFun he (Sum.inl 0)
  exact one_ne_zero (by simpa only [Pi.single_eq_same, Pi.zero_apply] using hh)

theorem m1b_standard_symplectic_nondegenerate (k : ℕ) :
    (m1b_J k).toBilin'.Nondegenerate := by
  constructor
  · intro x hx
    funext p
    cases p with
    | inl i =>
      have h := hx (Pi.single (Sum.inr i) 1)
      simpa [Matrix.toBilin'_apply, m1b_J, Matrix.one_apply, Pi.single_apply] using h
    | inr i =>
      have h := hx (Pi.single (Sum.inl i) 1)
      simpa [Matrix.toBilin'_apply, m1b_J, Matrix.one_apply, Pi.single_apply] using h
  · intro y hy
    funext p
    cases p with
    | inl i =>
      have h := hy (Pi.single (Sum.inr i) 1)
      simpa [Matrix.toBilin'_apply, m1b_J, Matrix.one_apply, Pi.single_apply] using h
    | inr i =>
      have h := hy (Pi.single (Sum.inl i) 1)
      simpa [Matrix.toBilin'_apply, m1b_J, Matrix.one_apply, Pi.single_apply] using h

theorem m1b_standard_symplectic_alternating (k : ℕ) (x : Fin k ⊕ Fin k → ℂ) :
    (m1b_J k).toBilin' x x = 0 := by
  simp [Matrix.toBilin'_apply, m1b_J, Matrix.one_apply, mul_comm]

theorem m1b_symplectic_plane_polynomial {r n : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → Fin 1 ⊕ Fin 1 → ℂ) ℂ)
    (hf : ∀ u ∈ m1b_isometries (m1b_J 1).toBilin', ∀ v,
      f (fun j => m1b_copies r u (v j)) = f v) :
    ∃ P : MvPolynomial (((Fin 1 ⊕ Fin 1) × (Fin 1 ⊕ Fin 1)) ⊕
        (Fin n × (Fin r × (Fin 1 ⊕ Fin 1)))) ℂ,
      ∀ (e : (Fin 1 ⊕ Fin 1 → ℂ) ≃ₗ[ℂ] (Fin 1 ⊕ Fin 1 → ℂ))
        (v : Fin n → Fin r → Fin 1 ⊕ Fin 1 → ℂ),
        MvPolynomial.eval (Sum.elim
          (fun ij => m1b_formTransport (m1b_J 1).toBilin' e
            (Pi.single ij.1 1) (Pi.single ij.2 1))
          (fun ij => v ij.1 ij.2.1 ij.2.2)) P = f (fun i j => e.symm (v i j)) := by
  classical
  refine ⟨MvPolynomial.rename
    (Sum.map (fun _ : Fin 1 => (Sum.inl 0, Sum.inr 0)) id)
      (m1b_pairedDiagonalPolynomial f), ?_⟩
  intro e v
  let B := m1b_formTransport (m1b_J 1).toBilin' e
  have ha : ∀ x, B x x = 0 := fun x => m1b_standard_symplectic_alternating 1 (e.symm x)
  let a := B (Pi.single (Sum.inl 0) 1) (Pi.single (Sum.inr 0) 1)
  have ha0 : a ≠ 0 := m1b_plane_pivot_ne_zero B ha
    (m1b_nondegenerate_transport e _ (m1b_standard_symplectic_nondegenerate 1))
  let s : Fin 1 → ℂˣ := fun _ => Units.mk0 a ha0
  have htrans : m1b_formTransport (m1b_J 1).toBilin' (m1b_leftScaleEquiv 1 s).symm =
      m1b_formTransport (m1b_J 1).toBilin' e := by
    rw [m1b_weightedJ_transport]
    exact (m1b_plane_weighted_form B ha).symm
  have h := congrArg (fun g : MultilinearMap ℂ
    (fun _ : Fin n => Fin r → Fin 1 ⊕ Fin 1 → ℂ) ℂ => g v)
      (m1b_multilinear_transport_independent (m1b_J 1).toBilin' f hf
        (m1b_leftScaleEquiv 1 s).symm e htrans)
  rw [MvPolynomial.eval_rename]
  have hev : (Sum.elim
      (fun ij => m1b_formTransport (m1b_J 1).toBilin' e
        (Pi.single ij.1 1) (Pi.single ij.2 1))
      (fun ij : Fin n × (Fin r × (Fin 1 ⊕ Fin 1)) => v ij.1 ij.2.1 ij.2.2)) ∘
        Sum.map (fun _ : Fin 1 => (Sum.inl 0, Sum.inr 0)) id =
      Sum.elim (fun _ : Fin 1 => a)
        (fun ij : Fin n × (Fin r × (Fin 1 ⊕ Fin 1)) => v ij.1 ij.2.1 ij.2.2) := by
    funext q
    cases q <;> rfl
  rw [hev, m1b_pairedDiagonalPolynomial_eval]
  calc
    f (fun i c p => Sum.elim (fun _ => a) (fun _ => 1) p * v i c p) =
        f (fun i c => m1b_leftScaleEquiv 1 s (v i c)) := by
      apply congrArg f
      funext i c p
      exact (m1b_leftScaleEquiv_apply 1 s (v i c) p).symm
    _ = f (fun i j => e.symm (v i j)) := h

end HodgeLean.Foundations.Program
