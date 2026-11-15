import HodgeLean.Foundations.Program.MilneTensorPairMatrixNumerator
import HodgeLean.Foundations.Program.MilneTensorAlternatingAssembly
import HodgeLean.Foundations.Program.MilneTensorPairModel
import HodgeLean.Foundations.Program.MilneTensorProductForm
import HodgeLean.Foundations.Program.MilneTensorEquivMatrix
import Mathlib.Order.Sum.Order

noncomputable section
open Matrix
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem m1b_alternating_pair_induction_step {d r n : ℕ} (hd : 0 < d)
    (B : LinearMap.BilinForm ℂ (Fin d → ℂ)) (hB : B.Nondegenerate) (haB : ∀ x, B x x = 0)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → (Fin 2 → ℂ) × (Fin d → ℂ)) ℂ)
    (hf : ∀ u ∈ m1b_isometries (m1b_prodBilin m1b_pairForm B),
      ∀ v, f (fun t => m1b_copies r u (v t)) = f v)
    (hsmall : ∀ m (g : MultilinearMap ℂ (fun _ : Fin m => Fin r → Fin d → ℂ) ℂ),
      (∀ u ∈ m1b_isometries B, ∀ v, g (fun t => m1b_copies r u (v t)) = g v) →
      ∃ P : MvPolynomial ((Fin d × Fin d) ⊕ (Fin m × (Fin r × Fin d))) ℂ,
        ∀ (e : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d → ℂ)) (v : Fin m → Fin r → Fin d → ℂ),
          MvPolynomial.eval (Sum.elim
            (fun ij => m1b_formTransport B e (Pi.single ij.1 1) (Pi.single ij.2 1))
            (fun tc => v tc.1 tc.2.1 tc.2.2)) P = g (fun t c => e.symm (v t c))) :
    ∃ P : MvPolynomial (((Fin 2 ⊕ Fin d) × (Fin 2 ⊕ Fin d)) ⊕
      (Fin n × (Fin r × (Fin 2 ⊕ Fin d)))) ℂ,
      ∀ (t : (Fin 2 ⊕ Fin d → ℂ) ≃ₗ[ℂ] (Fin 2 ⊕ Fin d → ℂ))
        (v : Fin n → Fin r → Fin 2 ⊕ Fin d → ℂ),
          MvPolynomial.eval (Sum.elim
            (fun ij => m1b_formTransport
              ((m1b_prodBilin m1b_pairForm B).compl₁₂
                (m1b_pairCoordinates d).toLinearMap (m1b_pairCoordinates d).toLinearMap) t
              (Pi.single ij.1 1) (Pi.single ij.2 1))
            (fun tc => v tc.1 tc.2.1 tc.2.2)) P =
              f (fun j c => m1b_pairCoordinates d (t.symm (v j c))) := by
  letI sumOrder : LinearOrder (Fin 2 ⊕ Fin d) := inferInstanceAs (LinearOrder (Fin 2 ⊕ₗ Fin d))
  letI : LT (Fin 2 ⊕ Fin d) := sumOrder.toLT
  letI : LE (Fin 2 ⊕ Fin d) := sumOrder.toLE
  let c := m1b_pairCoordinates d
  let Bp := m1b_prodBilin m1b_pairForm B
  let Br := Bp.compl₁₂ c.toLinearMap c.toLinearMap
  let C := LinearMap.BilinForm.toMatrix' Br
  have hC : C.toBilin' = Br := Matrix.toBilin'_toMatrix' Br
  have hBp : Bp.Nondegenerate := m1b_prodBilin_nondegenerate _ _ m1b_pairForm_nondegenerate hB
  have haBp (x) : Bp x x = 0 := by
    change m1b_pairForm x.1 x.1 + B x.2 x.2 = 0
    rw [m1b_pairForm_alternating, haB, add_zero]
  have hBr : Br.Nondegenerate := m1b_nondegenerate_transport c.symm Bp hBp
  have haBr (x) : Br x x = 0 := haBp (c x)
  have hskewC (i j) : C j i = -C i j := by
    change Br (Pi.single j 1) (Pi.single i 1) = -Br (Pi.single i 1) (Pi.single j 1)
    exact (LinearMap.BilinForm.IsAlt.neg_eq haBr _ _).symm
  have hdC : C.det ≠ 0 := LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mp
    (by rw [hC]; exact hBr)
  have hiC : C (Sum.inl 0) (Sum.inl 1) ≠ 0 := by
    change Bp (c (Pi.single (Sum.inl 0) 1)) (c (Pi.single (Sum.inl 1) 1)) ≠ 0
    rw [m1b_pairCoordinates_basis, m1b_pairCoordinates_basis]
    change (1 * 1 - 0 * 0 : ℂ) + B 0 0 ≠ 0
    simp
  let g := f.compLinearMap (fun _ => (m1b_copiesEquiv c.symm r).symm.toLinearMap)
  have hg : ∀ u ∈ m1b_isometries C.toBilin', ∀ v,
      g (fun j => m1b_copies r u (v j)) = g v := by
    intro u hu v
    apply m1b_multilinear_invariant_transport c.symm Bp f hf u _ v
    simpa only [LinearEquiv.symm_symm, hC] using hu
  obtain ⟨k, a, ha⟩ := m1b_alternating_pair_orbit_numerator B hB haB f hf hsmall
  have hat := m1b_pair_numerator_on_all_forms Bp hBp haBp f k a ha
  have ham := m1b_pair_matrix_numerator Bp hBp haBp f hf k a hat
  change ∀ Q : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ, Q.transpose = -Q → Q.det ≠ 0 → Q (Sum.inl 0) (Sum.inl 1) ≠ 0 → ∀ v : Fin n → Fin r → Fin 2 ⊕ Fin d → ℂ,
    MvPolynomial.eval _ a = Q (Sum.inl 0) (Sum.inl 1) ^ k *
      m1b_totalOrbitExtension Br g Q.toBilin' v at ham
  rw [← hC] at ham
  let p₀ : {p : (Fin 2 ⊕ Fin d) × (Fin 2 ⊕ Fin d) // p.1 < p.2} :=
    ⟨(Sum.inl 0, Sum.inl 1), Sum.Lex.inl_lt_inl_iff.mpr (show (0 : Fin 2) < 1 from by decide)⟩
  let p₁ : {p : (Fin 2 ⊕ Fin d) × (Fin 2 ⊕ Fin d) // p.1 < p.2} :=
    ⟨(Sum.inl 0, Sum.inr ⟨0, hd⟩), Sum.Lex.inl_lt_inr _ _⟩
  let e := Equiv.swap (Sum.inl (1 : Fin 2)) (Sum.inr (⟨0, hd⟩ : Fin d))
  obtain ⟨P, hP⟩ := m1b_alternating_orbit_polynomial_from_numerator C hskewC hdC p₀ p₁
    (by intro h; have h' := congrArg (fun p => p.val.2) h; cases h') e
    (by simp [e, p₀, p₁, Equiv.swap_apply_def])
    (by simp [e, p₀, p₁]) hiC g hg a k (by
      intro Q hQ _ hdQ hiQ v
      exact ham Q (by ext i j; exact hQ i j) hdQ hiQ v)
  refine ⟨P, ?_⟩
  intro t v
  have he := m1b_matrix_polynomial_linearEquiv C g P hP t v
  rw [hC] at he
  exact he

end HodgeLean.Foundations.Program
