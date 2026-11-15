import HodgeLean.Foundations.Program.MilneTensorPairTotalNumerator
import HodgeLean.Foundations.Program.MilneTensorPairCoordinates
import HodgeLean.Foundations.Program.MilneTensorMatrixAlternating

noncomputable section
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem m1b_pair_matrix_numerator {d r n : ℕ}
    (B : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × (Fin d → ℂ)))
    (hB : B.Nondegenerate) (haB : ∀ x, B x x = 0)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → (Fin 2 → ℂ) × (Fin d → ℂ)) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v, f (fun j => m1b_copies r u (v j)) = f v)
    (k : ℕ) (q : MvPolynomial (((Fin 2 ⊕ Fin d) × (Fin 2 ⊕ Fin d)) ⊕
      (Fin n × (Fin r × (Fin 2 ⊕ Fin d)))) ℂ)
    (hq : ∀ Q : LinearMap.BilinForm ℂ ((Fin 2 → ℂ) × (Fin d → ℂ)), Q.Nondegenerate →
      (∀ x, Q x x = 0) → Q (Pi.single 0 1, 0) (Pi.single 1 1, 0) ≠ 0 → ∀ v,
        MvPolynomial.eval (m1b_pairFormPoint Q v) q =
          Q (Pi.single 0 1, 0) (Pi.single 1 1, 0) ^ k * m1b_totalOrbitExtension B f Q v) :
    ∀ Q : Matrix (Fin 2 ⊕ Fin d) (Fin 2 ⊕ Fin d) ℂ,
      Q.transpose = -Q → Q.det ≠ 0 → Q (Sum.inl 0) (Sum.inl 1) ≠ 0 →
      ∀ v : Fin n → Fin r → Fin 2 ⊕ Fin d → ℂ,
        MvPolynomial.eval (Sum.elim (fun st => Q st.1 st.2)
          (fun tc => v tc.1 tc.2.1 tc.2.2)) q = Q (Sum.inl 0) (Sum.inl 1) ^ k *
          m1b_totalOrbitExtension
            (B.compl₁₂ (m1b_pairCoordinates d).toLinearMap (m1b_pairCoordinates d).toLinearMap)
            (f.compLinearMap (fun _ =>
              (m1b_copiesEquiv (m1b_pairCoordinates d).symm r).symm.toLinearMap)) Q.toBilin' v := by
  intro Q hQ hdQ hiQ v
  let e := m1b_pairCoordinates d
  let Qp := Q.toBilin'.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap
  have hQp : Qp.Nondegenerate := m1b_nondegenerate_transport e Q.toBilin'
    (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdQ)
  have haQp (x) : Qp x x = 0 := m1b_matrix_bilin_alternating Q hQ (e.symm x)
  have hp : Qp (Pi.single 0 1, 0) (Pi.single 1 1, 0) = Q (Sum.inl 0) (Sum.inl 1) := by
    change Q.toBilin' (e.symm (Pi.single 0 1, 0)) (e.symm (Pi.single 1 1, 0)) = _
    have he (i : Fin 2) : e.symm (Pi.single i 1, 0) = Pi.single (Sum.inl i) (1 : ℂ) := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      exact (m1b_pairCoordinates_basis d (Sum.inl i)).symm
    rw [he, he]
    exact Matrix.toBilin'_single Q (Sum.inl 0) (Sum.inl 1)
  have hmem := m1b_alternating_forms_same_orbit B Qp hB hQp haB haQp
  have hc := m1b_totalOrbitExtension_coordinate_transport e.symm B f hf Qp hmem v
  have hQQ : Qp.compl₁₂ e.toLinearMap e.toLinearMap = Q.toBilin' := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Q.toBilin' (e.symm (e x)) (e.symm (e y)) = Q.toBilin' x y
    simp only [LinearEquiv.symm_apply_apply]
  simp only [LinearEquiv.symm_symm, hQQ] at hc
  have he := hq Qp hQp haQp (by rw [hp]; exact hiQ) (fun j c => e (v j c))
  rw [m1b_pairFormPoint_coordinates, hp] at he
  exact he.trans (congrArg (fun z => Q (Sum.inl 0) (Sum.inl 1) ^ k * z) hc.symm)

end HodgeLean.Foundations.Program
