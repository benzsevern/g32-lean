import HodgeLean.Foundations.Program.MilneTensorScalarTotalNumerator
import HodgeLean.Foundations.Program.MilneTensorScalarPoint
import HodgeLean.Foundations.Program.MilneTensorTotalCoordinates

noncomputable section
namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000 in
theorem m1b_scalar_matrix_numerator {d r n : ℕ}
    (B : LinearMap.BilinForm ℂ (ℂ × (Fin d → ℂ)))
    (hB : B.Nondegenerate) (hsB : ∀ x y, B x y = B y x)
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin r → ℂ × (Fin d → ℂ)) ℂ)
    (hf : ∀ u ∈ m1b_isometries B, ∀ v, f (fun j => m1b_copies r u (v j)) = f v)
    (k : ℕ) (q : MvPolynomial (((Unit ⊕ Fin d) × (Unit ⊕ Fin d)) ⊕
      (Fin n × (Fin r × (Unit ⊕ Fin d)))) ℂ)
    (hq : ∀ (Q : LinearMap.BilinForm ℂ (ℂ × (Fin d → ℂ))), Q.Nondegenerate →
      (∀ x y, Q x y = Q y x) → Q (1, 0) (1, 0) ≠ 0 → ∀ v,
        MvPolynomial.eval (m1b_scalarFormPoint Q v) q =
          Q (1, 0) (1, 0) ^ k * m1b_totalOrbitExtension B f Q v) :
    ∀ (Q : Matrix (Unit ⊕ Fin d) (Unit ⊕ Fin d) ℂ),
      (∀ s t, Q s t = Q t s) → Q.det ≠ 0 → Q (Sum.inl ()) (Sum.inl ()) ≠ 0 →
      ∀ v : Fin n → Fin r → Unit ⊕ Fin d → ℂ,
        MvPolynomial.eval (Sum.elim (fun st => Q st.1 st.2)
          (fun tc => v tc.1 tc.2.1 tc.2.2)) q =
            Q (Sum.inl ()) (Sum.inl ()) ^ k *
              m1b_totalOrbitExtension
                (B.compl₁₂ (m1b_scalarCoordinates d).toLinearMap
                  (m1b_scalarCoordinates d).toLinearMap)
                (f.compLinearMap (fun _ =>
                  (m1b_copiesEquiv (m1b_scalarCoordinates d).symm r).symm.toLinearMap))
                Q.toBilin' v := by
  intro Q hsQ hdQ hiQ v
  let e := m1b_scalarCoordinates d
  let Qp := Q.toBilin'.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap
  have hQp : Qp.Nondegenerate := m1b_nondegenerate_transport e Q.toBilin'
    (LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdQ)
  have hsQ' : Q.toBilin'.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr
    (Matrix.IsSymm.ext_iff.mpr (fun s t => hsQ t s))
  have hsQp : ∀ x y, Qp x y = Qp y x :=
    fun x y => hsQ'.eq (e.symm x) (e.symm y)
  have hp : Qp (1, 0) (1, 0) = Q (Sum.inl ()) (Sum.inl ()) := by
    change Q.toBilin' (e.symm (1, 0)) (e.symm (1, 0)) = _
    have he : e.symm (1, 0) = Pi.single (Sum.inl ()) (1 : ℂ) := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      exact (m1b_scalarCoordinates_basis d (Sum.inl ())).symm
    rw [he]
    exact Matrix.toBilin'_single Q (Sum.inl ()) (Sum.inl ())
  have hmem := m1b_symmetric_forms_same_orbit B Qp hB hQp hsB hsQp
  have hc := m1b_totalOrbitExtension_coordinate_transport e.symm B f hf Qp hmem v
  have hQQ : Qp.compl₁₂ e.toLinearMap e.toLinearMap = Q.toBilin' := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Q.toBilin' (e.symm (e x)) (e.symm (e y)) = Q.toBilin' x y
    simp only [LinearEquiv.symm_apply_apply]
  simp only [LinearEquiv.symm_symm, hQQ] at hc
  have he := hq Qp hQp hsQp (by rw [hp]; exact hiQ) (fun j c => e (v j c))
  rw [m1b_scalarFormPoint_coordinates, hp] at he
  exact he.trans (congrArg (fun z => Q (Sum.inl ()) (Sum.inl ()) ^ k * z) hc.symm)

end HodgeLean.Foundations.Program
