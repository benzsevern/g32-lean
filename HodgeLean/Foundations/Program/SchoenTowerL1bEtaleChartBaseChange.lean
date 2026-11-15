import HodgeLean.Foundations.Program.SchoenTowerL1bCoordinateChart
import Mathlib.RingTheory.RingHom.Etale

/-! Etale coordinates on the base change of a polynomial blowup chart.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct
universe u
namespace HodgeLean.Foundations.Program

/-- The base change of a coordinate blowup chart has etale polynomial coordinates.
The original centre coordinate is the ratio times the exceptional coordinate;
every other original coordinate and every ground coefficient is retained. -/
theorem s2v_l1b_etale_chart_baseChange
    {k R σ : Type u} [CommRing k] [CommRing R] [DecidableEq σ]
    [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
    (a b : σ) (hab : a ≠ b) :
    let P := MvPolynomial σ k
    let Q := s2v_L1bChart (MvPolynomial.X a : P) (MvPolynomial.X b)
    let T := Q ⊗[P] R
    ∃ (c : k →+* T) (z : σ → T),
      (MvPolynomial.eval₂Hom c z).Etale ∧
      (∀ d, c d = Algebra.TensorProduct.includeRight
        (algebraMap P R (MvPolynomial.C d))) ∧
      (∀ j, Algebra.TensorProduct.includeRight
        (algebraMap P R (MvPolynomial.X j)) =
          if j = a then z a * z b else z j) := by
  dsimp only
  let P := MvPolynomial σ k
  let Q := s2v_L1bChart (MvPolynomial.X a : P) (MvPolynomial.X b)
  let T := Q ⊗[P] R
  let q := Ideal.Quotient.mk (Ideal.span
    {Polynomial.C (MvPolynomial.X a : P) - Polynomial.X * Polynomial.C (MvPolynomial.X b)})
  obtain ⟨e, heC, heX⟩ := s2v_l1b_coordinate_chart_equiv (R := k) a b hab
  let l : Q →+* T := algebraMap Q T
  let F : P →+* T := l.comp e.symm.toRingHom
  have hF : (MvPolynomial.eval₂Hom (F.comp MvPolynomial.C)
      (fun j => F (MvPolynomial.X j))) = F := by
    apply MvPolynomial.ringHom_ext
    · intro d
      exact MvPolynomial.eval₂Hom_C _ _ _
    · intro j
      exact MvPolynomial.eval₂Hom_X' _ _ _
  refine ⟨F.comp MvPolynomial.C, fun j => F (MvPolynomial.X j), ?_, ?_, ?_⟩
  · rw [hF]
    exact RingHom.Etale.stableUnderComposition e.symm.toRingHom l
      (RingHom.Etale.of_bijective e.symm.bijective)
      ((RingHom.etale_algebraMap (R := Q) (S := T)).mpr inferInstance)
  · intro d
    have hd : e (q (Polynomial.C (MvPolynomial.C d))) = MvPolynomial.C d := by
      rw [heC, MvPolynomial.eval₂Hom_C]
    have hid := Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := P) (A := Q) (B := R)
    have H := RingHom.congr_fun hid (MvPolynomial.C d)
    change l (e.symm (MvPolynomial.C d)) = _
    have hd' : e.symm (MvPolynomial.C d) = q (Polynomial.C (MvPolynomial.C d)) :=
      (congrArg e.symm hd).symm.trans (by rw [e.symm_apply_apply])
    rw [hd']
    exact H
  · intro j
    have hid := Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := P) (A := Q) (B := R)
    have H := (RingHom.congr_fun hid (MvPolynomial.X j)).symm
    dsimp only [RingHom.comp_apply] at H
    change Algebra.TensorProduct.includeRight (algebraMap P R (MvPolynomial.X j)) = _
    refine H.trans ?_
    change l (q (Polynomial.C (MvPolynomial.X j))) = _
    have hj := heC (MvPolynomial.X j)
    rw [MvPolynomial.eval₂Hom_X'] at hj
    by_cases hja : j = a
    · subst j
      rw [ite_eq_left rfl] at hj ⊢
      change l (q (Polynomial.C (MvPolynomial.X a))) =
        l (e.symm (MvPolynomial.X a)) * l (e.symm (MvPolynomial.X b))
      rw [← map_mul, ← map_mul, ← hj, e.symm_apply_apply]
    · rw [ite_eq_right hja] at hj ⊢
      change l (q (Polynomial.C (MvPolynomial.X j))) = l (e.symm (MvPolynomial.X j))
      apply congrArg l
      apply e.injective
      rw [e.apply_symm_apply]
      exact hj

end HodgeLean.Foundations.Program
