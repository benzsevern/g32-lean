import HodgeLean.Foundations.Program.SchoenTowerL1bChartAlgebra
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Monomial

/-! Polynomial coordinates on a binomial blowup chart.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Replacing one centre coordinate by the chart ratio gives a polynomial chart,
with explicit coefficient substitution and every other coordinate retained. -/
theorem s2v_l1b_coordinate_chart_equiv {R σ : Type*} [CommRing R]
    [DecidableEq σ] (a b : σ) (hab : a ≠ b) :
    ∃ e : s2v_L1bChart (MvPolynomial.X a : MvPolynomial σ R) (MvPolynomial.X b) ≃+*
        MvPolynomial σ R,
      (∀ p, e (Ideal.Quotient.mk _ (Polynomial.C p)) =
        MvPolynomial.eval₂Hom MvPolynomial.C
          (fun i => if i = a then MvPolynomial.X a * MvPolynomial.X b else MvPolynomial.X i) p) ∧
      e (Ideal.Quotient.mk _ Polynomial.X) = MvPolynomial.X a := by
  let P := MvPolynomial σ R
  let J : Ideal (Polynomial P) := Ideal.span
    {Polynomial.C (MvPolynomial.X a) - Polynomial.X * Polynomial.C (MvPolynomial.X b)}
  let q := Ideal.Quotient.mk J
  let f : P →+* P := MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i => if i = a then MvPolynomial.X a * MvPolynomial.X b else MvPolynomial.X i)
  have hfa : f (MvPolynomial.X a) = MvPolynomial.X a * MvPolynomial.X b := by
    dsimp only [f]
    rw [MvPolynomial.eval₂Hom_X', if_pos rfl]
  have hfb : f (MvPolynomial.X b) = MvPolynomial.X b := by
    dsimp only [f]
    rw [MvPolynomial.eval₂Hom_X', if_neg hab.symm]
  obtain ⟨F, hF, _⟩ := s2v_l1b_chart_lift (MvPolynomial.X a : P) (MvPolynomial.X b)
    f (MvPolynomial.X a) (by rw [hfa, hfb])
  have hFC (p : P) : F (q (Polynomial.C p)) = f p :=
    (RingHom.congr_fun hF (Polynomial.C p)).trans (Polynomial.eval₂_C _ _)
  have hFX : F (q Polynomial.X) = MvPolynomial.X a :=
    (RingHom.congr_fun hF Polynomial.X).trans (Polynomial.eval₂_X _ _)
  let G : P →+* s2v_L1bChart (MvPolynomial.X a : P) (MvPolynomial.X b) :=
    MvPolynomial.eval₂Hom ((q.comp Polynomial.C).comp MvPolynomial.C)
      (fun i => if i = a then q Polynomial.X else q (Polynomial.C (MvPolynomial.X i)))
  have hGa : G (MvPolynomial.X a) = q Polynomial.X := by
    dsimp only [G]
    rw [MvPolynomial.eval₂Hom_X', if_pos rfl]
  have hGb : G (MvPolynomial.X b) = q (Polynomial.C (MvPolynomial.X b)) := by
    dsimp only [G]
    rw [MvPolynomial.eval₂Hom_X', if_neg hab.symm]
  have hGF : G.comp F = RingHom.id _ := by
    apply Ideal.Quotient.ringHom_ext
    apply Polynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro c
        change G (F (q (Polynomial.C (MvPolynomial.C c)))) = q (Polynomial.C (MvPolynomial.C c))
        rw [hFC]
        dsimp only [f, G]
        rw [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
        rfl
      · intro i
        change G (F (q (Polynomial.C (MvPolynomial.X i)))) = q (Polynomial.C (MvPolynomial.X i))
        rw [hFC]
        by_cases hi : i = a
        · subst i
          rw [hfa, map_mul, hGa, hGb]
          exact (s2v_l1b_chart_relation (MvPolynomial.X a : P) (MvPolynomial.X b)).symm
        · dsimp only [f]
          rw [MvPolynomial.eval₂Hom_X', if_neg hi]
          dsimp only [G]
          rw [MvPolynomial.eval₂Hom_X', if_neg hi]
    · change G (F (q Polynomial.X)) = q Polynomial.X
      rw [hFX, hGa]
  have hFG : F.comp G = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change F (G (MvPolynomial.C c)) = MvPolynomial.C c
      dsimp only [G]
      rw [MvPolynomial.eval₂Hom_C]
      change F (q (Polynomial.C (MvPolynomial.C c))) = MvPolynomial.C c
      rw [hFC]
      exact MvPolynomial.eval₂Hom_C _ _ _
    · intro i
      change F (G (MvPolynomial.X i)) = MvPolynomial.X i
      by_cases hi : i = a
      · subst i
        rw [hGa, hFX]
      · dsimp only [G]
        rw [MvPolynomial.eval₂Hom_X']
        rw [if_neg hi, hFC]
        dsimp only [f]
        rw [MvPolynomial.eval₂Hom_X', if_neg hi]
  let e : s2v_L1bChart (MvPolynomial.X a : P) (MvPolynomial.X b) ≃+* P :=
    { F with
      invFun := G
      left_inv := fun x => RingHom.congr_fun hGF x
      right_inv := fun x => RingHom.congr_fun hFG x }
  exact ⟨e, hFC, hFX⟩

end HodgeLean.Foundations.Program
