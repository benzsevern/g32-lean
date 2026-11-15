import HodgeLean.Foundations.Program.SchoenTowerL1bEtaleBinomialChart

/-! Binomial blowup coordinates for a specified etale section tuple.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
universe u
namespace HodgeLean.Foundations.Program

/-- Blowing up two members of a specified etale coordinate tuple gives new etale
coordinates on the binomial chart, retaining the ground map and every other section. -/
theorem s2v_l1b_etale_section_binomial_chart
    {k R σ : Type u} [CommRing k] [CommRing R] [DecidableEq σ]
    (c : k →+* R) (z : σ → R) (het : (MvPolynomial.eval₂Hom c z).Etale)
    (a b : σ) (hab : a ≠ b) :
    let q := Ideal.Quotient.mk (Ideal.span
      {Polynomial.C (z a) - Polynomial.X * Polynomial.C (z b)})
    ∃ w : σ → s2v_L1bChart (z a) (z b),
      (MvPolynomial.eval₂Hom ((q.comp Polynomial.C).comp c) w).Etale ∧
      (∀ j, q (Polynomial.C (z j)) = if j = a then w a * w b else w j) := by
  let : Algebra (MvPolynomial σ k) R := (MvPolynomial.eval₂Hom c z).toAlgebra
  let : Algebra.Etale (MvPolynomial σ k) R := het
  have H := s2v_l1b_etale_binomial_chart (k := k) (R := R) a b hab
  dsimp only at H
  simp only [RingHom.algebraMap_toAlgebra] at H
  simp only [MvPolynomial.eval₂Hom_comp_C] at H
  obtain ⟨w, hw, hwe⟩ := H
  let J : Ideal (Polynomial R) := Ideal.span
    {Polynomial.C ((MvPolynomial.eval₂Hom c z) (MvPolynomial.X a)) -
      Polynomial.X * Polynomial.C ((MvPolynomial.eval₂Hom c z) (MvPolynomial.X b))}
  let K : Ideal (Polynomial R) := Ideal.span
    {Polynomial.C (z a) - Polynomial.X * Polynomial.C (z b)}
  have hJK : J = K := by
    dsimp only [J, K]
    rw [MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
  let e := (Ideal.quotientEquivAlgOfEq R hJK).toRingEquiv
  have he (p : Polynomial R) : e (Ideal.Quotient.mk J p) = Ideal.Quotient.mk K p :=
    Ideal.quotientEquivAlgOfEq_mk R hJK p
  let q := Ideal.Quotient.mk K
  let c' := (q.comp Polynomial.C).comp c
  have hmap : MvPolynomial.eval₂Hom c' (fun j => e (w j)) =
      e.toRingHom.comp (MvPolynomial.eval₂Hom
        (((Ideal.Quotient.mk J).comp Polynomial.C).comp c) w) := by
    apply MvPolynomial.ringHom_ext
    · intro d
      rw [MvPolynomial.eval₂Hom_C]
      change c' d = e ((MvPolynomial.eval₂Hom
        (((Ideal.Quotient.mk J).comp Polynomial.C).comp c) w) (MvPolynomial.C d))
      rw [MvPolynomial.eval₂Hom_C]
      exact (he (Polynomial.C (c d))).symm
    · intro j
      rw [MvPolynomial.eval₂Hom_X']
      change e (w j) = e ((MvPolynomial.eval₂Hom
        (((Ideal.Quotient.mk J).comp Polynomial.C).comp c) w) (MvPolynomial.X j))
      rw [MvPolynomial.eval₂Hom_X']
  refine ⟨fun j => e (w j), ?_, ?_⟩
  · change (MvPolynomial.eval₂Hom c' (fun j => e (w j))).Etale
    rw [hmap]
    exact RingHom.Etale.stableUnderComposition _ _ hw
      (RingHom.Etale.of_bijective e.bijective)
  · intro j
    have Hj := congrArg e (hwe j)
    change e (Ideal.Quotient.mk J
      (Polynomial.C ((MvPolynomial.eval₂Hom c z) (MvPolynomial.X j)))) = _ at Hj
    rw [he, MvPolynomial.eval₂Hom_X'] at Hj
    by_cases hja : j = a
    · rw [ite_eq_left hja, map_mul] at Hj
      rw [ite_eq_left hja]
      exact Hj
    · rw [ite_eq_right hja] at Hj ⊢
      exact Hj

end HodgeLean.Foundations.Program
