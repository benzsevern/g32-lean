import HodgeLean.Foundations.Program.SchoenCycleChartIdeals

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program

/-- The actual projective residue ideals pull back to the normalized linear equations.
Source: Schoen (1988), Lemma 2.3(vi), printed pp. 13–14; Lemma 2.4 proof, printed p. 15. -/
theorem s2e_chain_residue_projective_chart_aux
    (k : ℕ) (T : Finset (Fin (k + 1))) (i : Fin (k + 1)) :
    Ideal.map (Scheme.ΓSpecIso
        ↧(MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ)).hom.hom
      (((s2e_s2b_intersectionIdeal k T).comap (s2e_s2b_chart i)).ideal ⟨⊤, isAffineOpen_top _⟩) =
    Ideal.span ((fun j : Fin (k + 1) =>
      if h : j = i then (1 : MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ)
      else MvPolynomial.X ⟨j, h⟩) '' (↑T : Set (Fin (k + 1)))) :=
  by
    classical
    induction T using Finset.induction_on with
    | empty =>
      have hI : s2e_s2b_intersectionIdeal k ∅ = ⊥ := by
        simp [s2e_s2b_intersectionIdeal]
      rw [hI, Scheme.IdealSheafData.comap_bot, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
        Ideal.map_bot]
      simp only [Finset.coe_empty, Set.image_empty, Ideal.span_empty]
    | @insert a T ha ih =>
      have hI : s2e_s2b_intersectionIdeal k (insert a T) =
          s2e_s2b_residueIdeal k a ⊔ s2e_s2b_intersectionIdeal k T := by
        simp [s2e_s2b_intersectionIdeal, Finset.mem_insert, iSup_or, iSup_sup_eq]
      rw [hI, Scheme.IdealSheafData.comap_sup, Scheme.IdealSheafData.ideal_sup,
        Pi.sup_apply, Ideal.map_sup, s2e_residueIdeal_chart, ih]
      simp only [Finset.coe_insert, Set.image_insert_eq, Ideal.span_insert,
        s2e_chartHom_coordinate]

end HodgeLean.Foundations.Program
