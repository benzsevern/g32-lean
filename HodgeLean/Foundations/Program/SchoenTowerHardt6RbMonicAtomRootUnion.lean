import HodgeLean.Foundations.Program.SchoenTowerHardt6RbBooleanFamilyCoordinates
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbMonicNormalization

/-! One monic polynomial has exactly the union of all nonzero atom root fibers. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_monic_atom_root_union {n m : ℕ}
    (B : Fin m → s2v_t11b_Formula (n + 1))
    (hB : ∀ j p, p ∈ (B j).atoms → p ≠ 0 →
      IsUnit (MvPolynomial.finSuccEquiv ℝ n p).leadingCoeff) :
    ∃ Q : Polynomial (MvPolynomial (Fin n) ℝ), Q.Monic ∧
      ∀ (x : Fin n → ℝ) (t : ℝ), Q.eval₂ (MvPolynomial.eval x) t = 0 ↔
        ∃ j p, p ∈ (B j).atoms ∧ p ≠ 0 ∧ MvPolynomial.eval (Fin.cons t x) p = 0 := by
  classical
  let S := (Finset.univ.biUnion (fun j => (B j).atoms)).filter (fun p => p ≠ 0)
  have hS (p : S) : IsUnit (MvPolynomial.finSuccEquiv ℝ n p.val).leadingCoeff := by
    obtain ⟨hp, hp0⟩ := Finset.mem_filter.mp p.property
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
    exact hB j p.val hj hp0
  choose Q hQ hroots using fun p : S => s2v_hardt6rb_monic_normalization _ (hS p)
  refine ⟨∏ p : S, Q p, Polynomial.monic_prod_of_monic _ _ (fun p _ => hQ p), ?_⟩
  intro x t
  change (Polynomial.eval₂RingHom (MvPolynomial.eval x) t) (∏ p : S, Q p) = 0 ↔ _
  rw [map_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨p, _, hp⟩
    obtain ⟨hmem, hp0⟩ := Finset.mem_filter.mp p.property
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hmem
    refine ⟨j, p.val, hj, hp0, ?_⟩
    rw [MvPolynomial.eval_eq_eval_mv_eval', Polynomial.eval_map]
    exact (hroots p _ _).mpr hp
  · rintro ⟨j, p, hp, hp0, hzero⟩
    have hpS : p ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hp⟩, hp0⟩
    refine ⟨⟨p, hpS⟩, Finset.mem_univ _, ?_⟩
    apply (hroots ⟨p, hpS⟩ _ _).mp
    rwa [MvPolynomial.eval_eq_eval_mv_eval', Polynomial.eval_map] at hzero

end HodgeLean.Foundations.Program
