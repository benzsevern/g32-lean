import HodgeLean.Foundations.Program.SchoenCycleProjectiveCharts

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry.ComplexProjectiveSpace MvPolynomial
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Selected normalized chart coordinates, indexed without the denominator.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
def s2e_chartSelection {k : ℕ} (i : Fin (k + 1)) (T : Finset (Fin (k + 1))) : Finset (Fin k) :=
  Finset.univ.filter (fun j => i.succAbove j ∈ T)

/-- The normalized linear ideal is the coordinate ideal under the explicit chart reindexing.
Source: Schoen (1988), Lemma 2.4 proof, printed p. 15. -/
theorem s2e_chartSelectedIdeal {k : ℕ} (i : Fin (k + 1)) (T : Finset (Fin (k + 1)))
    (hi : i ∉ T) :
    Ideal.span ((fun j : Fin (k + 1) =>
      if h : j = i then (1 : MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ)
      else X ⟨j, h⟩) '' (↑T : Set (Fin (k + 1)))) =
    Ideal.map (MvPolynomial.renameEquiv ℂ (finSuccAboveEquiv i)).toRingHom
      (Ideal.span ((X (R := ℂ)) '' (↑(s2e_chartSelection i T) : Set (Fin k)))) := by
  classical
  rw [Ideal.map_span, ← Set.image_comp]
  congr 1
  ext p
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    let t := (finSuccAboveEquiv i).symm ⟨j, hji⟩
    refine ⟨t, ?_, ?_⟩
    · simp only [s2e_chartSelection, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      have ht : i.succAbove t = j := congrArg Subtype.val ((finSuccAboveEquiv i).apply_symm_apply ⟨j, hji⟩)
      rwa [ht]
    · change MvPolynomial.rename (finSuccAboveEquiv i) (X t) = _
      rw [MvPolynomial.rename_X]
      dsimp only
      rw [dite_eq_right hji]
      exact congrArg X ((finSuccAboveEquiv i).apply_symm_apply ⟨j, hji⟩)
  · rintro ⟨j, hj, rfl⟩
    have hjT : i.succAbove j ∈ T := (Finset.mem_filter.mp hj).2
    refine ⟨i.succAbove j, hjT, ?_⟩
    change (if h : i.succAbove j = i then 1 else X ⟨i.succAbove j, h⟩) =
      MvPolynomial.rename (finSuccAboveEquiv i) (X j)
    rw [dite_eq_right (Fin.succAbove_ne i j), MvPolynomial.rename_X]
    rfl

/-- The quotient of the normalized chart by its selected equations retains the other variables.
Source: Schoen (1988), Lemma 2.3(vi), printed pp. 13–14; Lemma 2.4 proof, printed p. 15. -/
theorem s2e_chartQuotient {k : ℕ} (i : Fin (k + 1)) (T : Finset (Fin (k + 1)))
    (hi : i ∉ T) :
    Nonempty ((MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ ⧸
      Ideal.span ((fun j : Fin (k + 1) =>
        if h : j = i then (1 : MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ)
        else X ⟨j, h⟩) '' (↑T : Set (Fin (k + 1))))) ≃ₐ[ℂ]
      MvPolynomial {j : Fin k // j ∉ s2e_chartSelection i T} ℂ) := by
  obtain ⟨Q, _⟩ := s2e_chain_residue_coordinate_quotient k (s2e_chartSelection i T)
  exact ⟨(Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv ℂ (finSuccAboveEquiv i))
    (s2e_chartSelectedIdeal i T hi)).symm.trans Q⟩

end HodgeLean.Foundations.Program
