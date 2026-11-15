import HodgeLean.Foundations.Program.PrymVariationCentreCharacters

noncomputable section
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program

theorem b63d_conjugateRep_age (g : b4b_Group) :
    b4_age (HurwitzPrymRex_barRep b63d_naturalRep g) =
      g32h_age (b4b_toMatrix g)⁻¹ := by
  have hinv : (b4b_toMatrix g)⁻¹ = b4b_toMatrix g⁻¹ :=
    Matrix.inv_eq_left_inv (by rw [← map_mul, inv_mul_cancel, map_one])
  have hchar : ((b4b_toMatrix g)⁻¹).charpoly =
      (b4b_toMatrix g).charpoly.map (starRingEnd ℂ) := by
    rw [hinv, b63l_toMatrix_inv_eq_star, Matrix.star_eq_conjTranspose]
    change ((b4b_toMatrix g).transpose.map (starRingEnd ℂ)).charpoly = _
    rw [Matrix.charpoly_map, Matrix.charpoly_transpose]
  have hroots := (Matrix.charpoly_monic (b4b_toMatrix g)).roots_map_of_card_eq_natDegree
    (starRingEnd ℂ) IsAlgClosed.card_roots_eq_natDegree
  simp only [b4_age, HurwitzPrymRex_roots_bar]
  change (Multiset.map g32h_angle
    ((Matrix.toLin' (b4b_toMatrix g)).charpoly.roots.map (starRingEnd ℂ))).sum = _
  rw [Matrix.charpoly_toLin', hroots]
  exact congrArg (fun p : Polynomial ℂ ↦ (p.roots.map g32h_angle).sum) hchar.symm

theorem b63d_root_rank_sum :
    (∑ i : Fin 13, ((b4b_toMatrix (b4b_root i) - 1).rank : ℝ)) = 14 := by
  have h : (∑ i : Fin 13, ((b4b_toMatrix (b4b_root i) - 1).rank : ℤ)) = 14 := by
    have h := b63d_root_multCW
    unfold g32h_multCW at h
    change -2 * 4 + (∑ i : Fin 13, ((b4b_toMatrix (b4b_root i) - 1).rank : ℤ)) = 6 at h
    linarith
  exact_mod_cast h

theorem b63d_root_conjugate_age_sum :
    (∑ i : Fin 13, b4_age (HurwitzPrymRex_barRep b63d_naturalRep (b4b_root i))) = 7 := by
  simp only [b63d_conjugateRep_age]
  have h := b63d_root_holoCW
  unfold g32h_holoCW at h
  linarith

theorem b63d_root_natural_age_sum :
    (∑ i : Fin 13, b4_age (b63d_naturalRep (b4b_root i))) = 7 := by
  have hsum :
      (∑ i : Fin 13, b4_age (HurwitzPrymRex_barRep b63d_naturalRep (b4b_root i))) +
      (∑ i : Fin 13, b4_age (b63d_naturalRep (b4b_root i))) = 14 := by
    rw [← Finset.sum_add_distrib, ← b63d_root_rank_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [HurwitzPrymRex_age_add_bar, b63d_naturalRep_rank]
  rw [b63d_root_conjugate_age_sum] at hsum
  linarith

end HodgeLean.Foundations.Program
