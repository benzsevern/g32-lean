import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPositiveIntrinsic
import Mathlib.LinearAlgebra.AffineSpace.Centroid

/-! Every nonempty finite hull contains its actual centroid in its intrinsic interior. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_intrinsic {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (hs : s.Nonempty) :
    s.centroid ℝ id ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  classical
  letI : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  let w : stdSimplex ℝ s :=
    ⟨(Finset.univ : Finset s).centroidWeights ℝ,
      (fun _ => by simp only [Finset.centroidWeights_apply, inv_nonneg, Nat.cast_nonneg]),
      (Finset.univ : Finset s).sum_centroidWeights_eq_one_of_nonempty ℝ Finset.univ_nonempty⟩
  have hw : ∀ i, 0 < w.val i := by
    intro i
    change 0 < (Finset.card (Finset.univ : Finset s) : ℝ)⁻¹
    apply inv_pos.mpr
    exact_mod_cast Finset.card_pos.mpr (Finset.univ_nonempty : (Finset.univ : Finset s).Nonempty)
  have he : (∑ i : s, w.val i • i.val) = s.centroid ℝ id := by
    calc
      (∑ i : s, w.val i • i.val) =
          (Finset.univ : Finset s).affineCombination ℝ ((↑) : s → E) w.val :=
        (Finset.affineCombination_eq_linear_combination _ _ _ w.property.2).symm
      _ = (Finset.univ : Finset s).centroid ℝ ((↑) : s → E) := rfl
      _ = s.centroid ℝ id := Finset.centroid_univ ℝ s
  have hrange : Set.range ((↑) : s → E) = (s : Set E) := by
    ext x
    simp
  rw [← hrange, ← he]
  exact s2v_hardt6rb_positive_weights_mem_intrinsicInterior ((↑) : s → E) w hw

end HodgeLean.Foundations.Program
