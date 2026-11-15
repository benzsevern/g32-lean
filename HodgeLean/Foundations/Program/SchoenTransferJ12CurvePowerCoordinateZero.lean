import HodgeLean.Foundations.Program.SchoenTransferJ12CurvePowerOffDegree

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
open scoped DirectSum TensorProduct BigOperators
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- A zero coordinate operator annihilates the recursively ordered tensor operator. -/
theorem s4_selected_tensorPullback_zero_coordinate
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (n : ℕ) (d : Fin n → ℕ) (b : Fin n → (Y ⟶ Y))
    (hb : ∃ i, homPullback (b i) (d i) = 0) :
    s4_e1_tensorPullback Y n d b = 0 := by
  induction n with
  | zero => obtain ⟨i, _⟩ := hb; exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨i, hi⟩ := hb
    change TensorProduct.map (homPullback (b 0) (d 0))
      (s4_e1_tensorPullback Y n (Fin.tail d) (Fin.tail b)) = 0
    refine Fin.cases ?_ (fun j hj => ?_) i hi
    · intro h
      rw [h, TensorProduct.map_zero_left]
    · rw [ih (Fin.tail d) (Fin.tail b) ⟨j, hj⟩, TensorProduct.map_zero_right]

/-- A coordinate endomorphism killing one H1 factor has zero extracted all-degree-one component. -/
theorem s4_selected_curve_power_extract_coordinate_zero
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (n : ℕ)
    [IsIntegral (g3_power Y n).left] [Smooth (g3_power Y n).hom]
    [IsProjective (g3_power Y n).hom]
    (u : g3_power Y n ⟶ g3_power Y n) (b : Fin n → (Y ⟶ Y))
    (hu : ∀ i, u ≫ g3_proj Y n i = g3_proj Y n i ≫ b i)
    (hb : ∃ i, homPullback (b i) 1 = 0) :
    (s4_selected_curve_power_extract Y hdim n).comp (homPullback u n) = 0 := by
  classical
  let E := s4_selected_curve_power_extract Y hdim n
  have hzero : s4_e1_tensorPullback Y n (fun _ => 1) b = 0 :=
    s4_selected_tensorPullback_zero_coordinate Y n (fun _ => 1) b hb
  have hK : (E.comp (homPullback u n)).comp (s4_e1_kunneth Y n n) = 0 := by
    apply DirectSum.linearMap_ext ℚ
    intro d
    apply LinearMap.ext
    intro v
    have hgen (m : ℕ) (d : {d : Fin n → ℕ // ∑ i, d i = m})
        (v : s4_e1_tensor Y n d.val) :
        homPullback u m (s4_e1_kunneth Y n m (DirectSum.lof ℚ _ _ d v)) =
        s4_e1_kunneth Y n m
          (DirectSum.lof ℚ _ _ d (s4_e1_tensorPullback Y n d.val b v)) := by
      rcases d with ⟨d, hd⟩
      subst m
      have hs := s4_e1_orderedCup_coordinate_tensor Y (g3_power Y n) u n d
        (g3_proj Y n) b hu
      simpa only [s4_e1_kunneth, DirectSum.toModule_lof, LinearMap.comp_apply,
        eq_mp_eq_cast, cast_eq]
        using LinearMap.congr_fun hs v
    have he := hgen n d v
    change E (homPullback u n (s4_e1_kunneth Y n n (DirectSum.lof ℚ _ _ d v))) = 0
    rw [he]
    by_cases hd : d = ⟨fun _ => 1, s4_e1_sum_one n⟩
    · subst d
      rw [hzero, LinearMap.zero_apply, map_zero, map_zero, map_zero]
    · exact s4_selected_curve_power_extract_off_degree Y hdim n d hd _
  ext x
  obtain ⟨v, rfl⟩ := (s4_e1_power_kunneth Y hdim n n).surjective x
  exact LinearMap.congr_fun hK v

#print axioms s4_selected_tensorPullback_zero_coordinate
#print axioms s4_selected_curve_power_extract_coordinate_zero
end HodgeLean.Foundations.Program
