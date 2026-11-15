import HodgeLean.Foundations.Program.SchoenTransferJ12CorrespondenceOffDegree
import HodgeLean.Foundations.Program.SchoenTransferJ12GraphTransferAdjunction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct DirectSum
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection s4_e1_binaryDegreeEquiv

/-- Pullback of an actual correspondence kernel agrees with applying that kernel after graph transfer.
Source: graph adjunction on matching external summands and Künneth off-degree vanishing. -/
theorem s4_selected_correspondence_graph_transfer
    (A B Y : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (D d : ℕ) (hB : TopologicalSpace.dim B.left = D) (hY : TopologicalSpace.dim Y.left = d)
    (IB : HQ B (2 * D) ≃ₗ[ℚ] ℚ) (IY : HQ Y (2 * d) ≃ₗ[ℚ] ℚ)
    (e : ComplexPoint B) (hec : Order.coheight e.underlying = D)
    (he : IB (cycleComponentSheafClass B e.underlying hec) = 1)
    (g : Y ⟶ B) (c p q s : ℕ) (hshift : D + p = d + s) (hkernel : c + s = D + q)
    (K : HQ (A ⊗ B) (2 * c)) (b : HQ Y (2 * p)) :
    s4_selected_corr_action A B D IB c (2 * s) (2 * q) (by omega) K
      (s4_selected_graph_transfer B Y D d IY e hec g (2 * p) (2 * s) (by omega) b) =
    s4_selected_corr_action A Y d IY c (2 * p) (2 * q) (by omega)
      (homPullback (lift (fst A Y) (snd A Y ≫ g)) (2 * c) K) b := by
  classical
  let x := s4_selected_graph_transfer B Y D d IY e hec g (2 * p) (2 * s) (by omega) b
  let m : A ⊗ Y ⟶ A ⊗ B := lift (fst A Y) (snd A Y ≫ g)
  let L := (s4_selected_projection A B D (2 * q) IB).comp
    (((cupProductOf (A ⊗ B)).cup (by omega : 2 * c + 2 * s = 2 * D + 2 * q)).flip
      (homPullback (snd A B) (2 * s) x))
  let R := (s4_selected_projection A Y d (2 * q) IY).comp
    ((((cupProductOf (A ⊗ Y)).cup (by omega : 2 * c + 2 * p = 2 * d + 2 * q)).flip
      (homPullback (snd A Y) (2 * p) b)).comp (homPullback m (2 * c)))
  let E := s4_e1_binaryDegreeEquiv A B (2 * c)
  have hLR : L.comp E.toLinearMap = R.comp E.toLinearMap := by
    apply DirectSum.linearMap_ext ℚ
    intro k
    apply TensorProduct.ext'
    intro u v
    change s4_selected_corr_action A B D IB c (2 * s) (2 * q) (by omega)
      (s4_e1_binaryDegreeEquiv A B (2 * c) (DirectSum.lof ℚ _ _ k (u ⊗ₜ[ℚ] v))) x =
      s4_selected_corr_action A Y d IY c (2 * p) (2 * q) (by omega)
        (homPullback m (2 * c)
          (s4_e1_binaryDegreeEquiv A B (2 * c) (DirectSum.lof ℚ _ _ k (u ⊗ₜ[ℚ] v)))) b
    rw [s4_e1_binaryDegreeEquiv_tmul, spec_homPullback_cup]
    rcases k with ⟨⟨r, t⟩, hrt⟩
    have hmA : homPullback m r (homPullback (fst A B) r u) = homPullback (fst A Y) r u := by
      rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_fst]
    have hmB : homPullback m t (homPullback (snd A B) t v) =
        homPullback (snd A Y) t (homPullback g t v) := by
      rw [← LinearMap.comp_apply, ← spec_homPullback_comp, lift_snd,
        spec_homPullback_comp, LinearMap.comp_apply]
    rw [hmA, hmB]
    by_cases hr : r = 2 * q
    · subst r
      have hs : s ≤ D := by omega
      have ht : t = 2 * (D - s) := by omega
      subst t
      rw [s4_selected_corr_action_cross A B D IB c (2 * s) (2 * q) (2 * (D - s)) (by omega) (by omega),
        s4_selected_corr_action_cross A Y d IY c (2 * p) (2 * q) (2 * (D - s)) (by omega) (by omega)]
      exact congrArg (fun z : ℚ => z • u)
        (s4_selected_graph_transfer_adjunction B Y D d p (D - s) s hB hY hshift
          (Nat.sub_add_cancel hs) IB IY e hec he g v b)
    · rw [s4_selected_corr_action_cross_off_degree A B D IB c (2 * s) (2 * q) r t (by omega) hrt hr,
        s4_selected_corr_action_cross_off_degree A Y d IY c (2 * p) (2 * q) r t (by omega) hrt hr]
  obtain ⟨z, rfl⟩ := E.surjective K
  exact LinearMap.congr_fun hLR z

#print axioms s4_selected_correspondence_graph_transfer
end HodgeLean.Foundations.Program
