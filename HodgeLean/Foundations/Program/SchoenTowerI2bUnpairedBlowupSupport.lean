import HodgeLean.Foundations.Program.SchoenTowerI2bBlowupChartCover
import HodgeLean.Foundations.Program.SchoenTowerI2bBlowupChartLift
import HodgeLean.Foundations.Program.SchoenTowerI2bChartSupport
import HodgeLean.Foundations.Program.SchoenTowerI2bStrictChartSupport

/-! Actual support inclusion for an independent unpaired branch.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Polynomial
namespace HodgeLean.Foundations.Program

/-- Every actual upper point above an independent unpaired branch belongs to its reduced strict transform.
Source: the retained two-chart cover and density of the unpaired divisor away from the centre. -/
theorem s2v_i2b_unpaired_blowup_support_inclusion
    (X Y U : Over (Spec ↧ℂ)) [IsAffine U.left]
    (a : U ⟶ X) [IsOpenImmersion a.left] (b : Y ⟶ X)
    (D I : X.left.IdealSheafData)
    (hcartier : ∀ y : Y.left, ∃ V : Y.left.affineOpens, y ∈ V.1 ∧
      Nonempty (((I.comap b.left).ideal V) ≃ₗ[Γ(Y.left, V)] Γ(Y.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (f : T ⟶ X),
      (∀ x : T.left, ∃ W : T.left.affineOpens, x ∈ W.1 ∧
        Nonempty (((I.comap f.left).ideal W) ≃ₗ[Γ(T.left, W)] Γ(T.left, W))) →
      ∃! g : T ⟶ Y, g ≫ b = f)
    (u v z : Γ(U.left, ⊤))
    (hI : (I.comap a.left).ideal ⟨⊤, isAffineOpen_top U.left⟩ = Ideal.span {u, v})
    (hD : (D.comap a.left).ideal ⟨⊤, isAffineOpen_top U.left⟩ = Ideal.span {z})
    (hpair : RingTheory.Sequence.IsWeaklyRegular Γ(U.left, ⊤) [v, u])
    (hpair' : RingTheory.Sequence.IsWeaklyRegular Γ(U.left, ⊤) [u, v])
    (htriple : RingTheory.Sequence.IsWeaklyRegular Γ(U.left, ⊤) [z, v, u])
    (htriple' : RingTheory.Sequence.IsWeaklyRegular Γ(U.left, ⊤) [z, u, v]) :
    ∀ y : Y.left, b.left y ∈ Set.range a.left → b.left y ∈ D.support →
      y ∈ (s2c_strictTransform b.left D I).support := by
  have hI' : (I.comap a.left).ideal ⟨⊤, isAffineOpen_top U.left⟩ = Ideal.span {v, u} :=
    hI.trans (congrArg Ideal.span (Set.pair_comm u v))
  obtain ⟨g, hg⟩ := s2v_i2b_retained_blowup_chart_lift X Y U a b I hblowup u v hI hpair
  obtain ⟨g', hg'⟩ := s2v_i2b_retained_blowup_chart_lift X Y U a b I hblowup v u hI' hpair'
  have hd := s2v_i2b_actual_blowup_chart_support_density U.left
    (D.comap a.left) (I.comap a.left) u v z hD hI htriple
  have hd' := s2v_i2b_actual_blowup_chart_support_density U.left
    (D.comap a.left) (I.comap a.left) v u z hD hI' htriple'
  have hdg : closure ((g ≫ b.left) ⁻¹' ((D.support : Set X.left) \ (I.support : Set X.left))) =
      (g ≫ b.left) ⁻¹' (D.support : Set X.left) := by
    rw [hg]
    simpa only [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.preimage,
      TopologicalSpace.Closeds.coe_mk, Set.preimage, Set.mem_sdiff, Set.mem_ofPred_eq,
      Scheme.Hom.comp_apply] using hd
  have hdg' : closure ((g' ≫ b.left) ⁻¹' ((D.support : Set X.left) \ (I.support : Set X.left))) =
      (g' ≫ b.left) ⁻¹' (D.support : Set X.left) := by
    rw [hg']
    simpa only [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.preimage,
      TopologicalSpace.Closeds.coe_mk, Set.preimage, Set.mem_sdiff, Set.mem_ofPred_eq,
      Scheme.Hom.comp_apply] using hd'
  intro y hy hDy
  rcases s2v_i2b_retained_blowup_chart_point_cover X Y U a b I hcartier hblowup u v hI
      g hg g' hg' y hy with h | h
  · obtain ⟨q, rfl⟩ := h
    exact s2v_i2b_dense_chart_strictTransform_support b.left g D I hdg q hDy
  · obtain ⟨q, rfl⟩ := h
    exact s2v_i2b_dense_chart_strictTransform_support b.left g' D I hdg' q hDy

end HodgeLean.Foundations.Program
