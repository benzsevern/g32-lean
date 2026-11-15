import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedRestrictions
import HodgeLean.Foundations.Program.G32Native.PairedResidualNativePairCharts

/-! # Single-pair charts on the actual selected tower -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RegularPairChart
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29

/-- At every selected residue point, both original Rees charts are available
in the full ambient, including intersections with other unprocessed pairs.
Source: Hartshorne, Algebraic Geometry, II.7.13; Schoen, Compositio
Mathematica 65 (1988), Lemma 2.5 and Sublemma 2.7. -/
theorem paired_c3_route_n_pair_charts
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r)
    (x : ComplexPoint (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))))
    (hx : x.underlying ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support) :
    ∃ (U : (P.T.B i.castSucc).left.affineOpens)
      (u v : Γ((P.T.B i.castSucc).left, U)),
      (Point.map (P.C.slices i.castSucc) x).underlying ∈ U.1 ∧
      (P.T.D i.castSucc ⟨2 * i.val, by omega⟩).ideal U = Ideal.span {u} ∧
      (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal U = Ideal.span {v} ∧
      ∃ (V₁ V₂ : (P.T.B i.succ).left.affineOpens)
        (h₁ : V₁.1 ≤ (P.T.b i).left ⁻¹ᵁ U.1)
        (h₂ : V₂.1 ≤ (P.T.b i).left ⁻¹ᵁ U.1)
        (e₁ : ring u v ≃+* Γ((P.T.B i.succ).left, V₁))
        (e₂ : ring v u ≃+* Γ((P.T.B i.succ).left, V₂)),
        V₁.1 ⊔ V₂.1 = (P.T.b i).left ⁻¹ᵁ U.1 ∧
        e₁.toRingHom.comp (coeff u v) = ((P.T.b i).left.appLE U.1 V₁.1 h₁).hom ∧
        e₂.toRingHom.comp (coeff v u) = ((P.T.b i).left.appLE U.1 V₂.1 h₂).hom := by
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i le_rfl
  have hx₁ : (Point.map (P.C.slices i.castSucc) x).underlying ∈
      (P.T.D i.castSucc ⟨2 * i.val, by omega⟩).support := by
    have h : x.underlying ∈ ((P.T.D i.castSucc ⟨2 * i.val, by omega⟩).comap
        (P.C.slices i.castSucc).left).support := by rw [hp.1]; exact hx
    rw [Scheme.IdealSheafData.support_comap] at h
    exact h
  have hx₂ : (Point.map (P.C.slices i.castSucc) x).underlying ∈
      (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).support := by
    have h : x.underlying ∈ ((P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap
        (P.C.slices i.castSucc).left).support := by rw [hp.2]; exact hx
    rw [Scheme.IdealSheafData.support_comap] at h
    exact h
  obtain ⟨U, u, v, hxU, hu, hv, V₁, V₂, h₁, h₂, e₁, e₂, hc, he₁, he₂, _, _⟩ :=
    FibreC.residual_native_tower_pair_charts R.Z R.B₀ R.hdimZ R.h R.r R.γ
      R.hγsurj R.hγinv R.hγ
      (fun t => Point.map R.p₀ (R.eY (R.y (R.σ t)))) (R.hy.comp R.σ.injective)
      P.T.B P.T.e₀ P.T.b P.T.D P.T.hD₀ P.T.htransform P.T.hcartier P.T.hblowup
      i (Point.map (P.C.slices i.castSucc) x) hx₁ hx₂
  exact ⟨U, u, v, hxU, hu, hv, V₁, V₂, h₁, h₂, e₁, e₂, hc, he₁, he₂⟩

end HodgeLean.Foundations.Program.G32Native
