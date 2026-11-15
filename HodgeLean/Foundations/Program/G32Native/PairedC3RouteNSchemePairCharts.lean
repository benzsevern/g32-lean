import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNPairCharts
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNPointCover
import HodgeLean.Adapters.IntersectionProductScaf

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

/-- The single-pair chart cover contains every scheme point of the residue
hyperplane, rather than only its complex points.
Source: Hartshorne, Algebraic Geometry, II.3.14 and II.7.13. -/
theorem paired_c3_route_n_scheme_pair_charts
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r)
    (x : ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ))
    (hx : x ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support) :
    ∃ (U : (P.T.B i.castSucc).left.affineOpens)
      (u v : Γ((P.T.B i.castSucc).left, U)),
      (P.C.slices i.castSucc).left x ∈ U.1 ∧
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
  classical
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))
  letI : Smooth PP.hom := HodgeLean.Adapters.IntersectionProductScaf_projective_smooth R.P.k
  let H := s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)
  let T := {q : ComplexPoint PP // q.underlying ∈ H.support}
  have hcharts := fun q : T => paired_c3_route_n_pair_charts R P i q.val q.property
  choose U u v hU hu hv V₁ V₂ h₁ h₂ e₁ e₂ hc he₁ he₂ using hcharts
  obtain ⟨q, hq⟩ := paired_c3_closed_locus_open_cover PP H.support
    (fun q : T => (P.C.slices i.castSucc).left ⁻¹ᵁ (U q).1)
    (by
      intro p hp
      exact ⟨⟨p, hp⟩, hU ⟨p, hp⟩⟩) x hx
  exact ⟨U q, u q, v q, hq, hu q, hv q, V₁ q, V₂ q, h₁ q, h₂ q,
    e₁ q, e₂ q, hc q, he₁ q, he₂ q⟩

end HodgeLean.Foundations.Program.G32Native
