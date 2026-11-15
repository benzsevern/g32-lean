import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNSchemePairCharts
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNUnitNeighborhood
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidueSupport
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

/-- At every scheme point of the retained residue hyperplane the two
actual branch equations have an ambient unit ratio modulo the slice ideal.
Source: Hartshorne, Algebraic Geometry, II.3 and II.7.13.
-/
theorem paired_c3_route_n_adapted_unit_equation
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r)
    (x : ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ))
    (hx : x ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support) :
    ∃ (U : (P.T.B i.castSucc).left.affineOpens)
      (u v : Γ((P.T.B i.castSucc).left, U))
      (a : Γ((P.T.B i.castSucc).left, U)ˣ),
      (P.C.slices i.castSucc).left x ∈ U.1 ∧
      (P.T.D i.castSucc ⟨2 * i.val, by omega⟩).ideal U = Ideal.span {u} ∧
      (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal U = Ideal.span {v} ∧
      u - (a : Γ((P.T.B i.castSucc).left, U)) * v ∈
        (P.C.slices i.castSucc).left.ker.ideal U := by
  obtain ⟨U, u, v, hxU, hu, hv, _⟩ := paired_c3_route_n_scheme_pair_charts R P i x hx
  let i₀ := (P.C.slices i.castSucc).left
  let D := P.T.D i.castSucc ⟨2 * i.val, by omega⟩
  let E := P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  letI : IsIntegral (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))).left :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral R.P.k
  letI : IsClosedImmersion i₀ := P.C.sliceImmersion i.castSucc
  letI : Nonempty (i₀ ⁻¹ᵁ U.1) := ⟨⟨x, hxU⟩⟩
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i le_rfl
  have heq : D.comap i₀ = E.comap i₀ := hp.1.trans hp.2.symm
  have hproper : (E.comap i₀).support ≠ ⊤ := by
    rw [hp.2]
    exact paired_c3_residue_support_proper _ _
  obtain ⟨a, ha, hunit⟩ := paired_c3_affine_normalized_equation i₀ D E heq hproper U u v hu hv
  obtain ⟨V, hVU, hunitV, hpre⟩ := paired_c3_normalizing_unit_neighborhood i₀ U a hunit
  let r := ((P.T.B i.castSucc).left.presheaf.map
    (homOfLE (X := (P.T.B i.castSucc).left.Opens) hVU).op).hom
  obtain ⟨a', ha'⟩ := hunitV
  refine ⟨V, r u, r v, a', ?_, ?_, ?_, ?_⟩
  · change x ∈ i₀ ⁻¹ᵁ V.1
    rw [hpre]
    exact hxU
  · rw [← D.map_ideal hVU, hu, Ideal.map_span, Set.image_singleton]
    rfl
  · rw [← E.map_ideal hVU, hv, Ideal.map_span, Set.image_singleton]
    rfl
  · rw [ha']
    change r u - r a * r v ∈ i₀.ker.ideal V
    rw [← map_mul, ← map_sub, ← i₀.ker.map_ideal hVU]
    exact Ideal.mem_map_of_mem r ha

end HodgeLean.Foundations.Program.G32Native
