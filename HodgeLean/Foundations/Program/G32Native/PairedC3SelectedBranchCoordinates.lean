import HodgeLean.Foundations.Program.G32Native.PairedC3AffineCotangentIndependent
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedRestrictions
import HodgeLean.Foundations.Program.SchoenTowerL1b

/-! # Selected branch coordinates at the retained residue hyperplane -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- The selected last pair retains its original simultaneous affine
étale branch coordinates at each complex residue point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2 and Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.8. -/
theorem paired_c3_selected_last_branch_coordinates
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r)
    (x : ComplexPoint (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))))
    (hx : x.underlying ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support) :
    ∃ (U : (P.T.B i.castSucc).left.affineOpens) (hn : 2 ≤ R.h + 1)
      (z : Fin (R.h + 1) → Γ((P.T.B i.castSucc).left, U)),
      (Point.map (P.C.slices i.castSucc) x).underlying ∈ U.1 ∧
      (MvPolynomial.eval₂Hom ((P.T.B i.castSucc).hom.appLE ⊤ U.1 le_top).hom z).Etale ∧
      (P.T.D i.castSucc ⟨2 * i.val, by omega⟩).ideal U =
        Ideal.span {z ⟨0, by omega⟩} ∧
      (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal U =
        Ideal.span {z ⟨1, by omega⟩} := by
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i (by rfl)
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
  have havoid : ∀ t : Fin (2 * R.r), t.val ≠ 2 * i.val → t.val ≠ 2 * i.val + 1 →
      (Point.map (P.C.slices i.castSucc) x).underlying ∉ (P.T.D i.castSucc t).support := by
    intro t ht₀ ht₁ hmem
    have ht : t.val < 2 * i.val := by omega
    exact Set.disjoint_left.mp (P.C.sliceAvoidance i.castSucc t ht)
      ⟨x.underlying, rfl⟩ hmem
  exact s2v_l1b_tower_branch_generators S R.Y R.Z R.W₀ R.B₀ R.hdimY R.hdimZ R.a R.e R.ha1 R.hamul R.hinj R.p₀ R.hp₀ R.hpsurj R.hporbit R.C R.eY R.hpointAction R.r R.σ R.y R.rot R.hrot R.hy R.hbranch R.hexp R.hpair R.h R.hh R.q₀ R.hqsurj R.hqinv R.hq R.γ R.hγsurj R.hγinv R.hγ R.β₀ R.hβ₀ R.d₀ R.hd₀ R.hgenerator P.T.B P.T.e₀ P.T.b P.T.D P.T.hD₀ P.T.htransform P.T.hcartier P.T.hblowup P.T.η P.T.hη₀ P.T.hη P.T.eW P.T.heW P.T.hgeneric P.T.w P.T.hw P.T.d P.T.hd P.T.hdinit P.T.hdw P.T.horder i (Point.map (P.C.slices i.castSucc) x) hx₁ hx₂ havoid

#print axioms paired_c3_selected_last_branch_coordinates
end HodgeLean.Foundations.Program.ResidueSelected
