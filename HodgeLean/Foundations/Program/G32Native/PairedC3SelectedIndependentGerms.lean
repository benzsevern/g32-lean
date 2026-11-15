import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedBranchCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedAdaptedEquation
import HodgeLean.Ported.Hironaka.Scheme.IdealSheaf.StalkIdeal
import HodgeLean.Ported.Hironaka.Scheme.IdealSheaf.Order.Basic

/-! # Independent original branch germs and the actual adapted slice equation -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- At a retained residue point the original branch sections have independent
cotangent germs, and their adapted difference lies in the actual slice ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2 and Sublemma 2.7;
Hartshorne, Algebraic Geometry, II.5 and II.8. -/
theorem paired_c3_selected_last_independent_germs
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r)
    (x : ComplexPoint (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))))
    (hx : x.underlying ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support) :
    let p := (P.C.slices i.castSucc).left x.underlying
    let A := (P.T.B i.castSucc).left.presheaf.stalk p
    ∃ (U : (P.T.B i.castSucc).left.affineOpens)
      (u v a : Γ((P.T.B i.castSucc).left, U)) (hpU : p ∈ U.1),
      (P.T.D i.castSucc ⟨2 * i.val, by omega⟩).ideal U = Ideal.span {u} ∧
      (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal U = Ideal.span {v} ∧
      u - a * v ∈ (P.C.slices i.castSucc).left.ker.ideal U ∧
      ∃ (hmu : ((P.T.B i.castSucc).left.presheaf.germ U.1 p hpU).hom u ∈ maximalIdeal A)
        (hmv : ((P.T.B i.castSucc).left.presheaf.germ U.1 p hpU).hom v ∈ maximalIdeal A),
      LinearIndependent (ResidueField A)
        ![(maximalIdeal A).toCotangent ⟨((P.T.B i.castSucc).left.presheaf.germ U.1 p hpU).hom u, hmu⟩,
          (maximalIdeal A).toCotangent ⟨((P.T.B i.castSucc).left.presheaf.germ U.1 p hpU).hom v, hmv⟩] := by
  dsimp only
  obtain ⟨U, hn, z, hxU, het, hu, hv⟩ := paired_c3_selected_last_branch_coordinates R P i hi x hx
  let X := (P.T.B i.castSucc).left
  let p := (P.C.slices i.castSucc).left x.underlying
  let g := (X.presheaf.germ U.1 p hxU).hom
  let u := z ⟨0, by omega⟩
  let v := z ⟨1, by omega⟩
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i le_rfl
  have hm (D : X.IdealSheafData) (s : Γ(X, U.1))
      (hD : D.ideal U = Ideal.span {s})
      (heq : D.comap (P.C.slices i.castSucc).left =
        s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)) :
      g s ∈ maximalIdeal (X.presheaf.stalk p) := by
    have hpD : p ∈ D.support := by
      have h : x.underlying ∈ (D.comap (P.C.slices i.castSucc).left).support := by
        rw [heq]
        exact hx
      rw [Scheme.IdealSheafData.support_comap] at h
      exact h
    apply (D.mem_support_iff_stalkIdeal_le_maximalIdeal p).mp hpD
    rw [D.stalkIdeal_eq_map_germ U (x := p) (show p ∈ U.1 from hxU), hD]
    exact Ideal.mem_map_of_mem g (Ideal.subset_span (Set.mem_singleton _))
  have hmu := hm _ u hu hp.1
  have hmv := hm _ v hv hp.2
  let e : Fin 2 ↪ Fin (R.h + 1) := ⟨fun j => ⟨j.val, by omega⟩,
    fun _ _ h => Fin.ext (congrArg (fun t : Fin (R.h + 1) => t.val) h)⟩
  have hcoords (j : Fin 2) : g (z (e j)) ∈ maximalIdeal (X.presheaf.stalk p) := by
    fin_cases j
    · exact hmu
    · exact hmv
  have H := G32Native.paired_c3_affine_cotangent_independent X U p hxU
    ((P.T.B i.castSucc).hom.appLE ⊤ U.1 le_top).hom z het e hcoords
  obtain ⟨a, ha⟩ := paired_c3_selected_adapted_ideal R P i.castSucc i le_rfl U u v hu hv
  refine ⟨U, u, v, a, hxU, hu, hv, ha, hmu, hmv, ?_⟩
  convert H using 1
  ext j
  fin_cases j <;> rfl

#print axioms paired_c3_selected_last_independent_germs
end HodgeLean.Foundations.Program.ResidueSelected
