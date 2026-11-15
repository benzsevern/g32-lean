import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedIndependentGerms
import HodgeLean.Foundations.Program.G32Native.PairedC3AdaptedCentreIdeal
import HodgeLean.Foundations.Program.G32Native.PairedC3SmoothEquationsInside
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedSliceDimensions
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedAmbientDimension
import HodgeLean.Ported.Hironaka.Resolution.Algebraic.Order.SupPow

/-! # Actual selected slice equations in adapted affine coordinates -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- Pointwise adapted generators give actual affine étale equations for the
selected slice, retaining both original branch ideals on the smaller open.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8; EGA IV, 17.11.1;
Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 2.8. -/
theorem paired_c3_selected_last_adapted_coordinates
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r)
    (x : ComplexPoint (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))))
    (hx : x.underlying ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support) :
    ∃ (d n : ℕ) (_ : n + 1 = R.P.k) (U : (P.T.B i.castSucc).left.affineOpens)
      (u v a : Γ((P.T.B i.castSucc).left, U)),
      (P.C.slices i.castSucc).left x.underlying ∈ U.1 ∧
      (P.T.D i.castSucc ⟨2 * i.val, by omega⟩).ideal U = Ideal.span {u} ∧
      (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal U = Ideal.span {v} ∧
      letI := HodgeLean.Foundations.Program.s2e_step1_sectionAlgebra (P.T.B i.castSucc) U.1
      ∃ (F : MvPolynomial (Fin d) ℂ →ₐ[ℂ] Γ((P.T.B i.castSucc).left, U.1))
        (e : Fin (n + 2) ↪ Fin d),
        F.toRingHom.Etale ∧
        (P.C.slices i.castSucc).left.ker.ideal U = Ideal.span
          (Set.range (fun j : Fin (n + 1) => F (MvPolynomial.X (e j.succ)))) ∧
        v = F (MvPolynomial.X (e 0)) ∧
        u - a * v = F (MvPolynomial.X (e (0 : Fin (n + 1)).succ)) := by
  obtain ⟨V, u, v, a, hpV, hu, hv, ha, hmu, hmv, htrans⟩ :=
    paired_c3_selected_last_independent_germs R P i hi x hx
  let X := P.T.B i.castSucc
  let p := (P.C.slices i.castSucc).left x.underlying
  let g := (X.left.presheaf.germ V.1 p hpV).hom
  let I := (P.C.slices i.castSucc).left.ker
  let D₁ := P.T.D i.castSucc ⟨2 * i.val, by omega⟩
  let D₂ := P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  let D := I ⊔ (D₁ ⊔ D₂)
  have ht : g u - g a * g v ∈ I.stalkIdeal p := by
    rw [I.stalkIdeal_eq_map_germ V (x := p) (show p ∈ V.1 from hpV)]
    simpa only [map_sub, map_mul] using Ideal.mem_map_of_mem g ha
  have hD₁ : D₁.stalkIdeal p = Ideal.span {g u} := by
    rw [D₁.stalkIdeal_eq_map_germ V (x := p) (show p ∈ V.1 from hpV), hu, Ideal.map_span, Set.image_singleton]
  have hD₂ : D₂.stalkIdeal p = Ideal.span {g v} := by
    rw [D₂.stalkIdeal_eq_map_germ V (x := p) (show p ∈ V.1 from hpV), hv, Ideal.map_span, Set.image_singleton]
  have hD : D.stalkIdeal p = I.stalkIdeal p ⊔ Ideal.span {g v} := by
    dsimp only [D]
    rw [Scheme.IdealSheafData.stalkIdeal_sup, Scheme.IdealSheafData.stalkIdeal_sup, hD₁, hD₂]
    exact G32Native.paired_c3_adapted_centre_ideal _ _ _ _ ht
  have hpI : p ∈ I.support := (P.C.slices i.castSucc).left.range_subset_ker_support
    ⟨x.underlying, rfl⟩
  have hIm := (I.mem_support_iff_stalkIdeal_le_maximalIdeal p).mp hpI
  have hpD : p ∈ D.support := (D.mem_support_iff_stalkIdeal_le_maximalIdeal p).mpr (by
    rw [hD]
    exact sup_le hIm (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmv)))
  have hk : 0 < R.P.k := R.P.act.cyc_positive
  have hk1 : R.P.k - 1 + 1 = R.P.k := by omega
  have hk2 : R.P.k - 1 + 2 = R.P.k + 1 := by omega
  letI : SmoothOfRelativeDimension (R.P.k + (R.P.k - 1 + 1)) X.hom := by
    rw [hk1, ← two_mul]
    exact paired_c3_selected_ambient_relative_dimension R P i.castSucc
  letI : SmoothOfRelativeDimension R.P.k (I.subschemeι ≫ X.hom) :=
    paired_c3_selected_slice_image_dimension R P i.castSucc
  letI : SmoothOfRelativeDimension (R.P.k - 1) (D.subschemeι ≫ X.hom) :=
    paired_c3_selected_centre_slice_dimension R P i
  have hs := G32Native.paired_c3_smooth_equations_inside X R.P.k (R.P.k - 1) hk I D
    (Point.map (P.C.slices i.castSucc) x) hpD
    ⟨g v, hmv⟩ ⟨g u, hmu⟩ hD
    (LinearIndependent.pair_symm_iff.mpr htrans) (g a) ht V hpV v (u - a * v) rfl
    (by change g (u - a * v) = g u - g a * g v; rw [map_sub, map_mul])
  obtain ⟨U, hUV, hpU, F, e, hF, hI, hvc, hdc⟩ := hs
  let res := (X.left.presheaf.map (homOfLE (show U.1 ≤ V.1 from hUV)).op).hom
  refine ⟨R.P.k + (R.P.k - 1 + 1), R.P.k - 1, hk1, U, res u, res v, res a, hpU, ?_, ?_, F, e, hF, hI, hvc, ?_⟩
  · rw [← D₁.map_ideal hUV, hu, Ideal.map_span, Set.image_singleton]
    rfl
  · rw [← D₂.map_ideal hUV, hv, Ideal.map_span, Set.image_singleton]
    rfl
  · change res (u - a * v) = _ at hdc
    rw [map_sub, map_mul] at hdc
    exact hdc

#print axioms paired_c3_selected_last_adapted_coordinates
end HodgeLean.Foundations.Program.ResidueSelected
