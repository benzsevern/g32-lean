import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedNormalizationUnit
import HodgeLean.Foundations.Program.G32Native.PairedC3SuppliedMarkedIdeal
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidueSupport
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

attribute [local instance] G32JointSlicedComponent.sliceImmersion
open HodgeLean.Foundations.Program.G32Native

/-- On an actual selected Rees chart, the next slice cuts the residual
component at the translated raw ratio. The slice ideal is the stored one. -/
theorem pairedC3_selected_chart_marked_ideal
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (U : (P.T.B i.castSucc).left.affineOpens)
    [Nonempty ((P.C.slices i.castSucc).left ⁻¹ᵁ U.1)]
    (V : (P.T.B i.succ).left.affineOpens)
    (hV : V.1 ≤ (P.T.b i).left ⁻¹ᵁ U.1)
    (u v α : Γ((P.T.B i.castSucc).left, U))
    (t : Γ((P.T.B i.succ).left, V))
    (hu : (P.T.D i.castSucc ⟨2 * i.val, by omega⟩).ideal U = Ideal.span {u})
    (hv : (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal U = Ideal.span {v})
    (hrel : ((P.T.b i).left.appLE U.1 V.1 hV).hom v =
      t * ((P.T.b i).left.appLE U.1 V.1 hV).hom u)
    (hs : Function.Surjective
      (Polynomial.eval₂RingHom ((P.T.b i).left.appLE U.1 V.1 hV).hom t))
    (hk : RingHom.ker
      (Polynomial.eval₂RingHom ((P.T.b i).left.appLE U.1 V.1 hV).hom t) =
      Ideal.span {Polynomial.C v - Polynomial.X * Polynomial.C u})
    (hα : ((P.C.slices i.castSucc).left.app U.1).hom (v - α * u) = 0) :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let M := (K ⊔ (P.C.slices i.castSucc).left.ker).comap (P.T.b i).left
    let q := Ideal.Quotient.mk (M.ideal V)
    Ideal.map q ((P.C.slices i.succ).left.ker.ideal V) =
      Ideal.span {q t - q (((P.T.b i).left.appLE U.1 V.1 hV).hom α)} := by
  dsimp only
  letI : IsIntegral (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))).left :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral R.P.k
  letI := P.C.sliceImmersion i.castSucc
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i le_rfl
  have hproper : ((P.T.D i.castSucc ⟨2 * i.val, by omega⟩).comap
      (P.C.slices i.castSucc).left).support ≠ ⊤ := by
    rw [hp.1]
    exact paired_c3_residue_support_proper _ _
  rw [P.C.sliceStrict i]
  exact pairedC3_supplied_strict_marked_ideal (P.C.slices i.castSucc).left
    (P.T.b i).left _ _ hproper U V hV u v α t hu hv hrel hs hk hα

#print axioms pairedC3_selected_chart_marked_ideal
end HodgeLean.Foundations.Program.ResidueSelected
