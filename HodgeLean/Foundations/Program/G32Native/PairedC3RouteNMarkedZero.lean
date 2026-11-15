import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedMarkedIdeal
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNRulingParameters
import HodgeLean.Foundations.Program.G32Native.PairedC3SuppliedReciprocalMarkedIdeal
import HodgeLean.Foundations.Program.G32Native.PairedC3RatioNormalization
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

/-- The actual slice ideal on selected chart 0 is the normalized marked ideal. -/
theorem pairedC3_route_n_parameter_marked_ideal_0
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (C : PairedC3RouteNRulingParameters R P i)
    (x : {x : ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ) //
      x ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support}) :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let D := K ⊔ (P.C.slices i.castSucc).left.ker
    let M := D.comap (P.T.b i).left
    let q := Ideal.Quotient.mk (M.ideal (C.V x 0))
    let b := pairedC3AffineResidualCoefficient (P.T.b i).left D (C.U x) (C.V x 0) (C.h₀ x)
    let β := Units.map b.toMonoidHom (C.equations x).2.2.2.2.1.unit
    Ideal.map q ((P.C.slices i.succ).left.ker.ideal (C.V x 0)) =
      Ideal.span {((↑β : Γ((P.T.B i.succ).left, C.V x 0) ⧸ M.ideal (C.V x 0)) *
        q (C.s x) - 1)} := by
  letI : IsIntegral (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))).left :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral R.P.k
  letI : Nonempty ((P.C.slices i.castSucc).left ⁻¹ᵁ (C.U x).1) :=
    ⟨⟨x.val, C.contains x⟩⟩
  dsimp only
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i le_rfl
  have hproper : ((P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap
      (P.C.slices i.castSucc).left).support ≠ ⊤ := by
    rw [hp.2]
    exact paired_c3_residue_support_proper _ _
  rw [P.C.sliceStrict i]
  exact pairedC3_supplied_reciprocal_marked_ideal (P.C.slices i.castSucc).left
    (P.T.b i).left _ _ hproper (C.U x) (C.V x 0) (C.h₀ x)
    (C.u x) (C.v x) (C.α x) (C.s x)
    (C.equations x).1 (C.equations x).2.1
    (C.equations x).2.2.2.2.2.1
    (C.equations x).2.2.2.2.2.2.2.1
    (C.equations x).2.2.2.2.2.2.2.2.1
    (C.equations x).2.2.1 (C.equations x).2.2.2.1
    (C.equations x).2.2.2.2.1

#print axioms pairedC3_route_n_parameter_marked_ideal_0


end HodgeLean.Foundations.Program.ResidueSelected
