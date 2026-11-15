import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNObjects
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # The actual total-transform square and its retained component -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- The supplied next slice factors through the literal total-transform
subscheme. Its projection to the old slice is the identity, and the
source-to-total square is cartesian.
Source: Hartshorne, Algebraic Geometry, II.3 and II.7.13. -/
theorem paired_c3_route_n_total_square
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    let σ := (P.T.b i).left
    let i₀ := (P.C.slices i.castSucc).left
    let i₁ := (P.C.slices i.succ).left
    let I := i₀.ker.comap σ
    ∃ (p : I.subscheme ⟶ (ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ)))
      (a : (ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ)) ⟶ I.subscheme),
      IsPullback p I.subschemeι i₀ σ ∧ a ≫ I.subschemeι = i₁ ∧ a ≫ p = 𝟙 _ := by
  dsimp only
  letI := P.C.sliceImmersion i.castSucc
  let σ := (P.T.b i).left
  let i₀ := (P.C.slices i.castSucc).left
  let i₁ := (P.C.slices i.succ).left
  let I := i₀.ker.comap σ
  let t := I.subschemeι
  have hker : i₀.ker ≤ (t ≫ σ).ker := by
    rw [← Scheme.IdealSheafData.map_ker]
    apply Scheme.IdealSheafData.le_map_iff_comap_le.mpr
    rw [Scheme.IdealSheafData.ker_subschemeι]
  let p := IsClosedImmersion.lift i₀ (t ≫ σ) hker
  have hp : p ≫ i₀ = t ≫ σ := IsClosedImmersion.lift_fac _ _ _
  have hc : i₁ ≫ σ = i₀ := congrArg Over.Hom.left (P.C.sliceComp i)
  have hI : t.ker ≤ i₁.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
    rw [Scheme.IdealSheafData.map_ker, hc]
  let a := IsClosedImmersion.lift t i₁ hI
  have ha : a ≫ t = i₁ := IsClosedImmersion.lift_fac _ _ _
  refine ⟨p, a, ?_, ha, ?_⟩
  · apply IsPullback.flip
    exact isPullback_of_isClosedImmersion t i₀ p σ hp.symm
      (Scheme.IdealSheafData.ker_subschemeι I).symm
  · apply (cancel_mono i₀).mp
    rw [Category.assoc, hp, ← Category.assoc, ha, hc, Category.id_comp]

#print axioms paired_c3_route_n_total_square
end HodgeLean.Foundations.Program.G32Native
