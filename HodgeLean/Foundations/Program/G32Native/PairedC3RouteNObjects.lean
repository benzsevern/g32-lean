import HodgeLean.Foundations.AlgebraicGeometry.ConormalComparisonMap
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheaf
import HodgeLean.Ported.NYLL.SchemeTheory.Modules.Tensor.Monoidal
import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedOrientedPositiveData
import HodgeLean.Foundations.Program.SchoenPolynomialProjectiveSpace
import HodgeLean.Foundations.Program.G32Native.PairedConormalLocalFrameIso

/-! # The bundles and hyperplane quotients used in Route N -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected

/-- Polynomial projective space for the selected parameter dimension. -/
abbrev pairedC3Proj (k : ℕ) :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) ℂ)

/-- The negative twisting line, defined as the dual of the glued positive line. -/
abbrev pairedC3NegativeLine (k : ℕ) : (pairedC3Proj k).Modules :=
  (ProjSpace.twistingSheaf ℂ k).dual

/-- The bundle with a trivial summands and b negative twisting summands.
Recursion makes the zero-twist endpoint literally the indicated free module. -/
def pairedC3SplitBundle (k a : ℕ) : ℕ → (pairedC3Proj k).Modules
  | 0 => SheafOfModules.free (Fin a)
  | b + 1 => pairedC3SplitBundle k a b ⊞ pairedC3NegativeLine k

/-- The structure module of the specified reduced coordinate hyperplane,
transported to polynomial projective space. There is no tensor twist. -/
def pairedC3HyperplaneQuotient (k : ℕ) (j : Fin (k + 1)) :
    (pairedC3Proj k).Modules :=
  (Scheme.Modules.pullback (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom).obj
    ((Scheme.Modules.pushforward (s2e_s2b_residueIdeal k j).subschemeι).obj
      (SheafOfModules.unit (s2e_s2b_residueIdeal k j).subscheme.ringCatSheaf))

/-- The actual slice conormal at a specified tower stage, transported to Proj. -/
def pairedC3StageConormal
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    {R : G32JointPrefix J aut S} (P : G32JointOrientedPositiveData R)
    (i : Fin (R.r + 1)) : (pairedC3Proj R.P.k).Modules :=
  (Scheme.Modules.pullback
    (s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))).hom).obj
      (s2c_conormal (P.C.slices i).left)

/-- The natural comparison for one retained blow-up, with the identity
pullback on the slice source removed before transport to Proj. -/
def pairedC3StageComparison
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    {R : G32JointPrefix J aut S} (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) : pairedC3StageConormal P i.castSucc ⟶
      pairedC3StageConormal P i.succ := by
  let X := ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ)
  let e := s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))
  have h : (𝟙 X) ≫ (P.C.slices i.castSucc).left =
      (P.C.slices i.succ).left ≫ (P.T.b i).left := by
    rw [Category.id_comp]
    exact (congrArg Over.Hom.left (P.C.sliceComp i)).symm
  exact (Scheme.Modules.pullback e.hom).map
    (((Scheme.Modules.pullbackId X).app
      (s2c_conormal (P.C.slices i.castSucc).left)).inv ≫
      Conormal.comparisonMap (P.C.slices i.castSucc).left
        (P.C.slices i.succ).left (P.T.b i).left (𝟙 X) h)

end HodgeLean.Foundations.Program.G32Native
