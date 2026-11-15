import HodgeLean.Foundations.Program.G32Native.PairedC3FreeExtension
import HodgeLean.Foundations.Program.G32Native.PairedC3FrameExtension
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNInduction
import HodgeLean.Foundations.Program.G32Native.PairedConormalIsoPullback
import HodgeLean.Foundations.Program.SchoenPolynomialProjectiveSpace
import HodgeLean.Foundations.Program.G32Native.ResidueJointSelectedOrientedPositiveData

/-! # The retained penultimate conormal frame

Route N uses the full initial Abel fibre only at stage zero, then a
single-pair elementary modification at each strict-prefix step. At the
penultimate stage its global frame gives the requested split extension.
The final blowup is excluded.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29

/-- The geometric conormal extension on the actual penultimate slice,
written through the polynomial projective-space identification. Construct
it from the Route N frame on the strict prefix of the full ambient tower.
The two outer frames have ranks g and r−1.
Source: ACGH, Geometry of Algebraic Curves I, IV.1–IV.3;
Schoen, Compositio Mathematica 65 (1988), Lemma 2.3(ii) and proof of
Lemma 2.4; Hartshorne, Algebraic Geometry, II.8, Theorem 8.17.
Open: uses the initial flag, single-pair modification and projective splitting
steps in PairedC3RouteNInitial, PairedC3RouteNStep and PairedC3RouteNSplitting. -/
theorem paired_c3_penultimate_extension_aux
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (last : Fin R.r) (hlast : last.val + 1 = R.r) :
    let N := Proj (MvPolynomial.homogeneousSubmodule (Fin (R.P.k + 1)) ℂ)
    let e := s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))
    let i₀ := (P.C.slices last.castSucc).left
    ∃ E : ShortComplex N.Modules,
      E.ShortExact ∧ E.X₂.IsQuasicoherent ∧
      Nonempty (E.X₂ ≅ (Scheme.Modules.pullback e.hom).obj (s2c_conormal i₀)) ∧
      Nonempty (E.X₁ ≅ SheafOfModules.free (Fin (R.P.k + 1 - R.r))) ∧
      Nonempty (E.X₃ ≅ SheafOfModules.free (Fin (R.r - 1))) := by
  obtain ⟨e⟩ := paired_c3_route_n_penultimate_frame R P last hlast
  have hrk : R.r ≤ R.P.k + 1 := by
    have h := Fintype.card_le_of_injective _ P.C.residue.indices.injective
    simpa only [Fintype.card_fin] using h
  have hdim : (R.P.k + 1 - R.r) + (R.r - 1) = R.P.k := by
    have := last.isLt
    omega
  exact paired_c3_extension_of_frame _ _ _ _ hdim e

/-- Frame of the retained penultimate immersion in the full ambient,
obtained by splitting the conormal extension. Its source is
the projective parameter scheme, rather than the component upstairs.
Source: Schoen, Compositio Mathematica 65 (1988), proof of Lemma 2.4;
Hartshorne, Algebraic Geometry, III, Theorem 5.1.
Open: depends on paired_c3_penultimate_extension_aux. -/
def pairedC3PenultimateFrame
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (last : Fin R.r) (hlast : last.val + 1 = R.r) :
    s2c_conormal (P.C.slices last.castSucc).left ≅
      (SheafOfModules.free (R :=
        (ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ)).ringCatSheaf)
        (Fin R.P.k) :
        (ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ)).Modules) := by
  let h := paired_c3_penultimate_extension_aux R P last hlast
  let E := Classical.choose h
  have hE := Classical.choose_spec h
  letI : E.X₂.IsQuasicoherent := hE.2.1
  let eM := Classical.choice hE.2.2.1
  let e₁ := Classical.choice hE.2.2.2.1
  let e₃ := Classical.choice hE.2.2.2.2
  letI : E.X₃.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent _).prop_of_iso e₃.symm inferInstance
  have hr := last.isLt
  have hrk : R.r ≤ R.P.k + 1 := by
    have hc := Fintype.card_le_of_injective _ P.C.residue.indices.injective
    simpa only [Fintype.card_fin] using hc
  have hdim : (R.P.k + 1 - R.r) + (R.r - 1) = R.P.k := by omega
  let e := s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))
  let F := Scheme.Modules.pullback e.hom
  letI : F.IsEquivalence := paired_module_pullback_isEquivalence e
  letI : (SheafOfModules.pushforward e.hom.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward e.hom).IsRightAdjoint
  let frame := pairedC3FreeExtensionFrame ℂ R.P.k E hE.1 _ _ e₁ e₃
  let reindex := (SheafOfModules.freeFunctor (R :=
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (R.P.k + 1)) ℂ)).ringCatSheaf)).mapIso (Equiv.cast (congrArg Fin hdim)).toIso
  exact F.preimageIso (eM.symm ≪≫ frame ≪≫ reindex ≪≫
    (SheafOfModules.pullbackObjFreeIso e.hom.toRingCatSheafHom (Fin R.P.k)).symm)

#print axioms paired_c3_penultimate_extension_aux
#print axioms pairedC3PenultimateFrame
end HodgeLean.Foundations.Program.G32Native
