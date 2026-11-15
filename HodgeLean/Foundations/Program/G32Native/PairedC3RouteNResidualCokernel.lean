import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNUnionCokernel
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNCokernelAmbientTransport
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNTotalIdealComparison
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNTotalTransform
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNResidueIntersection
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # The original stage comparison cokernel on the actual residual intersection -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
open AlgebraicGeometry.Conormal
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- The actual stage comparison has the direct image of the actual
residual-intersection conormal as its cokernel. All arrows are retained;
no trivialization of that final conormal is asserted here.
Source: Fulton, Intersection Theory, Appendix B.7.4;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem paired_c3_route_n_residual_cokernel
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    letI := P.C.sliceImmersion i.succ
    let E := (P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap (P.T.b i).left
    let I := (P.C.slices i.castSucc).left.ker.comap (P.T.b i).left
    Nonempty (cokernel (pairedC3StageComparison P i) ≅
      (Scheme.Modules.pullback (s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))).hom).obj
        ((Scheme.Modules.pushforward
          (residualIntersectionFirst (P.C.slices i.succ) (E ⊔ I)).left).obj
            (s2c_conormal (residualIntersectionSecond (P.C.slices i.succ) (E ⊔ I)).left))) := by
  letI := P.C.sliceImmersion i.castSucc
  letI := P.C.sliceImmersion i.succ
  letI : IsLocallyNoetherian (P.T.B i.succ).left :=
    LocallyOfFiniteType.isLocallyNoetherian (P.T.B i.succ).hom
  dsimp only
  let PP := ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ)
  let σ := (P.T.b i).left
  let i₀ := (P.C.slices i.castSucc).left
  let i₁ := (P.C.slices i.succ).left
  let I := i₀.ker.comap σ
  let t := I.subschemeι
  let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  let L := K.comap σ ⊔ I
  let s₁ := (residualIntersectionFirst (P.C.slices i.succ) L).left
  let s₂ := (residualIntersectionSecond (P.C.slices i.succ) L).left
  obtain ⟨p, a, sq, ha, hap⟩ := paired_c3_route_n_total_square R P i
  obtain ⟨p₀, sq₀, hcomp⟩ := paired_c3_route_n_total_ideal_comparison_aux R P i
  haveI : IsIso ((Scheme.Modules.pullback i₁).map (idealPullbackMap i₀ t σ p sq.w)) := by
    rw [← idealPullbackMap_eq_of_ambient i₀ t σ p₀ p sq₀.w sq.w]
    exact hcomp
  let m := idealPullbackMap i₀ t σ p sq.w
  haveI : IsIso ((Scheme.Modules.pullback i₁).map ((Scheme.Modules.pullback (𝟙 _)).map m)) :=
    (NatIso.isIso_map_iff
      (Functor.isoWhiskerRight (Scheme.Modules.pullbackId (P.T.B i.succ).left)
        (Scheme.Modules.pullback i₁)) m).mpr
      (by change IsIso ((Scheme.Modules.pullback i₁).map (idealPullbackMap i₀ t σ p sq.w))
          infer_instance)
  have hc : i₁ ≫ σ = i₀ := congrArg Over.Hom.left (P.C.sliceComp i)
  have hcc : (a ≫ p) ≫ i₀ = i₁ ≫ ((𝟙 _) ≫ σ) := by
    rw [hap, Category.id_comp, Category.id_comp, hc]
  have hunion : t.ker = i₁.ker ⊓ L.subschemeι.ker := by
    change I.subschemeι.ker = i₁.ker ⊓ L.subschemeι.ker
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
    exact paired_c3_route_n_total_transform R P i
  have hs : s₁ ≫ i₁ = s₂ ≫ L.subschemeι :=
    congrArg Over.Hom.left (residualIntersection_square (P.C.slices i.succ) L)
  have hfac : s₁ ≫ i₁ = (i₁.ker ⊔ L).subschemeι :=
    residualIntersectionFirst_fac (P.C.slices i.succ) L
  have hinter : (s₁ ≫ i₁).ker = i₁.ker ⊔ L.subschemeι.ker := by
    rw [hfac, Scheme.IdealSheafData.ker_subschemeι,
      Scheme.IdealSheafData.ker_subschemeι]
  let eUnion := pairedUnionConormalCokernelIso t i₁ L.subschemeι a s₁ s₂ ha hs hunion hinter
  let eFull := pairedConormalCompositeCokernelIso i₀ t i₁ σ (𝟙 _) p a sq.w
    (ha.trans (Category.comp_id i₁).symm) hcc
  let hNative := (Category.id_comp i₀).trans hc.symm
  let native := comparisonMap i₀ i₁ σ (𝟙 PP) hNative
  let eNative := pairedConormalCokernelIsoOfAmbient i₀ i₁ σ ((𝟙 _) ≫ σ)
      (Category.id_comp σ).symm (𝟙 PP) (a ≫ p) hNative hcc ≪≫ eFull ≪≫ eUnion
  let raw := ((Scheme.Modules.pullbackId PP).app (s2c_conormal i₀)).inv ≫ native
  let eRaw := cokernel.mapIso raw native ((Scheme.Modules.pullbackId PP).app
      (s2c_conormal i₀)).symm (Iso.refl _) (by
        simp only [raw, Iso.refl_hom, Category.comp_id, Iso.symm_hom])
  let F := Scheme.Modules.pullback (s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))).hom
  letI := (Scheme.Modules.pullbackPushforwardAdjunction
    (s2_polynomialProjectiveSpaceIso ℂ (Fin (R.P.k + 1))).hom).leftAdjoint_preservesColimits
  exact ⟨(PreservesCokernel.iso F raw).symm ≪≫ F.mapIso (eRaw ≪≫ eNative)⟩

#print axioms paired_c3_route_n_residual_cokernel
end HodgeLean.Foundations.Program.G32Native
