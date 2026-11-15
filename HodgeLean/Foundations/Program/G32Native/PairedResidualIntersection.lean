import HodgeLean.Foundations.Program.G32Native.PairedResidualDiagramGeometry

/-! # The residual intersection as an actual fibre product -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

variable {C : Scheme} {P V : Over C} (i : P ⟶ V)
  [IsClosedImmersion i.left] (J : V.left.IdealSheafData)

/-- The ideal sum gives the fibre product with the specified residual component. -/
theorem residualIntersection_isPullback :
    IsPullback (residualIntersectionFirst i J).left
      (residualIntersectionSecond i J).left i.left
      (residualComponentι (V := V) J).left := by
  have hf : (residualIntersectionFirst i J).left ≫ i.left =
      (i.left.ker ⊔ J).subschemeι := residualIntersectionFirst_fac i J
  have hg : (residualIntersectionSecond i J).left ≫
      (residualComponentι (V := V) J).left = (i.left.ker ⊔ J).subschemeι :=
    (congrArg Over.Hom.left (residualIntersection_square i J)).symm.trans hf
  have hk (s : PullbackCone i.left (residualComponentι (V := V) J).left) :
      i.left.ker ⊔ J ≤ (s.fst ≫ i.left).ker := by
    apply sup_le (Scheme.Hom.le_ker_comp s.fst i.left)
    rw [s.condition]
    have h := Scheme.Hom.le_ker_comp s.snd (residualComponentι (V := V) J).left
    change J.subschemeι.ker ≤ _ at h
    rwa [Scheme.IdealSheafData.ker_subschemeι] at h
  let l (s : PullbackCone i.left (residualComponentι (V := V) J).left) :
      s.pt ⟶ (residualIntersection i J).left :=
    IsClosedImmersion.lift (i.left.ker ⊔ J).subschemeι (s.fst ≫ i.left)
      (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hk s)
  have hl (s : PullbackCone i.left (residualComponentι (V := V) J).left) :
      l s ≫ (i.left.ker ⊔ J).subschemeι = s.fst ≫ i.left :=
    IsClosedImmersion.lift_fac _ _ _
  have hfst (s : PullbackCone i.left (residualComponentι (V := V) J).left) :
      l s ≫ (residualIntersectionFirst i J).left = s.fst := by
    apply (cancel_mono i.left).mp
    rw [Category.assoc, hf, hl]
  have hsnd (s : PullbackCone i.left (residualComponentι (V := V) J).left) :
      l s ≫ (residualIntersectionSecond i J).left = s.snd := by
    apply (cancel_mono (residualComponentι (V := V) J).left).mp
    rw [Category.assoc, hg, hl, s.condition]
  apply IsPullback.of_isLimit'
    ⟨congrArg Over.Hom.left (residualIntersection_square i J)⟩
  refine PullbackCone.IsLimit.mk _ l hfst hsnd ?_
  intro s m hm _
  apply (cancel_mono (residualIntersectionFirst i J).left).mp
  exact hm.trans (hfst s).symm

/-- Its ideal on the retained component is the pulled residual ideal. -/
theorem residualIntersectionFirst_kernel :
    (residualIntersectionFirst i J).left.ker = J.comap i.left := by
  let h := residualIntersection_isPullback i J
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  exact congrArg (fun K => K.comap i.left) J.ker_subschemeι

#print axioms residualIntersection_isPullback
#print axioms residualIntersectionFirst_kernel

end HodgeLean.Foundations.Program.G32Native
