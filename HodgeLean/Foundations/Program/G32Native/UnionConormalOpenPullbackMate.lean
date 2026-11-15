import HodgeLean.Foundations.Program.G32Native.UnionConormalOpenMate

/-! # The pullback identification compatible with open direct image -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Open pullback comparison specified by the composed direct image adjunctions. -/
def unionConormalOpenPullbackAdjIso {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι :=
  (conjugateIsoEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))).symm
    (unionConormalOpenDirectImageSquareIso f U)

/-- The mate of open pullback comparison is the explicit open direct image identification. -/
lemma unionConormalOpenPullback_mate {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) :
    (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
      (TwoSquare.mk (Scheme.Modules.restrictFunctor U.ι)
        (Scheme.Modules.pullback f) (Scheme.Modules.pullback (f ∣_ U))
        (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι)
        (unionConormalOpenPullbackAdjIso f U).hom)).natTrans =
      (unionConormalOpenPushforwardNatIso f U).hom := by
  apply (mateEquiv (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)
    (Scheme.Modules.restrictAdjunction U.ι)).injective
  change (mateEquiv (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)
    (Scheme.Modules.restrictAdjunction U.ι)
      (mateEquiv _ _ (TwoSquare.mk _ _ _ _ (unionConormalOpenPullbackAdjIso f U).hom))).natTrans = _
  rw [iterated_mateEquiv_conjugateEquiv]
  change (conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))))
      (unionConormalOpenPullbackAdjIso f U).hom =
    (mateEquiv (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)
      (Scheme.Modules.restrictAdjunction U.ι)
      (TwoSquare.mk (Scheme.Modules.pushforward f)
        (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι)
        (Scheme.Modules.restrictFunctor U.ι)
        (Scheme.Modules.pushforward (f ∣_ U))
        (unionConormalOpenPushforwardNatIso f U).hom)).natTrans
  rw [unionConormalOpenPushforward_mate]
  exact (conjugateEquiv _ _).apply_symm_apply (unionConormalOpenDirectImageSquareIso f U).hom

end HodgeLean.Foundations.Program.G32Native
