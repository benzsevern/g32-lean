import HodgeLean.Foundations.Program.G32Native.UnionConormalOpenPullbackMate

/-! # Descending unit epimorphy through ambient open restriction -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- An epic unit on the restricted diagram gives an epic restriction of the original unit. -/
lemma unionConormal_unit_restrict_epi
    {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (M : Y.Modules)
    [Epi ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
      ((Scheme.Modules.restrictFunctor U.ι).obj M))] :
    Epi ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)) := by
  let α := TwoSquare.mk (Scheme.Modules.restrictFunctor U.ι)
    (Scheme.Modules.pullback f) (Scheme.Modules.pullback (f ∣_ U))
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι)
    (unionConormalOpenPullbackAdjIso f U).hom
  have he := unit_mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)) α M
  have hm := congrArg (fun η => η.app ((Scheme.Modules.pullback f).obj M))
    (unionConormalOpenPullback_mate f U)
  change (mateEquiv _ _ α).app _ = _ at hm
  rw [hm] at he
  haveI : Epi ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (unionConormalOpenPushforwardNatIso f U).hom.app ((Scheme.Modules.pullback f).obj M)) := by
    rw [he]
    change Epi ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app _ ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map ((unionConormalOpenPullbackAdjIso f U).hom.app M))
    infer_instance
  exact (epi_comp_iff_of_isIso _
    ((unionConormalOpenPushforwardNatIso f U).hom.app ((Scheme.Modules.pullback f).obj M))).mp
      inferInstance

end HodgeLean.Foundations.Program.G32Native
