import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineComparison

/-! # Pullback transport for a commuting square -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- A commuting square transports iterated module pullback naturally. -/
def unionConormalSquarePullbackIso
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f) :
    Scheme.Modules.pullback i ⋙ Scheme.Modules.pullback g ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback i' :=
  Scheme.Modules.pullbackComp g i ≪≫ Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp i' f).symm

/-- Evaluating square transport on the ideal gives the conormal prefix. -/
lemma unionConormalSquarePullbackIso_ideal_hom
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f) :
    (unionConormalSquarePullbackIso i i' f g h).hom.app
        (AlgebraicGeometry.Conormal.idealModule i) =
      (unionConormalComparisonPrefixIso i i' f g h).hom := by
  simp only [unionConormalSquarePullbackIso, unionConormalComparisonPrefixIso,
    Iso.trans_hom, NatTrans.comp_app, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    unionConormal_pullbackCongr_hom_app]
  have he := unionConormal_pullbackCongr_hom_app h
    (AlgebraicGeometry.Conormal.idealModule i)
  simp only [Iso.app_hom] at he
  rw [he]
  rfl

end HodgeLean.Foundations.Program.G32Native
