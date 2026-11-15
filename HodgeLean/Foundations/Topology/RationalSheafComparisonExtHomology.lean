import HodgeLean.Foundations.Topology.RationalSheafComparisonExtTransport
import HodgeLean.Foundations.Topology.RationalSheafComparisonHomTransport

/-! Exact-functor transport through Hom-complex homology and Ext.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CochainComplex CochainComplex.HomComplex
namespace HodgeLean.Topology.RationalSheafComparison

universe v w w'

/-- Source: Bredon, Sheaf Theory, second edition, II.4. -/
theorem resolutionHomology_transport
    {C D : Type*} [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
    [HasExt.{w} C] [HasExt.{w'} D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [Limits.PreservesFiniteLimits F]
    [Limits.PreservesFiniteColimits F]
    {A B : C} {A' B' : D} (R : InjectiveResolution B) (S : InjectiveResolution B')
    (a : A' ⟶ F.obj A) (b : F.obj B ⟶ B')
    (c : (F.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex ⟶ S.cochainComplex)
    (hc : (F.mapHomologicalComplex (.up ℤ)).map R.ι' ≫ c =
      (F.mapCochainComplexSingleFunctor 0).hom.app B ≫
        (CochainComplex.singleFunctor D 0).map b ≫ S.ι')
    (n : ℕ) (x : (HomComplex ((CochainComplex.singleFunctor C 0).obj A) R.cochainComplex).homology (n : ℤ)) :
    S.extEquivCohomologyClass.symm
      (homologyAddEquiv _ _ (n : ℤ)
        (HomologicalComplex.homologyMap
          (functorHomTransport F
            ((CochainComplex.singleFunctor D 0).map a ≫
              (F.mapCochainComplexSingleFunctor 0).inv.app A) c) (n : ℤ) x)) =
      ((Abelian.Ext.mk₀ a).comp
        ((R.extEquivCohomologyClass.symm (homologyAddEquiv _ _ (n : ℤ) x)).mapExactFunctor F)
          (zero_add n)).comp (Abelian.Ext.mk₀ b) (add_zero n) := by
  rw [homologyAddEquiv_functorHomTransport]
  obtain ⟨z, hz⟩ := (homologyAddEquiv _ _ (n : ℤ) x).mk_surjective
  rw [← hz, functorClassTransport_mk]
  exact resolutionClass_transport F R S a b c hc z

end HodgeLean.Topology.RationalSheafComparison
