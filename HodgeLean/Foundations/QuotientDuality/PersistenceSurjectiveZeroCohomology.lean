import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Cohomology

/-! Degree-zero detection for actual surjective continuous maps over any field. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_surjective_cohomology_zero_injective
    (K : Type) [Field K] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : Function.Surjective f) :
    Function.Injective (AlgebraicTopology.Singular.cohomologyMap K 0 f) := by
  let φ := AlgebraicTopology.Singular.singularChainComplexMap K f
  have hf₀ : Function.Surjective ((TopCat.toSSet.map f).app
      (Opposite.op (SimplexCategory.mk 0))) := by
    intro y
    let t := Y.toSSetObjEquiv _ y
    obtain ⟨x, hx⟩ := hf (t (Convexity.StdSimplex.single (R := ℝ) (0 : Fin 1)))
    refine ⟨(X.toSSetObjEquiv _).symm (ContinuousMap.const _ x), ?_⟩
    apply (Y.toSSetObjEquiv _).injective
    ext z
    change f x = t z
    haveI : Subsingleton (Fin 1) := inferInstance
    haveI : Subsingleton (Convexity.StdSimplex ℝ (Fin 1)) := inferInstance
    exact hx.trans (congrArg t (Subsingleton.elim _ _))
  have hep : Epi (φ.f 0) := by
    constructor
    intro Z g h e
    apply SSet.chainComplex_hom_ext
    intro y
    obtain ⟨x, rfl⟩ := hf₀ y
    have he := congrArg (fun k => (TopCat.toSSet.obj X).ιChainComplex x ≫ k) e
    change ((TopCat.toSSet.obj X).ιChainComplex x ≫
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of K K)).f 0) ≫ g =
      ((TopCat.toSSet.obj X).ιChainComplex x ≫
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of K K)).f 0) ≫ h at he
    simpa only [SSet.ι_chainComplexMap_f] using he
  have hepH : Epi (HomologicalComplex.homologyMap φ 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel φ 0 (by intro j; simp)
  have hs : Function.Surjective (AlgebraicTopology.Singular.homologyMap K 0 f) :=
    (ModuleCat.epi_iff_surjective _).mp hepH
  intro a b hab
  apply (AlgebraicTopology.Singular.cohomologyEquivDualHomology K Y 0).injective
  ext z
  obtain ⟨w, rfl⟩ := hs z
  have he := congrArg (fun c =>
    AlgebraicTopology.Singular.cohomologyEquivDualHomology K X 0 c w) hab
  simpa only [AlgebraicTopology.Singular.cohomologyEquivDualHomology_cohomologyMap] using he


end HodgeLean.Foundations.QuotientDuality
