import HodgeLean.Foundations.Program.CompensationAssemblyPrismPullback

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem cq_cohomologyClass_pairing_homologyπ (X : TopCat.{0}) (n : ℕ)
    (c : Cocycle ℚ (TopCat.toSSet.obj X) n) (w : (SingularChainComplex ℚ X).cycles n) :
    cohomologyEquivDualHomology ℚ X n (Singular.cohomologyClass X n c)
        ((SingularChainComplex ℚ X).homologyπ n w) =
      c.1 ((SingularChainComplex ℚ X).iCycles n w) := by
  let S := (SingularChainComplex ℚ X).sc n
  let v := S.moduleCatCyclesIso.hom w
  have hv : S.moduleCatHomologyClass v = (SingularChainComplex ℚ X).homologyπ n w := by
    have h := ConcreteCategory.congr_hom (S.moduleCatCyclesIso_inv_π) v
    change (SingularChainComplex ℚ X).homologyπ n (S.moduleCatCyclesIso.inv v) =
      S.moduleCatHomologyClass v at h
    have hvw : S.moduleCatCyclesIso.inv v = w := S.moduleCatCyclesIso.hom_inv_id_apply w
    rw [hvw] at h
    exact h.symm
  have he := cohomologyEquivDualHomology_cohomologyClass X n c v
  rw [hv] at he
  have hi := ConcreteCategory.congr_hom (S.moduleCatCyclesIso_hom_i) w
  change v.1 = (SingularChainComplex ℚ X).iCycles n w at hi
  exact he.trans (congrArg c.1 hi)

set_option backward.isDefEq.respectTransparency false in
theorem cq_circleCohomologyPrism_class_pairing (X : TopCat.{0}) (n : ℕ)
    (c : Cocycle ℚ (TopCat.toSSet.obj (TopCat.of (X × UnitAddCircle))) (n + 1))
    (w : (SingularChainComplex ℚ X).cycles n) :
    cohomologyEquivDualHomology ℚ X n
        (cq_circleCohomologyPrism X n
          (Singular.cohomologyClass (TopCat.of (X × UnitAddCircle)) (n + 1) c))
        ((SingularChainComplex ℚ X).homologyπ n w) =
      c.1 ((cq_circleChainHomotopy X).hom n (n + 1)
        ((SingularChainComplex ℚ X).iCycles n w)) := by
  have hp := cq_circleCohomologyPrism_pairing X n
    (Singular.cohomologyClass (TopCat.of (X × UnitAddCircle)) (n + 1) c)
    ((SingularChainComplex ℚ X).homologyπ n w)
  have hh := ConcreteCategory.congr_hom
    (cq_selfHomotopy_homologyMap_π (cq_circleChainHomotopy X) n) w
  have he := cq_cohomologyClass_pairing_homologyπ
    (TopCat.of (X × UnitAddCircle)) (n + 1) c
    (cq_selfHomotopy_cycleMap (cq_circleChainHomotopy X) n w)
  have hi := ConcreteCategory.congr_hom
    (cq_selfHomotopy_cycleMap_i (cq_circleChainHomotopy X) n) w
  exact hp.trans ((congrArg
    (cohomologyEquivDualHomology ℚ (TopCat.of (X × UnitAddCircle)) (n + 1)
      (Singular.cohomologyClass (TopCat.of (X × UnitAddCircle)) (n + 1) c)) hh).trans
        (he.trans (congrArg c.1 hi)))

set_option backward.isDefEq.respectTransparency false in
theorem cq_circleCohomologyPrism_pullback (X : TopCat.{0}) (n : ℕ)
    (a : Cohomology ℚ X (n + 1)) :
    cq_circleCohomologyPrism X n
      (cohomologyMap ℚ (n + 1) (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ :
        TopCat.of (X × UnitAddCircle) ⟶ X) a) = 0 := by
  obtain ⟨c, rfl⟩ := Singular.cohomologyClass_surjective X (n + 1) a
  let d := cq_normalizedCocycle X (n + 1) c
  have hd : Singular.cohomologyClass X (n + 1) d = Singular.cohomologyClass X (n + 1) c :=
    cq_normalizedCocycle_class X (n + 1) c
  rw [← hd]
  let f : TopCat.of (X × UnitAddCircle) ⟶ X := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  let b := cq_chainCocycleMap (singularChainComplexMap ℚ f) (n + 1) d
  have hb : cohomologyMap ℚ (n + 1) f (Singular.cohomologyClass X (n + 1) d) =
      Singular.cohomologyClass (TopCat.of (X × UnitAddCircle)) (n + 1) b :=
    Singular.cohomologyMap_class X f (n + 1) d b rfl
  rw [hb]
  apply (cohomologyEquivDualHomology ℚ X n).injective
  ext z
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((SingularChainComplex ℚ X).homologyπ n)).mp inferInstance z
  rw [cq_circleCohomologyPrism_class_pairing]
  have hz := LinearMap.congr_fun (cq_circlePrism_normalized_pullback X n c)
    ((SingularChainComplex ℚ X).iCycles n w)
  exact hz.trans (by simp)

end HodgeLean.Foundations.Program
