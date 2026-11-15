import HodgeLean.Foundations.Program.CompensationAssemblyCocycleCup

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
theorem cq_circlePrism_cup_class (X : TopCat.{0}) (n : ℕ) (a : Cohomology ℚ X n)
    (c : Cocycle ℚ (TopCat.toSSet.obj (TopCat.of UnitAddCircle)) 1) :
    cq_circleCohomologyPrism X n
        (Singular.cup (TopCat.of (X × UnitAddCircle)) rfl
          (cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a)
          (cohomologyMap ℚ 1 (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩)
            (Singular.cohomologyClass (TopCat.of UnitAddCircle) 1 c))) =
      -((-1 : ℤ) ^ n •
        ((cq_normalizedCocycle (TopCat.of UnitAddCircle) 1 c).1
          (chainOfSimplex ℚ (loopSimplex (ContinuousMap.id UnitAddCircle))) • a)) := by
  obtain ⟨d, rfl⟩ := Singular.cohomologyClass_surjective X n a
  let f : TopCat.of (X × UnitAddCircle) ⟶ X := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
  let g : TopCat.of (X × UnitAddCircle) ⟶ TopCat.of UnitAddCircle :=
    TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
  let e := cq_normalizedCocycle (TopCat.of UnitAddCircle) 1 c
  let dp := cq_chainCocycleMap (singularChainComplexMap ℚ f) n d
  let ep := cq_chainCocycleMap (singularChainComplexMap ℚ g) 1 e
  have hf := Singular.cohomologyMap_class X f n d dp rfl
  have hg := Singular.cohomologyMap_class (TopCat.of UnitAddCircle) g 1 e ep rfl
  have he : Singular.cohomologyClass (TopCat.of UnitAddCircle) 1 e =
      Singular.cohomologyClass (TopCat.of UnitAddCircle) 1 c :=
    cq_normalizedCocycle_class (TopCat.of UnitAddCircle) 1 c
  rw [← he, hf, hg, cq_cupCocycle_class]
  apply (cohomologyEquivDualHomology ℚ X n).injective
  ext z
  obtain ⟨w, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((SingularChainComplex ℚ X).homologyπ n)).mp inferInstance z
  rw [cq_circleCohomologyPrism_class_pairing]
  have h := LinearMap.congr_fun (cq_circlePrism_cup_cochain X n d.1 c)
    ((SingularChainComplex ℚ X).iCycles n w)
  change (cq_cupCocycle (TopCat.of (X × UnitAddCircle)) n 1 dp ep).1
    ((cq_circleChainHomotopy X).hom n (n + 1)
      ((SingularChainComplex ℚ X).iCycles n w)) = _ at h
  have hd := cq_cohomologyClass_pairing_homologyπ X n d w
  simp only [map_neg, map_zsmul, map_smul, LinearMap.neg_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, hd]
  exact h

end HodgeLean.Foundations.Program
