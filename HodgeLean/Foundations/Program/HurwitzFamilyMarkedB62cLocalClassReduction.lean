import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRelativeReduction
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.FundamentalClass

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
variable (R : Type) [CommRing R]

def b6m_localImageChain (P : TopPair.{0}) (F : puncturedPair ℝ 2 ⟶ P) :
    (SingularChainComplex R P.fst).X 2 :=
  ((((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
    (TopPair.Hom.fst F)).f 2).hom ((standardAmbientSimplexChain R 2).hom 1)

def b6m_localImageCycle (P : TopPair.{0}) (F : puncturedPair ℝ 2 ⟶ P) :
    ((relativeChainFunctor R).obj P).cycles 2 :=
  (HomologicalComplex.cyclesMap ((relativeChainFunctor R).map F) 2).hom
    ((standardLocalCycle R 2).hom 1)

set_option backward.isDefEq.respectTransparency false in
theorem b6m_localImageCycle_inclusion (P : TopPair.{0}) (F : puncturedPair ℝ 2 ⟶ P) :
    (((relativeChainFunctor R).obj P).iCycles 2).hom (b6m_localImageCycle R P F) =
      ((relativeChainProjection R P).f 2).hom (b6m_localImageChain R P F) := by
  have hnat := congrArg (fun f => f.f 2)
    (TopPair.Homotopy.relativeChainProjection_naturality (R := R) F)
  have heq : standardLocalCycle R 2 ≫
      HomologicalComplex.cyclesMap ((relativeChainFunctor R).map F) 2 ≫
        ((relativeChainFunctor R).obj P).iCycles 2 =
      standardAmbientSimplexChain R 2 ≫
        (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
          (TopPair.Hom.fst F)).f 2 ≫ (relativeChainProjection R P).f 2 := by
    rw [HomologicalComplex.cyclesMap_i, ← Category.assoc,
      standardLocalCycle_inclusion, standardLocalChain, Category.assoc]
    exact congrArg (fun f => standardAmbientSimplexChain R 2 ≫ f) hnat
  exact ConcreteCategory.congr_hom heq 1

theorem b6m_localImageCycle_class (P : TopPair.{0}) (F : puncturedPair ℝ 2 ⟶ P) :
    (((relativeChainFunctor R).obj P).homologyπ 2).hom (b6m_localImageCycle R P F) =
      relativeHomologyMap R 2 F (standardLocalClass R 2) := by
  have h := congrArg (fun f => f.hom ((standardLocalCycle R 2).hom 1))
    (HomologicalComplex.homologyπ_naturality ((relativeChainFunctor R).map F) 2)
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem b6m_localImageChain_reduction (P : TopPair.{0}) (F : puncturedPair ℝ 2 ⟶ P)
    (n : ℕ) :
    b6m_singularReduction P.fst n 2 (b6m_localImageChain ℤ P F) =
      b6m_localImageChain (ZMod n) P F := by
  unfold b6m_localImageChain
  rw [b6m_singularReduction_map]
  have h := b6m_singularReduction_iota (puncturedPair ℝ 2).fst n 2
    (standardSingularSimplex 2) 1
  simp only [Int.cast_one] at h
  change b6m_singularReduction (puncturedPair ℝ 2).fst n 2
    ((standardAmbientSimplexChain ℤ 2).hom 1) =
      (standardAmbientSimplexChain (ZMod n) 2).hom 1 at h
  rw [h]

set_option backward.isDefEq.respectTransparency false in
theorem b6m_localImageClass_reduction (P : TopPair.{0}) (F : puncturedPair ℝ 2 ⟶ P)
    (n : ℕ) (c : (SingularChainComplex ℤ P.fst).cycles 2)
    (d : (SingularChainComplex (ZMod n) P.fst).cycles 2)
    (hrep : ((SingularChainComplex (ZMod n) P.fst).iCycles 2).hom d =
      b6m_singularReduction P.fst n 2 (((SingularChainComplex ℤ P.fst).iCycles 2).hom c))
    (hclass : (relativeHomologyProjection ℤ P 2).hom
      (((SingularChainComplex ℤ P.fst).homologyπ 2).hom c) =
        relativeHomologyMap ℤ 2 F (standardLocalClass ℤ 2)) :
    (relativeHomologyProjection (ZMod n) P 2).hom
      (((SingularChainComplex (ZMod n) P.fst).homologyπ 2).hom d) =
        relativeHomologyMap (ZMod n) 2 F (standardLocalClass (ZMod n) 2) := by
  let π := relativeChainProjection ℤ P
  let π' := relativeChainProjection (ZMod n) P
  have heq :
      (((relativeChainFunctor (ZMod n)).obj P).homologyπ 2).hom
        ((HomologicalComplex.cyclesMap π' 2).hom d) =
      (((relativeChainFunctor (ZMod n)).obj P).homologyπ 2).hom
        (b6m_localImageCycle (ZMod n) P F) := by
    apply b6m_relative_reduction_preserves_eq P n 2
      ((HomologicalComplex.cyclesMap π 2).hom c) (b6m_localImageCycle ℤ P F)
      ((HomologicalComplex.cyclesMap π' 2).hom d) (b6m_localImageCycle (ZMod n) P F)
      (((SingularChainComplex ℤ P.fst).iCycles 2).hom c) (b6m_localImageChain ℤ P F)
    · exact (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i π 2) c).symm
    · exact (b6m_localImageCycle_inclusion ℤ P F).symm
    · rw [← hrep]
      exact (ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i π' 2) d).symm
    · rw [b6m_localImageChain_reduction]
      exact (b6m_localImageCycle_inclusion (ZMod n) P F).symm
    · exact (b6m_homologyπ_cyclesMap ℤ π 2 c).trans
        (hclass.trans (b6m_localImageCycle_class ℤ P F).symm)
  exact (b6m_homologyπ_cyclesMap (ZMod n) π' 2 d).symm.trans
    (heq.trans (b6m_localImageCycle_class (ZMod n) P F))

end HodgeLean.Foundations.Program
