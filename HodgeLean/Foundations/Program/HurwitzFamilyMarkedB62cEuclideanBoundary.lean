import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.Euclidean
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cLocalLifting

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open scoped _root_.Simplicial
variable (R : Type) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSubspaceBoundaryChain (n : ℕ) :
    ModuleCat.of R R ⟶
      ((chainPairFunctor R).obj (puncturedPair ℝ (n + 1))).left.X n :=
  ∑ i : Fin (n + 2), (-1) ^ i.val • standardSubspaceFaceChain R n i

set_option backward.isDefEq.respectTransparency false in
def b6m_relativeSingularBoundary (X : TopPair) (n : ℕ) :
    RelativeHomology R X (n + 1) ⟶ Homology R X.snd n :=
  (relativeChainShortComplex_shortExact R X).δ (n + 1) n
    (ComplexShape.down_mk (n + 1) n (by lia))

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSubspaceBoundaryChain_inclusion (n : ℕ) :
    b6m_standardSubspaceBoundaryChain R n ≫
      ((chainPairFunctor R).obj (puncturedPair ℝ (n + 1))).hom.f n =
    standardAmbientSimplexChain R (n + 1) ≫
      ((chainPairFunctor R).obj
        (puncturedPair ℝ (n + 1))).right.d (n + 1) n := by
  rw [b6m_standardSubspaceBoundaryChain, Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, standardFaceChain_inclusion]
  exact (standardAmbientSimplexChain_boundary R n).symm

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSubspaceBoundaryChain_boundary (n : ℕ) :
    b6m_standardSubspaceBoundaryChain R n ≫
      ((chainPairFunctor R).obj (puncturedPair ℝ (n + 1))).left.d n
        ((ComplexShape.down ℕ).next n) = 0 := by
  let f := ((chainPairFunctor R).obj (puncturedPair ℝ (n + 1))).hom
  let : Mono f := relativeChainMap_mono R (puncturedPair ℝ (n + 1))
  rw [← cancel_mono (f.f ((ComplexShape.down ℕ).next n)), Category.assoc, ← f.comm,
    ← Category.assoc, b6m_standardSubspaceBoundaryChain_inclusion R, Category.assoc,
    HomologicalComplex.d_comp_d, comp_zero]
  simp

set_option backward.isDefEq.respectTransparency false in
def b6m_standardPuncturedBoundaryCycle (n : ℕ) :
    ModuleCat.of R R ⟶
      ((chainPairFunctor R).obj (puncturedPair ℝ (n + 1))).left.cycles n :=
  ((chainPairFunctor R).obj (puncturedPair ℝ (n + 1))).left.liftCycles
    (b6m_standardSubspaceBoundaryChain R n) ((ComplexShape.down ℕ).next n) rfl
    (b6m_standardSubspaceBoundaryChain_boundary R n)

set_option backward.isDefEq.respectTransparency false in
def b6m_standardPuncturedBoundaryClass (n : ℕ) :
    Homology R (puncturedPair ℝ (n + 1)).snd n :=
  ((b6m_standardPuncturedBoundaryCycle R n ≫
    ((chainPairFunctor R).obj
      (puncturedPair ℝ (n + 1))).left.homologyπ n).hom) 1

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardLocalCycle_comp_relativeSingularBoundary (n : ℕ) :
    standardLocalCycle R (n + 1) ≫
        (standardLocalRelativeChainComplex R (n + 1)).homologyπ (n + 1) ≫
        b6m_relativeSingularBoundary R (puncturedPair ℝ (n + 1)) n =
      b6m_standardPuncturedBoundaryCycle R n ≫
        ((chainPairFunctor R).obj
          (puncturedPair ℝ (n + 1))).left.homologyπ n := by
  let hS := relativeChainShortComplex_shortExact R
    (puncturedPair ℝ (n + 1))
  exact hS.δ_eq (n + 1) n (ComplexShape.down_mk (n + 1) n (by lia))
    (standardLocalChain R (n + 1)) (standardLocalChain_boundary_succ R n)
    (standardAmbientSimplexChain R (n + 1)) rfl
    (b6m_standardSubspaceBoundaryChain R n) (b6m_standardSubspaceBoundaryChain_inclusion R n)
    ((ComplexShape.down ℕ).next n) rfl

set_option backward.isDefEq.respectTransparency false in
lemma b6m_relativeSingularBoundary_standardLocalClass (n : ℕ) :
    (b6m_relativeSingularBoundary R (puncturedPair ℝ (n + 1)) n).hom
        (standardLocalClass R (n + 1)) =
      b6m_standardPuncturedBoundaryClass R n :=
  ConcreteCategory.congr_hom (b6m_standardLocalCycle_comp_relativeSingularBoundary R n) 1

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardRealModel_homology_isZero (d k : ℕ) (hk : k ≠ 0) :
    IsZero (Homology R (TopCat.of (Fin d → ℝ)) k) :=
  b6m_contractible_homology_isZero R (Fin d → ℝ) k hk

set_option backward.isDefEq.respectTransparency false in
def b6m_standardPuncturedRelativeBoundaryIso (n : ℕ) (hn : n ≠ 0) :
    RelativeHomology R (puncturedPair ℝ (n + 1)) (n + 1) ≅
      Homology R (puncturedPair ℝ (n + 1)).snd n :=
  (relativeChainShortComplex_shortExact R (puncturedPair ℝ (n + 1))).δIso
    (n + 1) n (ComplexShape.down_mk (n + 1) n (by lia))
    (b6m_standardRealModel_homology_isZero R (n + 1) (n + 1) (by lia))
    (b6m_standardRealModel_homology_isZero R (n + 1) n hn)

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardPuncturedRelativeBoundaryIso_hom (n : ℕ) (hn : n ≠ 0) :
    (b6m_standardPuncturedRelativeBoundaryIso R n hn).hom =
      b6m_relativeSingularBoundary R (puncturedPair ℝ (n + 1)) n := rfl

set_option backward.isDefEq.respectTransparency false in
lemma b6m_span_standardLocalClass_succ_eq_top_iff (n : ℕ) (hn : n ≠ 0) :
    Submodule.span R {standardLocalClass R (n + 1)} = ⊤ ↔
      Submodule.span R {b6m_standardPuncturedBoundaryClass R n} = ⊤ := by
  let e := (b6m_standardPuncturedRelativeBoundaryIso R n hn).toLinearEquiv
  have he : e (standardLocalClass R (n + 1)) = b6m_standardPuncturedBoundaryClass R n := by
    change (b6m_standardPuncturedRelativeBoundaryIso R n hn).hom.hom
      (standardLocalClass R (n + 1)) = _
    rw [b6m_standardPuncturedRelativeBoundaryIso_hom R,
      b6m_relativeSingularBoundary_standardLocalClass R]
  have hmap :
      (Submodule.span R {standardLocalClass R (n + 1)}).map e.toLinearMap =
        Submodule.span R {b6m_standardPuncturedBoundaryClass R n} := by
    rw [Submodule.map_span]
    simp [he]
  have etop : (⊤ : Submodule R _).map e.toLinearMap = ⊤ := by
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  constructor
  · intro h
    rw [← hmap, h, etop]
  · intro h
    apply Submodule.map_injective_of_injective e.injective
    rw [hmap, h, etop]

end HodgeLean.Foundations.Program
