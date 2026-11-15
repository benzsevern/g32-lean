import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cEuclideanBoundary
import Mathlib.Algebra.Homology.HomologySequenceLemmas

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The relative singular boundary commutes with maps of topological pairs. -/
theorem s2v_l1b_action_boundary_naturality
    (R : Type) [CommRing R] {X Y : TopPair} (f : X ⟶ Y) (n : ℕ)
    (a : RelativeHomology R X (n + 1)) :
    (b6m_relativeSingularBoundary R Y n).hom (relativeHomologyMap R (n + 1) f a) =
      homologyMap R n f.left ((b6m_relativeSingularBoundary R X n).hom a) := by
  let φ : relativeChainShortComplex R X ⟶ relativeChainShortComplex R Y :=
    { τ₁ := ((chainPairFunctor R).map f).left
      τ₂ := ((chainPairFunctor R).map f).right
      τ₃ := (relativeChainFunctor R).map f
      comm₁₂ := ((chainPairFunctor R).map f).w
      comm₂₃ := ((coker.π (C := ChainCategory R)).naturality
        ((chainPairFunctor R).map f)) }
  exact (ConcreteCategory.congr_hom
    (HomologicalComplex.HomologySequence.δ_naturality φ
      (relativeChainShortComplex_shortExact R X)
      (relativeChainShortComplex_shortExact R Y)
      (n + 1) n (ComplexShape.down_mk (n + 1) n (by omega))) a).symm

/-- For a contractible ambient space, the degree-two relative boundary is
an isomorphism onto degree-one homology of the subspace. -/
def s2v_l1b_action_contractible_boundary_iso
    (R : Type) [CommRing R] (X : TopPair) [ContractibleSpace X.fst] :
    RelativeHomology R X 2 ≅ Homology R X.snd 1 :=
  (relativeChainShortComplex_shortExact R X).δIso 2 1
    (ComplexShape.down_mk 2 1 (by omega))
    (b6m_contractible_homology_isZero R X.fst 2 (by omega))
    (b6m_contractible_homology_isZero R X.fst 1 (by omega))

/-- In a contractible target neighbourhood, the local degree equality is
equivalent to its image under the punctured-neighbourhood boundary. -/
theorem s2v_l1b_action_boundary_sign_iff
    (R : Type) [CommRing R] {X Y : TopPair} [ContractibleSpace Y.fst]
    (f : X ⟶ Y) (a : RelativeHomology R X 2) (b : RelativeHomology R Y 2)
    (ε : ℤ) :
    relativeHomologyMap R 2 f a = ε • b ↔
      homologyMap R 1 f.left ((b6m_relativeSingularBoundary R X 1).hom a) =
        ε • (b6m_relativeSingularBoundary R Y 1).hom b := by
  have hinj := (s2v_l1b_action_contractible_boundary_iso R Y).toLinearEquiv.injective
  change Function.Injective (b6m_relativeSingularBoundary R Y 1).hom at hinj
  rw [← hinj.eq_iff, map_zsmul,
    s2v_l1b_action_boundary_naturality]

/-- In contractible ambient spaces, a relative degree-two isomorphism induces
an isomorphism on degree-one subspace homology through the boundary maps. -/
theorem s2v_l1b_action_boundary_homology_bijective
    (R : Type) [CommRing R] {X Y : TopPair}
    [ContractibleSpace X.fst] [ContractibleSpace Y.fst]
    (f : X ⟶ Y) (hf : Function.Bijective (relativeHomologyMap R 2 f)) :
    Function.Bijective (homologyMap R 1 f.left) := by
  let eX := (s2v_l1b_action_contractible_boundary_iso R X).toLinearEquiv
  let eY := (s2v_l1b_action_contractible_boundary_iso R Y).toLinearEquiv
  have h := eY.bijective.comp (hf.comp eX.symm.bijective)
  have heq : (homologyMap R 1 f.left : Homology R X.snd 1 → Homology R Y.snd 1) =
      fun a => eY (relativeHomologyMap R 2 f (eX.symm a)) := by
    funext a
    have hn := s2v_l1b_action_boundary_naturality R f 1 (eX.symm a)
    change eY (relativeHomologyMap R 2 f (eX.symm a)) = homologyMap R 1 f.left
      (eX (eX.symm a)) at hn
    rw [eX.apply_symm_apply] at hn
    exact hn.symm
  rw [heq]
  exact h

end HodgeLean.Foundations.Program
