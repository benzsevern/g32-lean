import HodgeLean.Foundations.QuotientDuality.ProperCycleCapTailZero

/-! # Original same-pair even caps on actual chain tails -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original even relative cocycle caps the actual relative chain tail into the original absolute chain complex.
Source: Hatcher, Algebraic Topology, section 3.3, the signed relative cap boundary formula.
HC no distance; AV milestone no distance. -/
def properCycle_even_relative_cap_chain_map
    (P : TopPair.{0}) (p : ℕ) (hp : Even p)
    (φ : RelativeCochain ℚ P p) (hφ : relativeCoboundary ℚ P p φ = 0) :
    ((relativeChainFunctor ℚ).obj P).restriction (properCycle_cap_tail_embedding p) ⟶
      SingularChainComplex ℚ P.fst where
  f q := relativeCapHom ℚ P p q φ
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    subst i
    apply ModuleCat.hom_ext
    change (AlgebraicTopology.Simplicial.boundary ℚ j).comp (relativeCap ℚ P p (j + 1) φ) =
      (relativeCap ℚ P p j φ).comp (relativeBoundary ℚ P (p + j))
    have h := boundary_relativeCap_eq_of_cocycle ℚ P p j φ hφ
    rw [hp.neg_one_pow, one_smul] at h
    exact h

/-- The actual same-pair even cap chain map induces the original relative cap in each positive output degree.
Source: Hatcher, Algebraic Topology, section 3.3, cap on homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_even_relative_cap_homology_comparison
    (P : TopPair.{0}) (p q : ℕ) (hp : Even p)
    (φ : RelativeCochain ℚ P p) (hφ : relativeCoboundary ℚ P p φ = 0) :
    (properCycle_cap_tail_homology_iso ((relativeChainFunctor ℚ).obj P) p q).hom ≫
      HomologicalComplex.homologyMap (properCycle_even_relative_cap_chain_map P p hp φ hφ) (q + 1) =
      ModuleCat.ofHom (relativeCapHomologyMap ℚ P p (q + 1) φ hφ) := by
  let E := properCycle_cap_tail_sc_iso ((relativeChainFunctor ℚ).obj P) p q
  let F := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) (q + 1)).map
    (properCycle_even_relative_cap_chain_map P p hp φ hφ)
  have h : ShortComplex.homologyMap (E.hom ≫ F) =
      ShortComplex.homologyMap (relativeCapShortComplexHom ℚ P p (q + 1) φ hφ) := by
    apply AlgebraicTopology.Simplicial.homologyMap_eq_of_τ₂_eq
    change E.hom.τ₂ ≫ relativeCapHom ℚ P p (q + 1) φ = _
    rw [relativeCapShortComplexHom_τ₂]
    have hmid : E.hom.τ₂ = 𝟙 _ := by
      apply ModuleCat.hom_ext
      ext z
      rfl
    rw [hmid, Category.id_comp]
  rw [ShortComplex.homologyMap_comp] at h
  exact h

/-- The actual same-pair even cap chain map induces the original relative cap at output degree zero.
Source: Hatcher, Algebraic Topology, section 3.3, the relative cap endpoint.
HC no distance; AV milestone no distance. -/
lemma properCycle_even_relative_cap_zero_homology_comparison
    (P : TopPair.{0}) (p : ℕ) (hp : Even p)
    (φ : RelativeCochain ℚ P p) (hφ : relativeCoboundary ℚ P p φ = 0) :
    properCycle_cap_tail_zero_homology_map ((relativeChainFunctor ℚ).obj P) p ≫
      HomologicalComplex.homologyMap (properCycle_even_relative_cap_chain_map P p hp φ hφ) 0 =
      ModuleCat.ofHom (relativeCapHomologyMap ℚ P p 0 φ hφ) := by
  let E := properCycle_cap_tail_zero_sc_map ((relativeChainFunctor ℚ).obj P) p
  let F := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) 0).map
    (properCycle_even_relative_cap_chain_map P p hp φ hφ)
  have h : ShortComplex.homologyMap (E ≫ F) =
      ShortComplex.homologyMap (relativeCapShortComplexHom ℚ P p 0 φ hφ) := by
    apply AlgebraicTopology.Simplicial.homologyMap_eq_of_τ₂_eq
    change E.τ₂ ≫ relativeCapHom ℚ P p 0 φ = _
    rw [relativeCapShortComplexHom_τ₂]
    have hmid : E.τ₂ = 𝟙 _ := by
      apply ModuleCat.hom_ext
      ext z
      rfl
    rw [hmid, Category.id_comp]
  rw [ShortComplex.homologyMap_comp] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
