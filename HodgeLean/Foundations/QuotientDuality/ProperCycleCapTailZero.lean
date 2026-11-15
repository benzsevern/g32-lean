import HodgeLean.Foundations.QuotientDuality.ProperCycleEvenCapHomology

/-! # The actual cap degree at the endpoint of a chain tail -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Original cycles in the first retained degree map to the actual endpoint of the degree tail.
Source: Mathlib, Algebra/Homology/ShortComplex/HomologicalComplex.lean, three-term chain models.
HC no distance; AV milestone no distance. -/
def properCycle_cap_tail_zero_sc_map
    (K : ChainComplex (ModuleCat ℚ) ℕ) (p : ℕ) :
    K.sc p ⟶ (K.restriction (properCycle_cap_tail_embedding p)).sc 0 := by
  let L := K.restriction (properCycle_cap_tail_embedding p)
  let e := K.isoSc' (p + 1) p ((ComplexShape.down ℕ).next p)
    (by rw [ChainComplex.prev]) rfl
  let e' := L.isoSc' 1 0 0 (by simp [ChainComplex.prev]) (by simp)
  let f : K.sc' (p + 1) p ((ComplexShape.down ℕ).next p) ⟶ L.sc' 1 0 0 :=
    ShortComplex.homMk (𝟙 _) (𝟙 _) 0 (by
      simp only [Category.id_comp, Category.comp_id]
      rfl) (by
      rw [comp_zero, Category.id_comp]
      exact (K.shape p p (by simp)))
  exact e.hom ≫ f ≫ e'.inv

/-- Original homology in the first retained degree maps to homology at the actual tail endpoint.
Source: Hatcher, Algebraic Topology, section 2.1, cycles and boundaries.
HC no distance; AV milestone no distance. -/
def properCycle_cap_tail_zero_homology_map
    (K : ChainComplex (ModuleCat ℚ) ℕ) (p : ℕ) :
    K.homology p ⟶ (K.restriction (properCycle_cap_tail_embedding p)).homology 0 :=
  ShortComplex.homologyMap (properCycle_cap_tail_zero_sc_map K p)

/-- Passing to the actual tail endpoint preserves every original homology class injectively.
Source: Hatcher, Algebraic Topology, section 2.1, identical boundaries under degree truncation.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_tail_zero_homology_injective
    (K : ChainComplex (ModuleCat ℚ) ℕ) (p : ℕ) :
    Function.Injective (properCycle_cap_tail_zero_homology_map K p).hom := by
  let E := properCycle_cap_tail_zero_sc_map K p
  have h1 : IsIso E.τ₁ := by
    dsimp [E, properCycle_cap_tail_zero_sc_map]
    infer_instance
  have h2 : IsIso E.τ₂ := by
    dsimp [E, properCycle_cap_tail_zero_sc_map]
    infer_instance
  letI := h1
  letI := h2
  have hm : Mono (ShortComplex.homologyMap E) := inferInstance
  exact (ModuleCat.mono_iff_injective _).mp hm

/-- The original endpoint comparison commutes with every actual chain map.
Source: Mathlib, Algebra/Homology/ShortComplex/HomologicalComplex.lean, natural three-term models.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_tail_zero_sc_naturality
    {K L : ChainComplex (ModuleCat ℚ) ℕ} (f : K ⟶ L) (p : ℕ) :
    (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) p).map f ≫
        properCycle_cap_tail_zero_sc_map L p =
      properCycle_cap_tail_zero_sc_map K p ≫
        (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) 0).map
          (HomologicalComplex.restrictionMap f (properCycle_cap_tail_embedding p)) := by
  apply ShortComplex.hom_ext
  · dsimp [properCycle_cap_tail_zero_sc_map, HomologicalComplex.isoSc',
      HomologicalComplex.natIsoSc']
    simp only [Category.comp_id, Category.id_comp]
    rw [HomologicalComplex.XIsoOfEq_hom_naturality_assoc f
      (show (ComplexShape.down ℕ).prev p = p + 1 by rw [ChainComplex.prev])]
    rw [Category.assoc]
    congr 1
    exact HomologicalComplex.XIsoOfEq_inv_naturality
      (HomologicalComplex.restrictionMap f (properCycle_cap_tail_embedding p))
      (show (ComplexShape.down ℕ).prev 0 = 1 by simp [ChainComplex.prev])

  · apply ModuleCat.hom_ext
    ext z
    rfl
  · simp [properCycle_cap_tail_zero_sc_map, HomologicalComplex.isoSc',
      HomologicalComplex.natIsoSc']

/-- The injective original homology comparison at the endpoint is natural for actual chain maps.
Source: Hatcher, Algebraic Topology, section 2.1, functoriality of homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_cap_tail_zero_homology_naturality
    {K L : ChainComplex (ModuleCat ℚ) ℕ} (f : K ⟶ L) (p : ℕ) :
    HomologicalComplex.homologyMap f p ≫ properCycle_cap_tail_zero_homology_map L p =
      properCycle_cap_tail_zero_homology_map K p ≫
        HomologicalComplex.homologyMap
          (HomologicalComplex.restrictionMap f (properCycle_cap_tail_embedding p)) 0 := by
  change ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _ =
    ShortComplex.homologyMap _ ≫ ShortComplex.homologyMap _
  rw [← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp]
  exact congrArg (fun g => ShortComplex.homologyMap g) (properCycle_cap_tail_zero_sc_naturality f p)

/-- The actual even cap chain map retains the original triad cap at tail degree zero.
Source: Hatcher, Algebraic Topology, section 3.3, relative cap on homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_even_triad_cap_zero_homology_comparison
    (X : TopCat.{0}) (A B : Set X) (p : ℕ) (hp : Even p)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := X) A) p)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := X) A) p φ = 0) :
    properCycle_cap_tail_zero_homology_map (triadRelativeChainComplex ℚ X A B) p ≫
      HomologicalComplex.homologyMap (properCycle_even_triad_cap_chain_map X A B p hp φ hφ) 0 =
      ModuleCat.ofHom (triadCapHomologyMap ℚ X A B p 0 φ hφ) := by
  let E := properCycle_cap_tail_zero_sc_map (triadRelativeChainComplex ℚ X A B) p
  let F := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) 0).map
    (properCycle_even_triad_cap_chain_map X A B p hp φ hφ)
  have h : ShortComplex.homologyMap (E ≫ F) =
      ShortComplex.homologyMap (triadCapShortComplexHom ℚ X A B p 0 φ hφ) := by
    apply AlgebraicTopology.Simplicial.homologyMap_eq_of_τ₂_eq
    change E.τ₂ ≫ triadCapHom ℚ X A B p 0 φ = _
    rw [triadCapShortComplexHom_τ₂]
    have hmid : E.τ₂ = 𝟙 _ := by
      apply ModuleCat.hom_ext
      ext z
      rfl
    rw [hmid, Category.id_comp]
  rw [ShortComplex.homologyMap_comp] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
