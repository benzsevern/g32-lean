import HodgeLean.Adapters.CycleClassDivisorProduct

/-! # The quotient by complement-small chains

Ambient chains modulo complement-small chains retain chains meeting the support.
The two complements cover their union, not generally the ambient space.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.Singular
namespace HodgeLean.Adapters

/-- The small-chain inclusion for the two complements.
Source: Hatcher, Algebraic Topology, §2.1, subdivision and excision. -/
abbrev ccm14_smallInclusion (Y : TopCat.{0}) (S T : Set Y) :=
  coverSmallRationalSingularChainInclusion Y (ccm13_complementFamily Y S T)

/-- Ambient chains modulo chains lying in either complement.
Equivalently use the ambient cover containing Y itself before taking the quotient.
Source: Hatcher, Algebraic Topology, §3.2, relative cup products. -/
def ccm14_smallRelativeComplex (Y : TopCat.{0}) (S T : Set Y) :
    ChainComplex (ModuleCat ℚ) ℕ := cokernel (ccm14_smallInclusion Y S T)

/-- The quotient projection as a chain map.
Source: Hatcher, Algebraic Topology, §2.1, relative chains. -/
def ccm14_smallProjection (Y : TopCat.{0}) (S T : Set Y) :
    (TopCat.toSSet.obj Y).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      ccm14_smallRelativeComplex Y S T := cokernel.π _

/-- Cochains on the actual quotient complex.
Source: Spanier, Algebraic Topology, chapter 5, relative cochains. -/
abbrev ccm14_smallRelativeCochain (Y : TopCat.{0}) (S T : Set Y) (n : ℕ) :=
  Module.Dual ℚ ((ccm14_smallRelativeComplex Y S T).X n)

/-- Degreewise universal property of the quotient projection.
Source: the cokernel universal property and exact evaluation of chain complexes. -/
def ccm14_projectionIsCokernel (Y : TopCat.{0}) (S T : Set Y) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ
      (f := (ccm14_smallInclusion Y S T).f n)
      ((ccm14_smallProjection Y S T).f n) (by
        exact congrArg (fun f => f.f n) (cokernel.condition (ccm14_smallInclusion Y S T)))) :=
  CokernelCofork.mapIsColimit _ (cokernelIsCokernel (ccm14_smallInclusion Y S T))
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) n)

/-- Descend the actual Alexander–Whitney lift through the small-chain quotient.
Source: Hatcher, Algebraic Topology, §3.2, relative cup construction. -/
def ccm14_smallRelativeCup (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ)
    (u : RelativeCochain ℚ (TopPair.ofSubset Sᶜ) p)
    (v : RelativeCochain ℚ (TopPair.ofSubset Tᶜ) q) :
    ccm14_smallRelativeCochain Y S T (p + q) :=
  ((ccm14_projectionIsCokernel Y S T (p + q)).desc
    (CokernelCofork.ofπ (ModuleCat.ofHom (ccm13_relativeCupLift Y S T p q u v)) (by
      apply ModuleCat.hom_ext
      exact ccm13_relativeCupLift_small_zero Y S T p q u v))).hom

/-- Source: the zero functional on a concrete quotient. -/
example : (0 : ccm14_smallRelativeCochain (TopCat.of PUnit) Set.univ ∅ 2) 0 = 0 := rfl

/-- Source: the defining factorization of the descended Alexander–Whitney functional. -/
example (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ)
    (u : RelativeCochain ℚ (TopPair.ofSubset Sᶜ) p)
    (v : RelativeCochain ℚ (TopPair.ofSubset Tᶜ) q) :
    (ccm14_smallRelativeCup Y S T p q u v).comp
      ((ccm14_smallProjection Y S T).f (p + q)).hom =
        ccm13_relativeCupLift Y S T p q u v := by
  exact congrArg ModuleCat.Hom.hom
    ((Cofork.IsColimit.π_desc (ccm14_projectionIsCokernel Y S T (p + q))).trans
      (CokernelCofork.π_ofπ _ _ _))

/-- The complement-small simplicial set maps to the singular set of the union.
Source: Hatcher, Algebraic Topology, §2.1, small chains for excision. -/
def ccm14_smallToUnion (Y : TopCat.{0}) (S T : Set Y) :
    (coverSmallSingularSubcomplex Y (ccm13_complementFamily Y S T) : SSet) ⟶
      TopCat.toSSet.obj (TopCat.of ↥((S ∩ T)ᶜ)) := by
  let f := TopCat.toSSet.map (topologicalSubsetInclusion Y (S ∩ T)ᶜ)
  have hf : Mono f := by
    have : Mono (topologicalSubsetInclusion Y (S ∩ T)ᶜ) :=
      (TopCat.mono_iff_injective _).mpr Subtype.val_injective
    dsimp [f]
    infer_instance
  let h : SSet.Subcomplex.range
      (coverSmallSingularSubcomplex Y (ccm13_complementFamily Y S T)).ι ≤
        SSet.Subcomplex.range f := by
    intro n σ hσ
    obtain ⟨σ, rfl⟩ := hσ
    have hσ := σ.2
    change σ.1 ∈ _
    generalize hval : σ.1 = τ₀ at *
    obtain ⟨b, τ, rfl⟩ :=
      (mem_coverSmallSingularSubcomplex_iff_exists_preimage Y
        (ccm13_complementFamily Y S T) τ₀).mp hσ
    have hb : ccm13_complementFamily Y S T b ⊆ (S ∩ T)ᶜ := by
      cases b <;> simp only [ccm13_complementFamily, Bool.false_eq_true, ↓reduceIte]
      · exact fun x hx h => hx h.1
      · exact fun x hx h => hx h.2
    let j : TopCat.of (ccm13_complementFamily Y S T b) ⟶ TopCat.of ↥((S ∩ T)ᶜ) :=
      TopCat.ofHom ⟨fun x => ⟨x.1, hb x.2⟩,
        Continuous.subtype_mk continuous_subtype_val _⟩
    exact ⟨(TopCat.toSSet.map j).app n τ, rfl⟩
  exact SSet.Subcomplex.lift _ h ≫ inv (SSet.Subcomplex.toRange f)

/-- Source: the factorization through the union subspace. -/
theorem ccm14_smallToUnion_comp (Y : TopCat.{0}) (S T : Set Y) :
    ccm14_smallToUnion Y S T ≫
      TopCat.toSSet.map (topologicalSubsetInclusion Y (S ∩ T)ᶜ) =
        (coverSmallSingularSubcomplex Y (ccm13_complementFamily Y S T)).ι := by
  unfold ccm14_smallToUnion
  dsimp only
  conv_lhs => rhs; rw [← SSet.Subcomplex.toRange_ι
    (TopCat.toSSet.map (topologicalSubsetInclusion Y (S ∩ T)ᶜ))]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, SSet.Subcomplex.lift_ι]

/-- The canonical map from the small relative quotient to genuine relative chains.
Source: Hatcher, Algebraic Topology, §2.1, excision comparison. -/
def ccm14_relativeComparison (Y : TopCat.{0}) (S T : Set Y) :
    ccm14_smallRelativeComplex Y S T ⟶
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset (S ∩ T)ᶜ) :=
  cokernel.desc _ (relativeChainProjection ℚ (TopPair.ofSubset (S ∩ T)ᶜ)) (by
    have h : ccm14_smallInclusion Y S T =
        SSet.chainComplexMap (ccm14_smallToUnion Y S T) (ModuleCat.of ℚ ℚ) ≫
          ((chainPairFunctor ℚ).obj (TopPair.ofSubset (S ∩ T)ᶜ)).hom := by
      change SSet.chainComplexMap _ _ = SSet.chainComplexMap _ _ ≫
        SSet.chainComplexMap _ _
      simp only [SSet.chainComplexMap, ← Functor.map_comp]
      exact congrArg (fun f :
        (coverSmallSingularSubcomplex Y (ccm13_complementFamily Y S T) : SSet) ⟶
          TopCat.toSSet.obj Y => SSet.chainComplexMap f (ModuleCat.of ℚ ℚ))
        (ccm14_smallToUnion_comp Y S T).symm
    rw [h, Category.assoc, subspaceChainMap_relativeChainProjection, comp_zero])

/-- Source: the cokernel factorization defining the comparison. -/
example (Y : TopCat.{0}) (S T : Set Y) :
    ccm14_smallProjection Y S T ≫ ccm14_relativeComparison Y S T =
      relativeChainProjection ℚ (TopPair.ofSubset (S ∩ T)ᶜ) := cokernel.π_desc _ _ _

end HodgeLean.Adapters
