import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.ChartFundamentalClass
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cOpenLift
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSupportHomology

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular _root_.Simplicial
variable (R : Type) [CommRing R]

theorem b6m_chain_complement_neighborhood {M : Type} [TopologicalSpace M] [T2Space M]
    (A : Set M) (i : ℕ)
    (b : ((chainPairFunctor R).obj (TopPair.ofSubset (X := TopCat.of M) Aᶜ)).left.X i) :
    ∃ W : Set M, IsOpen W ∧ A ⊆ W ∧ ∀ K : Set M, K ⊆ W →
      ((((chainPairFunctor R).obj (TopPair.ofSubset (X := TopCat.of M) Aᶜ)).hom.f i).hom b) ∈
        LinearMap.range ((((chainPairFunctor R).obj
          (TopPair.ofSubset (X := TopCat.of M) Kᶜ)).hom.f i).hom) := by
  let PA := TopPair.ofSubset (X := TopCat.of M) Aᶜ
  let jA := ((chainPairFunctor R).obj PA).hom
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp
    (b6m_chain_mem_iSup_range R (TopCat.toSSet.obj (TopCat.of ↥(Aᶜ : Set M))) i b)
  let S : Set M := ⋃ σ ∈ s,
    Set.range (fun t => ((TopCat.of ↥(Aᶜ : Set M)).toSSetObjEquiv _ σ t).1)
  have hSc : IsCompact S :=
    s.isCompact_biUnion (fun σ _ => isCompact_range
      (continuous_subtype_val.comp ((TopCat.of ↥(Aᶜ : Set M)).toSSetObjEquiv _ σ).continuous))
  have hSA : ∀ y ∈ S, y ∉ A := by
    intro y hy
    simp only [S, Set.mem_iUnion, Set.mem_range] at hy
    obtain ⟨σ, _, t, rfl⟩ := hy
    exact ((TopCat.of ↥(Aᶜ : Set M)).toSSetObjEquiv _ σ t).2
  refine ⟨Sᶜ, hSc.isClosed.isOpen_compl, fun a ha hS => hSA a hS ha, fun K hKW => ?_⟩
  let PK := TopPair.ofSubset (X := TopCat.of M) Kᶜ
  let jK := ((chainPairFunctor R).obj PK).hom
  suffices h : (⨆ σ ∈ s, LinearMap.range
      ((TopCat.toSSet.obj (TopCat.of ↥(Aᶜ : Set M))).ιChainComplex
        (R := ModuleCat.of R R) σ).hom) ≤
      (LinearMap.range (jK.f i).hom).comap (jA.f i).hom from h hs
  refine iSup₂_le fun σ hσ => ?_
  rintro _ ⟨r, rfl⟩
  show (jA.f i).hom
    (((TopCat.toSSet.obj (TopCat.of ↥(Aᶜ : Set M))).ιChainComplex
      (R := ModuleCat.of R R) σ).hom r) ∈ LinearMap.range (jK.f i).hom
  have key := SSet.ι_chainComplexMap_f (f := TopCat.toSSet.map PA.map)
    (R := ModuleCat.of R R) (x := σ)
  have key' := congrArg (fun q => q.hom r) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key'
  have key'' : (jA.f i).hom
      (((TopCat.toSSet.obj (TopCat.of ↥(Aᶜ : Set M))).ιChainComplex
        (R := ModuleCat.of R R) σ).hom r) =
      ((TopCat.toSSet.obj (TopCat.of M)).ιChainComplex (R := ModuleCat.of R R)
        ((TopCat.toSSet.map PA.map).app _ σ)).hom r := key'
  rw [key'']
  refine b6m_simplex_mem_range R Kᶜ _ (fun t hK => ?_) r
  apply hKW hK
  simp only [S, Set.mem_iUnion, Set.mem_range]
  exact ⟨σ, hσ, t, rfl⟩

theorem b6m_homologyMap_eq_zero_of_cycle_image_eq_zero
    {K L : ChainCategory R} (f : K ⟶ L) (i : ℕ) (c : K.cycles i)
    (hc : (f.f i).hom ((K.iCycles i).hom c) = 0) :
    (HomologicalComplex.homologyMap f i).hom ((K.homologyπ i).hom c) = 0 := by
  have hcyc : (HomologicalComplex.cyclesMap f i).hom c = 0 := by
    apply (ModuleCat.mono_iff_injective (L.iCycles i)).mp inferInstance
    have h := congrArg (fun q => q.hom c) (HomologicalComplex.cyclesMap_i f i)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hc, map_zero] using h
  have hnat := congrArg (fun q => q.hom c) (HomologicalComplex.homologyπ_naturality f i)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hcyc, map_zero] using hnat

set_option backward.isDefEq.respectTransparency false in
theorem b6m_absoluteClass_vanishes_near_point
    {M : Type} [TopologicalSpace M] [T2Space M] (i : ℕ)
    (α : Homology R (TopCat.of M) i) (x : M)
    (hx : (relativeHomologyProjection R (pointComplementPair x) i).hom α = 0) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ ∀ y ∈ W,
      (relativeHomologyProjection R (pointComplementPair y) i).hom α = 0 := by
  let P := pointComplementPair x
  let j := ((chainPairFunctor R).obj P).hom
  have hex := (ShortComplex.moduleCat_exact_iff _).mp
    ((relativeChainShortComplex_shortExact R P).homology_exact₂ i)
  obtain ⟨β, hβ⟩ := hex α hx
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective
    (((chainPairFunctor R).obj P).left.homologyπ i)).mp inferInstance β
  change (HomologicalComplex.homologyMap j i).hom
    ((((chainPairFunctor R).obj P).left.homologyπ i).hom c) = α at hβ
  obtain ⟨W, hW, hxW, hmem⟩ := b6m_chain_complement_neighborhood R {x} i
    ((((chainPairFunctor R).obj P).left.iCycles i).hom c)
  refine ⟨W, hW, hxW (Set.mem_singleton x), fun y hy => ?_⟩
  change (HomologicalComplex.homologyMap (relativeChainProjection R (pointComplementPair y)) i).hom α = 0
  rw [← hβ]
  refine (b6m_homologyMap_hom_comp_apply R j
    (relativeChainProjection R (pointComplementPair y)) i
    ((((chainPairFunctor R).obj P).left.homologyπ i).hom c)).trans ?_
  apply b6m_homologyMap_eq_zero_of_cycle_image_eq_zero R
  obtain ⟨v, hv⟩ := hmem {y} (Set.singleton_subset_iff.mpr hy)
  change (((relativeChainProjection R (pointComplementPair y)).f i).hom
    ((j.f i).hom ((((chainPairFunctor R).obj P).left.iCycles i).hom c))) = 0
  rw [← hv]
  exact congrArg (fun q => (q.f i).hom v)
    (subspaceChainMap_relativeChainProjection R (pointComplementPair y))

set_option backward.isDefEq.respectTransparency false in
theorem b6m_relativeHomologyProjection_bijective_of_isEmpty
    (P : TopPair.{0}) [IsEmpty P.snd] (i : ℕ) :
    Function.Bijective (relativeHomologyProjection R P i).hom := by
  have hj : ((chainPairFunctor R).obj P).hom = 0 := by
    apply HomologicalComplex.hom_ext
    intro k
    apply SSet.chainComplex_hom_ext
    intro σ
    exact isEmptyElim ((P.snd.toSSetObjEquiv _ σ) Convexity.StdSimplex.barycenter)
  have hS := relativeChainShortComplex_shortExact R P
  letI : Mono (relativeChainProjection R P) := hS.exact.mono_g hj
  letI : Epi (relativeChainProjection R P) := hS.epi_g
  letI : IsIso (relativeChainProjection R P) := isIso_of_mono_of_epi _
  change Function.Bijective (HomologicalComplex.homologyMap (relativeChainProjection R P) i).hom
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
theorem b6m_relativeHomologyProjection_support (X : TopCat.{0})
    {A B : Set X} (hAB : A ⊆ B) (i : ℕ) (α : Homology R X i) :
    relativeHomologyMap R i (supportInclusionPairMap X hAB)
      ((relativeHomologyProjection R (TopPair.ofSubset (X := X) Bᶜ) i).hom α) =
        (relativeHomologyProjection R (TopPair.ofSubset (X := X) Aᶜ) i).hom α := by
  let φ := (relativeChainFunctor R).map (supportInclusionPairMap X hAB)
  have hnat := TopPair.Homotopy.relativeChainProjection_naturality (R := R)
    (supportInclusionPairMap X hAB)
  change relativeChainProjection R (TopPair.ofSubset (X := X) Bᶜ) ≫ φ =
    ((singularChainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)).map (𝟙 X) ≫
      relativeChainProjection R (TopPair.ofSubset (X := X) Aᶜ) at hnat
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at hnat
  change (HomologicalComplex.homologyMap φ i).hom
    ((HomologicalComplex.homologyMap (relativeChainProjection R
      (TopPair.ofSubset (X := X) Bᶜ)) i).hom α) = _
  exact (b6m_homologyMap_hom_comp_apply R
    (relativeChainProjection R (TopPair.ofSubset (X := X) Bᶜ)) φ i α).trans
      (congrArg (fun f : SingularChainComplex R X ⟶
        (relativeChainFunctor R).obj (TopPair.ofSubset (X := X) Aᶜ) =>
          (HomologicalComplex.homologyMap f i).hom α) hnat)

end HodgeLean.Foundations.Program
