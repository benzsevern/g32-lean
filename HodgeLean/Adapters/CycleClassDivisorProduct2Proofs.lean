import HodgeLean.Adapters.CycleClassDivisorProduct2Defs

/-! # Excision obligation for the complement-small quotient
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Adapters

private def ccm14_unionCover (Y : TopCat.{0}) (S T : Set Y) :
    Bool → Set (TopCat.of ↥((S ∩ T)ᶜ)) :=
  fun b => {x | x.1 ∈ ccm13_complementFamily Y S T b}

private lemma ccm14_unionCover_isOpen (Y : TopCat.{0}) (S T : Set Y)
    (hS : IsClosed S) (hT : IsClosed T) :
    ∀ b, IsOpen (ccm14_unionCover Y S T b) := by
  intro b
  cases b
  · exact hS.isOpen_compl.preimage continuous_subtype_val
  · exact hT.isOpen_compl.preimage continuous_subtype_val

private lemma ccm14_unionCover_iUnion (Y : TopCat.{0}) (S T : Set Y) :
    ⋃ b, ccm14_unionCover Y S T b = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x.1 ∈ S
  · exact Set.mem_iUnion.2 ⟨true, by
      simp only [ccm14_unionCover, ccm13_complementFamily, if_pos,
        Set.mem_setOf_eq, Set.mem_compl_iff]
      exact fun hT => x.2 ⟨hx, hT⟩⟩
  · exact Set.mem_iUnion.2 ⟨false, by
      simp [ccm14_unionCover, ccm13_complementFamily, hx]⟩

private def ccm14_smallToUnionSmall (Y : TopCat.{0}) (S T : Set Y) :
    (coverSmallSingularSubcomplex Y (ccm13_complementFamily Y S T) : SSet) ⟶
      coverSmallSingularSubcomplex (TopCat.of ↥((S ∩ T)ᶜ))
        (ccm14_unionCover Y S T) := by
  apply SSet.Subcomplex.lift (ccm14_smallToUnion Y S T)
  intro n σ hσ
  obtain ⟨σ, rfl⟩ := hσ
  obtain ⟨b, τ, hτ⟩ :=
    (mem_coverSmallSingularSubcomplex_iff_exists_preimage Y
      (ccm13_complementFamily Y S T) σ.1).mp σ.2
  have hb : ccm13_complementFamily Y S T b ⊆ (S ∩ T)ᶜ := by
    cases b <;> simp only [ccm13_complementFamily, Bool.false_eq_true, ↓reduceIte]
    · exact fun _ hx h ↦ hx h.1
    · exact fun _ hx h ↦ hx h.2
  let j : TopCat.of (ccm13_complementFamily Y S T b) ⟶
      TopCat.of ↥((S ∩ T)ᶜ) :=
    TopCat.ofHom ⟨fun x ↦ ⟨x.1, hb x.2⟩,
      Continuous.subtype_mk continuous_subtype_val _⟩
  let k : TopCat.of (ccm13_complementFamily Y S T b) ⟶
      TopCat.of (ccm14_unionCover Y S T b) :=
    TopCat.ofHom ⟨fun x ↦ ⟨⟨x.1, hb x.2⟩, x.2⟩, by fun_prop⟩
  apply (mem_coverSmallSingularSubcomplex_iff_exists_preimage
    (TopCat.of ↥((S ∩ T)ᶜ)) (ccm14_unionCover Y S T) _).mpr
  refine ⟨b, (TopCat.toSSet.map k).app n τ, ?_⟩
  apply ((TopCat.of ↥((S ∩ T)ᶜ)).toSSetObjEquiv n).injective
  ext t
  have hc := congrArg (fun f ↦ f.app n σ)
    (ccm14_smallToUnion_comp Y S T)
  have hc' :
      (TopCat.toSSet.map (topologicalSubsetInclusion Y (S ∩ T)ᶜ)).app n
          ((ccm14_smallToUnion Y S T).app n σ) = σ.1 := by
    change (TopCat.toSSet.map (topologicalSubsetInclusion Y (S ∩ T)ᶜ)).app n
      ((ccm14_smallToUnion Y S T).app n σ) = σ.1 at hc
    exact hc
  have hj :
      (TopCat.toSSet.map (topologicalSubsetInclusion Y (S ∩ T)ᶜ)).app n
          ((TopCat.toSSet.map j).app n τ) = σ.1 := by
    have hmap : TopCat.toSSet.map j ≫
        TopCat.toSSet.map (topologicalSubsetInclusion Y (S ∩ T)ᶜ) =
          TopCat.toSSet.map
            (topologicalSubsetInclusion Y (ccm13_complementFamily Y S T b)) := by
      rw [← Functor.map_comp]
      rfl
    have := congrArg (fun f ↦ f.app n τ) hmap
    change (TopCat.toSSet.map (topologicalSubsetInclusion Y (S ∩ T)ᶜ)).app n
      ((TopCat.toSSet.map j).app n τ) =
        (TopCat.toSSet.map (topologicalSubsetInclusion Y
          (ccm13_complementFamily Y S T b))).app n τ at this
    exact this.trans hτ
  rw [← hc'] at hj
  exact congrArg (fun z ↦ Y.toSSetObjEquiv n z t) hj

@[reassoc]
private lemma ccm14_smallToUnionSmall_comp_inclusion (Y : TopCat.{0}) (S T : Set Y) :
    ccm14_smallToUnionSmall Y S T ≫
        (coverSmallSingularSubcomplex (TopCat.of ↥((S ∩ T)ᶜ))
          (ccm14_unionCover Y S T)).ι =
      ccm14_smallToUnion Y S T :=
  SSet.Subcomplex.lift_ι _ _

private lemma ccm14_smallToUnionSmall_isIso (Y : TopCat.{0}) (S T : Set Y) :
    IsIso (ccm14_smallToUnionSmall Y S T) := by
  have hmonoUnion : Mono (ccm14_smallToUnion Y S T) := by
    exact mono_of_mono_fac (ccm14_smallToUnion_comp Y S T)
  letI : Mono (ccm14_smallToUnionSmall Y S T) := by
    exact mono_of_mono_fac (ccm14_smallToUnionSmall_comp_inclusion Y S T)
  letI : Epi (ccm14_smallToUnionSmall Y S T) := by
    rw [NatTrans.epi_iff_epi_app]
    intro n
    rw [epi_iff_surjective]
    intro σ
    obtain ⟨b, τ, hτ⟩ :=
      (mem_coverSmallSingularSubcomplex_iff_exists_preimage
        (TopCat.of ↥((S ∩ T)ᶜ)) (ccm14_unionCover Y S T) σ.1).mp σ.2
    let l : TopCat.of (ccm14_unionCover Y S T b) ⟶
        TopCat.of (ccm13_complementFamily Y S T b) :=
      TopCat.ofHom ⟨fun x ↦ ⟨x.1.1, x.2⟩, by fun_prop⟩
    let σ₀ : (coverSmallSingularSubcomplex Y
        (ccm13_complementFamily Y S T) : SSet).obj n :=
      ⟨(TopCat.toSSet.map (topologicalSubsetInclusion Y
          (ccm13_complementFamily Y S T b))).app n
          ((TopCat.toSSet.map l).app n τ),
        (mem_coverSmallSingularSubcomplex_iff_exists_preimage Y
          (ccm13_complementFamily Y S T) _).mpr
            ⟨b, (TopCat.toSSet.map l).app n τ, rfl⟩⟩
    refine ⟨σ₀, ?_⟩
    apply Subtype.ext
    change ((ccm14_smallToUnionSmall Y S T ≫
      (coverSmallSingularSubcomplex (TopCat.of ↥((S ∩ T)ᶜ))
        (ccm14_unionCover Y S T)).ι).app n) σ₀ = _
    rw [ccm14_smallToUnionSmall_comp_inclusion]
    apply ((TopCat.of ↥((S ∩ T)ᶜ)).toSSetObjEquiv n).injective
    ext t
    have hc := congrArg (fun f ↦ f.app n σ₀)
      (ccm14_smallToUnion_comp Y S T)
    have hc' :
        (TopCat.toSSet.map (topologicalSubsetInclusion Y (S ∩ T)ᶜ)).app n
            ((ccm14_smallToUnion Y S T).app n σ₀) = σ₀.1 := by
      change (TopCat.toSSet.map (topologicalSubsetInclusion Y (S ∩ T)ᶜ)).app n
        ((ccm14_smallToUnion Y S T).app n σ₀) = σ₀.1 at hc
      exact hc
    have hs :
        (TopCat.toSSet.map (topologicalSubsetInclusion Y (S ∩ T)ᶜ)).app n σ.1 =
          σ₀.1 := by
      rw [← hτ]
      rfl
    rw [← hc'] at hs
    exact congrArg (fun z ↦ Y.toSSetObjEquiv n z t) hs.symm
  exact isIso_of_mono_of_epi _

private lemma ccm14_smallToUnionChainMap_quasiIso (Y : TopCat.{0}) (S T : Set Y)
    (hS : IsClosed S) (hT : IsClosed T) :
    QuasiIso (SSet.chainComplexMap (ccm14_smallToUnion Y S T)
      (ModuleCat.of ℚ ℚ)) := by
  letI : IsIso (ccm14_smallToUnionSmall Y S T) :=
    ccm14_smallToUnionSmall_isIso Y S T
  let e := coverSmallRationalChainHomotopyEquiv_of_openCover
    (TopCat.of ↥((S ∩ T)ᶜ)) (ccm14_unionCover Y S T)
      (ccm14_unionCover_isOpen Y S T hS hT) (ccm14_unionCover_iUnion Y S T)
  have hsmall : QuasiIso e.hom := e.quasiIso_hom
  rw [coverSmallRationalChainHomotopyEquiv_of_openCover_hom] at hsmall
  have hsmall' : QuasiIso (SSet.chainComplexMap
      (coverSmallSingularSubcomplex (TopCat.of ↥((S ∩ T)ᶜ))
        (ccm14_unionCover Y S T)).ι (ModuleCat.of ℚ ℚ)) := by
    exact hsmall
  have hiso : QuasiIso (SSet.chainComplexMap (ccm14_smallToUnionSmall Y S T)
      (ModuleCat.of ℚ ℚ)) := inferInstance
  letI : QuasiIso (SSet.chainComplexMap (ccm14_smallToUnionSmall Y S T)
      (ModuleCat.of ℚ ℚ)) := hiso
  letI : QuasiIso (SSet.chainComplexMap
      (coverSmallSingularSubcomplex (TopCat.of ↥((S ∩ T)ᶜ))
        (ccm14_unionCover Y S T)).ι (ModuleCat.of ℚ ℚ)) := hsmall'
  rw [← ccm14_smallToUnionSmall_comp_inclusion,
    SSet.chainComplexMap, Functor.map_comp]
  exact quasiIso_comp _ _

private def ccm14_smallToRelativePairArrow (Y : TopCat.{0}) (S T : Set Y) :
    Arrow.mk (ccm14_smallInclusion Y S T) ⟶
      (chainPairFunctor ℚ).obj (TopPair.ofSubset (S ∩ T)ᶜ) :=
  Arrow.homMk
    (SSet.chainComplexMap (ccm14_smallToUnion Y S T) (ModuleCat.of ℚ ℚ))
    (𝟙 _)
    (by
      have h : SSet.chainComplexMap (ccm14_smallToUnion Y S T) (ModuleCat.of ℚ ℚ) ≫
          SSet.chainComplexMap (TopCat.toSSet.map
            (topologicalSubsetInclusion Y (S ∩ T)ᶜ)) (ModuleCat.of ℚ ℚ) =
        SSet.chainComplexMap (coverSmallSingularSubcomplex Y
          (ccm13_complementFamily Y S T)).ι (ModuleCat.of ℚ ℚ) := by
        rw [SSet.chainComplexMap, ← Functor.map_comp, ccm14_smallToUnion_comp]
      change SSet.chainComplexMap (ccm14_smallToUnion Y S T) (ModuleCat.of ℚ ℚ) ≫
          SSet.chainComplexMap (TopCat.toSSet.map
            (topologicalSubsetInclusion Y (S ∩ T)ᶜ)) (ModuleCat.of ℚ ℚ) =
        SSet.chainComplexMap (coverSmallSingularSubcomplex Y
          (ccm13_complementFamily Y S T)).ι (ModuleCat.of ℚ ℚ) ≫ 𝟙 _
      simpa only [Category.comp_id] using h)

private def ccm14_cokernelSequenceHom (Y : TopCat.{0}) (S T : Set Y) :
    ShortComplex.cokernelSequence (ccm14_smallInclusion Y S T) ⟶
      ShortComplex.cokernelSequence
        ((chainPairFunctor ℚ).obj (TopPair.ofSubset (S ∩ T)ᶜ)).hom :=
  ShortComplex.homMk
    (SSet.chainComplexMap (ccm14_smallToUnion Y S T) (ModuleCat.of ℚ ℚ))
    (𝟙 _)
    (ccm14_relativeComparison Y S T)
    (ccm14_smallToRelativePairArrow Y S T).w
    (cokernel.π_desc _ _ _).symm

private lemma ccm14_smallCokernelSequence_shortExact (Y : TopCat.{0}) (S T : Set Y) :
    (ShortComplex.cokernelSequence (ccm14_smallInclusion Y S T)).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by
    change Mono (ccm14_smallInclusion Y S T)
    infer_instance
  epi_g := by infer_instance

private lemma ccm14_relativeCokernelSequence_shortExact (Y : TopCat.{0}) (S T : Set Y) :
    (ShortComplex.cokernelSequence
      ((chainPairFunctor ℚ).obj (TopPair.ofSubset (S ∩ T)ᶜ)).hom).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by
    change Mono ((chainPairFunctor ℚ).obj (TopPair.ofSubset (S ∩ T)ᶜ)).hom
    exact relativeChainMap_mono ℚ (TopPair.ofSubset (S ∩ T)ᶜ)
  epi_g := by infer_instance

theorem ccm14_relativeComparison_quasiIso_aux (Y : TopCat.{0}) (S T : Set Y)
    (hS : IsClosed S) (hT : IsClosed T) :
    QuasiIso (ccm14_relativeComparison Y S T) := by
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (ccm14_cokernelSequenceHom Y S T)
    (ccm14_smallCokernelSequence_shortExact Y S T)
    (ccm14_relativeCokernelSequence_shortExact Y S T)
    (ccm14_smallToUnionChainMap_quasiIso Y S T hS hT)
    (inferInstanceAs (QuasiIso (𝟙 (((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of ℚ ℚ))))))

end HodgeLean.Adapters
