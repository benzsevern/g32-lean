import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-! # Compact support of a relative singular class

A class in `H_i(M, M \ A; ℚ)` is represented by a chain `z` of `M` whose boundary is a finite
combination of simplices in `M \ A`. The union `S` of the images of those simplices is compact,
so closed in a Hausdorff `M`, and `z` is a relative cycle modulo `M \ K` for every `K` missing
`S`. So the class lifts to `H_i(M, M \ K; ℚ)` for every `K` with `A ⊆ K ⊆ M \ S`
(Hatcher, *Algebraic Topology*, Lemma 3.27, step (4)).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular Simplicial

namespace HodgeLean.RealDefs

/-- Simplicial chains are spanned by the summands of their simplices. -/
theorem C_chain_mem_iSup_range (X : SSet.{0}) (k : ℕ)
    (c : (X.chainComplex (ModuleCat.of ℚ ℚ)).X k) :
    c ∈ ⨆ σ : X _⦋k⦌, LinearMap.range (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom := by
  set N := ⨆ σ : X _⦋k⦌, LinearMap.range (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom
  have h : (ModuleCat.ofHom N.mkQ : (X.chainComplex (ModuleCat.of ℚ ℚ)).X k ⟶
      ModuleCat.of ℚ (_ ⧸ N)) = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    ext : 1
    apply LinearMap.ext
    intro r
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_ofHom,
      Submodule.mkQ_apply, comp_zero, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    exact le_iSup (fun σ => LinearMap.range (X.ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom) σ
      ⟨r, rfl⟩
  have := congrArg (fun f => f.hom c) h
  simp only [ModuleCat.hom_ofHom, Submodule.mkQ_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] at this
  exact (Submodule.Quotient.mk_eq_zero N).mp this

/-- Degreewise, a chain of `X` that vanishes modulo `A` is a chain of `A`. -/
theorem C_relativeChainProjection_exact (P : TopPair.{0}) (j : ℕ)
    (w : ((chainPairFunctor ℚ).obj P).right.X j)
    (hw : ((relativeChainProjection ℚ P).f j).hom w = 0) :
    ∃ v, ((((chainPairFunctor ℚ).obj P).hom.f j).hom v) = w := by
  have h := ((relativeChainShortComplex_shortExact ℚ P).map_of_exact
    (HomologicalComplex.eval _ (ComplexShape.down ℕ) j)).exact
  exact (ShortComplex.moduleCat_exact_iff _).mp h w hw

/-- Degreewise, every relative chain lifts to a chain of the ambient space. -/
theorem C_relativeChainProjection_surjective (P : TopPair.{0}) (j : ℕ) :
    Function.Surjective ((relativeChainProjection ℚ P).f j).hom := by
  have h := ((relativeChainShortComplex_shortExact ℚ P).map_of_exact
    (HomologicalComplex.eval _ (ComplexShape.down ℕ) j)).epi_g
  exact (ModuleCat.epi_iff_surjective _).mp h

/-- The summand of a singular simplex of `M` with values in `U` lies in the chains of `U`. -/
theorem C_simplex_mem_range {M : Type} [TopologicalSpace M] (U : Set M) {k : ℕ}
    (σ : (TopCat.toSSet.obj (TopCat.of M)) _⦋k⦌)
    (h : ∀ t, (TopCat.of M).toSSetObjEquiv _ σ t ∈ U) (r : ℚ) :
    (((TopCat.toSSet.obj (TopCat.of M)).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom r) ∈
      LinearMap.range ((((chainPairFunctor ℚ).obj
        (TopPair.ofSubset (X := TopCat.of M) U)).hom.f k).hom) := by
  let a : (TopCat.toSSet.obj (TopCat.of U)) _⦋k⦌ :=
    ((TopCat.of U).toSSetObjEquiv _).symm
      ⟨fun t => ⟨(TopCat.of M).toSSetObjEquiv _ σ t, h t⟩,
        ((TopCat.of M).toSSetObjEquiv _ σ).continuous.subtype_mk _⟩
  have ha : (TopCat.toSSet.map (TopPair.ofSubset (X := TopCat.of M) U).map).app _ a = σ := by
    apply ((TopCat.of M).toSSetObjEquiv _).injective
    ext t
    rfl
  refine ⟨((TopCat.toSSet.obj (TopCat.of U)).ιChainComplex (R := ModuleCat.of ℚ ℚ) a).hom r, ?_⟩
  have key := SSet.ι_chainComplexMap_f
    (f := TopCat.toSSet.map (TopPair.ofSubset (X := TopCat.of M) U).map)
    (R := ModuleCat.of ℚ ℚ) (x := a)
  rw [ha] at key
  exact congrArg (fun q => q.hom r) key

/-- A class in `H_i(M, M \ A; ℚ)` of a Hausdorff space lifts to `H_i(M, M \ K; ℚ)` for every
`K` with `A ⊆ K ⊆ W`, for some open `W ⊇ A`. -/
theorem C_exists_open_lift {M : Type} [TopologicalSpace M] [T2Space M] (A : Set M)
    (i : ℕ) (α : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Aᶜ) i) :
    ∃ W : Set M, IsOpen W ∧ A ⊆ W ∧ ∀ (K : Set M) (hAK : A ⊆ K), K ⊆ W →
      ∃ α' : RelativeHomology ℚ (TopPair.ofSubset (X := TopCat.of M) Kᶜ) i,
        relativeHomologyMap ℚ i (supportInclusionPairMap (TopCat.of M) hAK) α' = α := by
  let PA := TopPair.ofSubset (X := TopCat.of M) Aᶜ
  let Q := (relativeChainFunctor ℚ).obj PA
  let C := SingularChainComplex ℚ PA.fst
  let πA : C ⟶ Q := relativeChainProjection ℚ PA
  let jA : ((chainPairFunctor ℚ).obj PA).left ⟶ C := ((chainPairFunctor ℚ).obj PA).hom
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (Q.homologyπ i)).mp inferInstance α
  let j := (ComplexShape.down ℕ).next i
  obtain ⟨z, hz⟩ := C_relativeChainProjection_surjective PA i ((Q.iCycles i).hom c)
  have hdz : (πA.f j).hom ((C.d i j).hom z) = 0 := by
    have h1 := congrArg (fun q => q.hom z) (πA.comm i j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    rw [← h1]
    change (Q.d i j).hom ((πA.f i).hom z) = 0
    rw [hz]
    have h2 := congrArg (fun q => q.hom c) (Q.iCycles_d i j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h2
  obtain ⟨b, hb⟩ := C_relativeChainProjection_exact PA j _ hdz
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp
    (C_chain_mem_iSup_range (TopCat.toSSet.obj (TopCat.of ↥(Aᶜ : Set M))) j b)
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
  refine ⟨Sᶜ, hSc.isClosed.isOpen_compl, fun a ha hS => hSA a hS ha, fun K hAK hKW => ?_⟩
  let PK := TopPair.ofSubset (X := TopCat.of M) Kᶜ
  let QK := (relativeChainFunctor ℚ).obj PK
  let πK : C ⟶ QK := relativeChainProjection ℚ PK
  let jK : ((chainPairFunctor ℚ).obj PK).left ⟶ C := ((chainPairFunctor ℚ).obj PK).hom
  have hdzK : (C.d i j).hom z ∈ LinearMap.range (jK.f j).hom := by
    rw [← hb]
    suffices h : (⨆ σ ∈ s, LinearMap.range
        ((TopCat.toSSet.obj (TopCat.of ↥(Aᶜ : Set M))).ιChainComplex
          (R := ModuleCat.of ℚ ℚ) σ).hom) ≤
        (LinearMap.range (jK.f j).hom).comap (jA.f j).hom from h hs
    refine iSup₂_le fun σ hσ => ?_
    rintro _ ⟨r, rfl⟩
    show (jA.f j).hom
      (((TopCat.toSSet.obj (TopCat.of ↥(Aᶜ : Set M))).ιChainComplex
        (R := ModuleCat.of ℚ ℚ) σ).hom r) ∈ LinearMap.range (jK.f j).hom
    have key := SSet.ι_chainComplexMap_f (f := TopCat.toSSet.map PA.map)
      (R := ModuleCat.of ℚ ℚ) (x := σ)
    have key' := congrArg (fun q => q.hom r) key
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at key'
    have key'' : (jA.f j).hom
        (((TopCat.toSSet.obj (TopCat.of ↥(Aᶜ : Set M))).ιChainComplex
          (R := ModuleCat.of ℚ ℚ) σ).hom r) =
        ((TopCat.toSSet.obj (TopCat.of M)).ιChainComplex (R := ModuleCat.of ℚ ℚ)
          ((TopCat.toSSet.map PA.map).app _ σ)).hom r := key'
    rw [key'']
    refine C_simplex_mem_range Kᶜ _ (fun t hK => ?_) r
    apply hKW hK
    simp only [S, Set.mem_iUnion, Set.mem_range]
    exact ⟨σ, hσ, t, rfl⟩
  have hcyc : ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ ((πK.f i).hom z)) ≫
      QK.d i j = 0 := by
    ext : 1
    apply LinearMap.ext_ring
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      LinearMap.toSpanSingleton_apply, one_smul, ModuleCat.hom_zero, LinearMap.zero_apply]
    have h1 := congrArg (fun q => q.hom z) (πK.comm i j)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    change (QK.d i j).hom ((πK.f i).hom z) = 0
    rw [h1]
    obtain ⟨v, hv⟩ := hdzK
    rw [← hv]
    exact congrArg (fun q => (q.f j).hom v) (subspaceChainMap_relativeChainProjection ℚ PK)
  refine ⟨(QK.homologyπ i).hom ((QK.liftCycles _ j rfl hcyc).hom 1), ?_⟩
  let φ : QK ⟶ Q := (relativeChainFunctor ℚ).map (supportInclusionPairMap (TopCat.of M) hAK)
  change (HomologicalComplex.homologyMap φ i).hom
    ((QK.homologyπ i).hom ((QK.liftCycles _ j rfl hcyc).hom 1)) = (Q.homologyπ i).hom c
  have hnat := congrArg (fun q => q.hom ((QK.liftCycles _ j rfl hcyc).hom 1))
    (HomologicalComplex.homologyπ_naturality φ i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [hnat]
  congr 1
  apply (ModuleCat.mono_iff_injective (Q.iCycles i)).mp inferInstance
  have hl := congrArg (fun q => (Q.iCycles i).hom (q.hom 1))
    (HomologicalComplex.liftCycles_comp_cyclesMap (K := QK) _ j rfl hcyc φ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hl
  rw [hl]
  have hi := congrArg (fun q => q.hom 1) (HomologicalComplex.liftCycles_i Q
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ ((πK.f i).hom z)) ≫ φ.f i) j rfl
    (by rw [Category.assoc, φ.comm, ← Category.assoc, hcyc, zero_comp]))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hi
  rw [hi]
  simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul]
  rw [← hz]
  have hid : ((singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ)).map
      (𝟙 (TopCat.of M)) = 𝟙 C := CategoryTheory.Functor.map_id _ _
  have hn0 : πK ≫ φ = 𝟙 C ≫ πA := by
    rw [← hid]
    exact TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
      (supportInclusionPairMap (TopCat.of M) hAK)
  rw [Category.id_comp] at hn0
  exact congrArg (fun q => (q.f i).hom z) hn0

end HodgeLean.RealDefs
