import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.ChainStalk
import HodgeConjecture.Mathlib.Geometry.Convex.StdSimplex

/-! # Local relative-chain calculations for supported duality -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits TopologicalSpace AlgebraicTopology.Singular
open scoped Simplicial
namespace HodgeLean.Foundations.QuotientDuality

/-- Sheafification preserves the entire stalk chain complex.
Source: HodgeConjecture 2ead713, Other/AlgebraicTopology/Singular/Sheaf/Chain.lean.
HC no distance; AV milestone no distance. -/
lemma properCycle_chain_sheafification_stalk_isIso (X : TopCat.{0}) (x : X) :
    IsIso (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).mapHomologicalComplex
      (ComplexShape.down ℕ)).map (singularChainSheafificationUnit ℚ X)) := by
  let f := ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).mapHomologicalComplex
    (ComplexShape.down ℕ)).map (singularChainSheafificationUnit ℚ X)
  letI hcomponents : ∀ n, IsIso (f.f n) := fun n =>
    singularChainSheafificationUnit_stalk_isIso ℚ X x n
  exact HomologicalComplex.Hom.isIso_of_components f

set_option backward.isDefEq.respectTransparency false in
lemma properCycle_relative_projection_restrict (X : TopCat.{0}) {S T : Set X} (h : S ⊆ T) :
    relativeChainProjection ℚ (TopPair.ofSubset Tᶜ) ≫
      (relativeChainFunctor ℚ).map (supportInclusionPairMap X h) =
        relativeChainProjection ℚ (TopPair.ofSubset Sᶜ) := by
  have hn := TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ)
    (supportInclusionPairMap X h)
  change _ = (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
    (ModuleCat.of ℚ ℚ)).map (𝟙 X)) ≫ relativeChainProjection ℚ (TopPair.ofSubset Sᶜ) at hn
  exact hn.trans ((congrArg
    (fun f => f ≫ relativeChainProjection ℚ (TopPair.ofSubset Sᶜ))
    (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℚ)).obj
      (ModuleCat.of ℚ ℚ)).map_id X)).trans (Category.id_comp _))

lemma properCycle_simplex_avoids_neighborhood (X : TopCat.{0}) [T2Space X]
    (x : X) {n : ℕ}
    (σ : (TopCat.toSSet.obj (TopPair.ofSubset ({x} : Set X)ᶜ).snd) _⦋n⦌) :
    ∃ (U : OpenNhds x)
      (τ : (TopCat.toSSet.obj (TopPair.ofSubset (U.1 : Set X)ᶜ).snd) _⦋n⦌),
      (TopCat.toSSet.map (TopPair.ofSubset (U.1 : Set X)ᶜ).map).app _ τ =
        (TopCat.toSSet.map (TopPair.ofSubset ({x} : Set X)ᶜ).map).app _ σ := by
  let f := (TopPair.ofSubset ({x} : Set X)ᶜ).snd.toSSetObjEquiv _ σ
  let g : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X) :=
    ⟨fun t => (f t).1, continuous_subtype_val.comp f.continuous⟩
  have hc : IsClosed (Set.range g) := (isCompact_range g.continuous).isClosed
  let U : OpenNhds x := ⟨⟨(Set.range g)ᶜ, hc.isOpen_compl⟩, by
    rintro ⟨t, ht⟩
    exact (f t).2 (by simpa only [g, ContinuousMap.coe_mk, Set.mem_singleton_iff] using ht)⟩
  have hg : ∀ t, g t ∈ (U.1 : Set X)ᶜ := fun t h => h (Set.mem_range_self t)
  let τ : (TopCat.toSSet.obj (TopPair.ofSubset (U.1 : Set X)ᶜ).snd) _⦋n⦌ :=
    ((TopPair.ofSubset (U.1 : Set X)ᶜ).snd.toSSetObjEquiv _).symm
      ⟨fun t => ⟨g t, hg t⟩, g.continuous.subtype_mk hg⟩
  refine ⟨U, τ, ?_⟩
  apply (X.toSSetObjEquiv _).injective
  rfl

/-- Restriction from neighborhoods to the actual point complement.
Source: HodgeConjecture 2ead713, Other/AlgebraicTopology/Singular/Sheaf/ChainStalk.lean.
HC no distance; AV milestone no distance. -/
def properCycle_local_chain_cocone (X : TopCat.{0}) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ openRelativeSingularChainComplexFunctor ℚ X) where
  pt := (relativeChainFunctor ℚ).obj (TopPair.ofSubset ({x} : Set X)ᶜ)
  ι :=
    { app U := (relativeChainFunctor ℚ).map
        (supportInclusionPairMap X (Set.singleton_subset_iff.mpr U.unop.2))
      naturality {U V} i := by
        change (relativeChainFunctor ℚ).map (supportInclusionPairMap X (leOfHom i.unop)) ≫
          (relativeChainFunctor ℚ).map
            (supportInclusionPairMap X (Set.singleton_subset_iff.mpr V.unop.2)) = _
        rw [← CategoryTheory.Functor.map_comp, ← supportInclusionPairMap_trans]
        rfl }

example (X : TopCat.{0}) (x : X) :
    (properCycle_local_chain_cocone X x).pt =
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset ({x} : Set X)ᶜ) := rfl

set_option backward.isDefEq.respectTransparency false in
lemma properCycle_neighborhood_cocone_factor (X : TopCat.{0}) (x : X)
    (c : Cocone ((OpenNhds.inclusion x).op ⋙ openRelativeSingularChainComplexFunctor ℚ X))
    (U : OpenNhds x) :
    relativeChainProjection ℚ (TopPair.ofSubset ((⊤ : Opens X) : Set X)ᶜ) ≫
        c.ι.app (.op ⟨⊤, trivial⟩) =
      relativeChainProjection ℚ (TopPair.ofSubset (U.1 : Set X)ᶜ) ≫ c.ι.app (.op U) := by
  let i : U ⟶ (⟨⊤, trivial⟩ : OpenNhds x) := homOfLE le_top
  have hi := c.w i.op
  change (relativeChainFunctor ℚ).map (supportInclusionPairMap X (leOfHom i)) ≫
    c.ι.app (.op U) = c.ι.app (.op ⟨⊤, trivial⟩) at hi
  rw [← hi, ← Category.assoc, properCycle_relative_projection_restrict]

set_option backward.isDefEq.respectTransparency false in
lemma properCycle_subspace_simplex_projection (P : TopPair.{0}) {n : ℕ}
    (σ : (TopCat.toSSet.obj P.snd) _⦋n⦌) :
    (TopCat.toSSet.obj P.fst).ιChainComplex
        ((TopCat.toSSet.map P.map).app _ σ) ≫ (relativeChainProjection ℚ P).f n = 0 := by
  rw [← SSet.ι_chainComplexMap_f, Category.assoc]
  have hh := congrArg (fun f => f.f n) (subspaceChainMap_relativeChainProjection ℚ P)
  change (SSet.chainComplexMap (TopCat.toSSet.map P.map) (ModuleCat.of ℚ ℚ)).f n ≫
    (relativeChainProjection ℚ P).f n = 0 at hh
  rw [hh, comp_zero]

set_option backward.isDefEq.respectTransparency false in
lemma properCycle_complement_annihilates_cocone (X : TopCat.{0}) [T2Space X] (x : X)
    (c : Cocone ((OpenNhds.inclusion x).op ⋙ openRelativeSingularChainComplexFunctor ℚ X)) :
    ((chainPairFunctor ℚ).obj (TopPair.ofSubset ({x} : Set X)ᶜ)).hom ≫
      (relativeChainProjection ℚ (TopPair.ofSubset ((⊤ : Opens X) : Set X)ᶜ) ≫
        c.ι.app (.op ⟨⊤, trivial⟩)) = 0 := by
  let α := relativeChainProjection ℚ (TopPair.ofSubset ((⊤ : Opens X) : Set X)ᶜ) ≫
    c.ι.app (.op ⟨⊤, trivial⟩)
  apply HomologicalComplex.hom_ext
  intro n
  change (SSet.chainComplexMap
    (TopCat.toSSet.map (TopPair.ofSubset ({x} : Set X)ᶜ).map)
    (ModuleCat.of ℚ ℚ)).f n ≫ α.f n = 0
  apply SSet.chainComplex_hom_ext
  intro σ
  obtain ⟨U, τ, hτ⟩ := properCycle_simplex_avoids_neighborhood X x σ
  rw [← Category.assoc, SSet.ι_chainComplexMap_f, ← hτ]
  have hh := congrArg (fun f => f.f n) (properCycle_neighborhood_cocone_factor X x c U)
  change α.f n = (relativeChainProjection ℚ (TopPair.ofSubset (U.1 : Set X)ᶜ)).f n ≫
    (c.ι.app (.op U)).f n at hh
  rw [hh, ← Category.assoc, comp_zero]
  exact (congrArg (fun f => f ≫ (c.ι.app (.op U)).f n)
    (properCycle_subspace_simplex_projection (TopPair.ofSubset (U.1 : Set X)ᶜ) τ)).trans zero_comp

set_option backward.isDefEq.respectTransparency false in
/-- The actual point-complement chain complex is the neighborhood colimit.
Source: HodgeConjecture 2ead713, Other/AlgebraicTopology/Singular/Sheaf/ChainStalk.lean.
HC no distance; AV milestone no distance. -/
def properCycle_local_chain_colimit (X : TopCat.{0}) [T2Space X] (x : X) :
    IsColimit (properCycle_local_chain_cocone X x) := by
  let α (c : Cocone ((OpenNhds.inclusion x).op ⋙ openRelativeSingularChainComplexFunctor ℚ X)) :=
    relativeChainProjection ℚ (TopPair.ofSubset ((⊤ : Opens X) : Set X)ᶜ) ≫
      c.ι.app (.op ⟨⊤, trivial⟩)
  let d (c : Cocone ((OpenNhds.inclusion x).op ⋙ openRelativeSingularChainComplexFunctor ℚ X)) :=
    cokernel.desc ((chainPairFunctor ℚ).obj (TopPair.ofSubset ({x} : Set X)ᶜ)).hom
      (α c) (properCycle_complement_annihilates_cocone X x c)
  have hd (c) : relativeChainProjection ℚ (TopPair.ofSubset ({x} : Set X)ᶜ) ≫ d c = α c :=
    cokernel.π_desc _ _ _
  refine ⟨d, ?_, ?_⟩
  · intro c U
    let P := TopPair.ofSubset (U.unop.1 : Set X)ᶜ
    haveI hπ : Epi (relativeChainProjection ℚ P) := by
      dsimp [relativeChainProjection]
      infer_instance
    apply (cancel_epi (relativeChainProjection ℚ P)).mp
    change relativeChainProjection ℚ P ≫
      (relativeChainFunctor ℚ).map
        (supportInclusionPairMap X (Set.singleton_subset_iff.mpr U.unop.2)) ≫ d c = _
    rw [← Category.assoc, properCycle_relative_projection_restrict, hd]
    exact properCycle_neighborhood_cocone_factor X x c U.unop
  · intro c m hm
    haveI hπ : Epi (relativeChainProjection ℚ (TopPair.ofSubset ({x} : Set X)ᶜ)) := by
      dsimp [relativeChainProjection]
      infer_instance
    apply (cancel_epi (relativeChainProjection ℚ (TopPair.ofSubset ({x} : Set X)ᶜ))).mp
    rw [hd]
    change _ = relativeChainProjection ℚ (TopPair.ofSubset ((⊤ : Opens X) : Set X)ᶜ) ≫
      c.ι.app (.op ⟨⊤, trivial⟩)
    rw [← hm (.op ⟨⊤, trivial⟩), ← Category.assoc]
    change _ = (relativeChainProjection ℚ (TopPair.ofSubset ((⊤ : Opens X) : Set X)ᶜ) ≫
      (relativeChainFunctor ℚ).map (supportInclusionPairMap X _)) ≫ m
    rw [properCycle_relative_projection_restrict]

example (X : TopCat.{0}) [T2Space X] (x : X) :
    (properCycle_local_chain_colimit X x).desc (properCycle_local_chain_cocone X x) = 𝟙 _ := by
  symm
  apply (properCycle_local_chain_colimit X x).uniq
  intro U
  exact Category.comp_id _

/-- The relative-chain presheaf stalk is the actual point-complement chain group.
Source: HodgeConjecture 2ead713, Other/AlgebraicTopology/Singular/Sheaf/ChainStalk.lean.
HC no distance; AV milestone no distance. -/
def properCycle_chain_presheaf_stalk_iso (X : TopCat.{0}) [T2Space X] (x : X) (n : ℕ) :
    (singularChainPresheaf ℚ X n).stalk x ≅
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).obj
        (((relativeChainFunctor ℚ).obj (TopPair.ofSubset ({x} : Set X)ᶜ)).X n) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (isColimitOfPreserves (chainDegreeAdditiveFunctor ℚ n) (properCycle_local_chain_colimit X x))

lemma properCycle_chain_stalk_iso_germ (X : TopCat.{0}) [T2Space X]
    (x : X) (U : Opens X) (hx : x ∈ U) (n : ℕ) :
    (singularChainPresheaf ℚ X n).germ U x hx ≫
        (properCycle_chain_presheaf_stalk_iso X x n).hom =
      (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
        (((relativeChainFunctor ℚ).map
          (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx))).f n) :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    (isColimitOfPreserves (chainDegreeAdditiveFunctor ℚ n)
      (properCycle_local_chain_colimit X x)) (.op ⟨U, hx⟩)

set_option backward.isDefEq.respectTransparency false in
lemma properCycle_chain_stalk_iso_boundary (X : TopCat.{0}) [T2Space X] (x : X) (n : ℕ) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map (singularChainBoundary ℚ X n) ≫
        (properCycle_chain_presheaf_stalk_iso X x n).hom =
      (properCycle_chain_presheaf_stalk_iso X x (n + 1)).hom ≫
        (forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map
          (((relativeChainFunctor ℚ).obj (TopPair.ofSubset ({x} : Set X)ᶜ)).d (n + 1) n) := by
  apply (singularChainPresheaf ℚ X (n + 1)).stalk_hom_ext
  intro U hx
  rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ,
    Category.assoc, properCycle_chain_stalk_iso_germ,
    ← Category.assoc, properCycle_chain_stalk_iso_germ]
  exact congrArg ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).map)
    (((relativeChainFunctor ℚ).map
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx))).comm (n + 1) n).symm

/-- The neighborhood stalk comparison retains the entire boundary operator.
Source: HodgeConjecture 2ead713, Other/AlgebraicTopology/Singular/Sheaf/ChainStalk.lean.
HC no distance; AV milestone no distance. -/
def properCycle_presheaf_complex_stalk_iso (X : TopCat.{0}) [T2Space X] (x : X) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (singularChainPresheafComplex ℚ X) ≅
    ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
      ((relativeChainFunctor ℚ).obj (TopPair.ofSubset ({x} : Set X)ᶜ)) :=
  HomologicalComplex.Hom.isoOfComponents (properCycle_chain_presheaf_stalk_iso X x) (by
    intro i j hij
    obtain rfl := hij
    change (properCycle_chain_presheaf_stalk_iso X x (j + 1)).hom ≫ _ =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).map
        ((singularChainPresheafComplex ℚ X).d (j + 1) j) ≫
          (properCycle_chain_presheaf_stalk_iso X x j).hom
    rw [singularChainPresheafComplex_d]
    exact (properCycle_chain_stalk_iso_boundary X x j).symm)

/-- The sheafified relative-chain stalk is the actual local chain complex.
Source: HodgeConjecture 2ead713, Other/AlgebraicTopology/Singular/Sheaf/ChainStalk.lean.
HC no distance; AV milestone no distance. -/
def properCycle_sheaf_complex_stalk_iso (X : TopCat.{0}) [T2Space X] (x : X) :
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
      (((TopCat.Sheaf.forget AddCommGrpCat.{0} X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (singularChainSheafComplex ℚ X)) ≅
    ((forget₂ (ModuleCat.{0} ℚ) AddCommGrpCat.{0}).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
      ((relativeChainFunctor ℚ).obj (TopPair.ofSubset ({x} : Set X)ᶜ)) := by
  let f := ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x).mapHomologicalComplex
    (ComplexShape.down ℕ)).map (singularChainSheafificationUnit ℚ X)
  letI hunit : IsIso f := properCycle_chain_sheafification_stalk_isIso X x
  exact (asIso f).symm ≪≫ properCycle_presheaf_complex_stalk_iso X x

end HodgeLean.Foundations.QuotientDuality
