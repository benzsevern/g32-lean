import HodgeLean.RealDefs.FiniteBettiCompactDefs
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Contractible

/-! # Proof obligations for the finite Betti number specification -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular

namespace HodgeLean.RealDefs

/-- Degree-zero homology is finite-dimensional when there are finitely many path components. -/
theorem finbettiA_finite_homology_zero_of_finite_zerothHomotopy (Y : Type) [TopologicalSpace Y]
    [Finite (ZerothHomotopy Y)] : Module.Finite ℚ (Homology ℚ (TopCat.of Y) 0) := by
  classical
  let e := (TopCat.of Y).singularHomology₀Iso (ModuleCat.of ℚ ℚ) ≪≫
    ModuleCat.coprodIsoDirectSum (fun _ : ZerothHomotopy (TopCat.of Y) ↦ ModuleCat.of ℚ ℚ)
  exact Module.Finite.equiv e.toLinearEquiv.symm

/-- Homology at a degree where the singular chain complex is exact is finite-dimensional. -/
theorem finbettiA_finite_homology_of_exactAt (Y : Type) [TopologicalSpace Y] (n : ℕ)
    (h : (SingularChainComplex ℚ (TopCat.of Y)).ExactAt n) :
    Module.Finite ℚ (Homology ℚ (TopCat.of Y) n) := by
  have : Subsingleton (Homology ℚ (TopCat.of Y) n) :=
    ModuleCat.subsingleton_of_isZero h.isZero_homology
  infer_instance

theorem finbetti_finiteHomology_of_convex_aux {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Set E} (hK : Convex ℝ K) :
    FiniteHomology K := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · intro i
    rcases i with _ | n
    · have : IsEmpty (ZerothHomotopy (TopCat.of (∅ : Set E))) :=
        ⟨fun x => by induction x with | mk x => exact x.2⟩
      exact finbettiA_finite_homology_zero_of_finite_zerothHomotopy _
    · exact finbettiA_finite_homology_of_exactAt _ _
        (AlgebraicTopology.singularChainComplexFunctor_exactAt_of_totallyDisconnectedSpace
          _ _ _ _ (by omega))
  · have : Nonempty K := hne.to_subtype
    have : ContractibleSpace K := hK.contractibleSpace hne
    intro i
    rcases i with _ | n
    · have : PathConnectedSpace K :=
        isPathConnected_iff_pathConnectedSpace.mp (hK.isPathConnected hne)
      have : Subsingleton (ZerothHomotopy (TopCat.of K)) := ⟨fun x y => by
        induction x with | mk x => induction y with | mk y =>
          exact ZerothHomotopy.sound (PathConnectedSpace.somePath x y)⟩
      exact finbettiA_finite_homology_zero_of_finite_zerothHomotopy _
    · exact finbettiA_finite_homology_of_exactAt _ _
        (AlgebraicTopology.singularChainComplex_exactAt_of_contractible ℚ K _ (by omega))

section MVNat

open CategoryTheory.Limits
variable {X X' : TopCat.{0}} (f : X ⟶ X') (U V : Set X) (U' V' : Set X')
  (hU : U ⊆ f ⁻¹' U') (hV : V ⊆ f ⁻¹' V')

/-- The restriction `S → S'` of a continuous map `f : X → X'` with `S ⊆ f⁻¹(S')`.

Source: Hatcher, *Algebraic Topology*, §2.1 (maps of pairs of spaces and the maps they induce). -/
def finbettiA_res (S : Set X) (S' : Set X') (h : S ⊆ f ⁻¹' S') :
    TopCat.of S ⟶ TopCat.of S' :=
  TopCat.ofHom ⟨fun x => ⟨f x.1, h x.2⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

example (S : Set X) (S' : Set X') (h : S ⊆ f ⁻¹' S') (x : S) :
    ((finbettiA_res f S S' h x : S') : X') = f x :=
  rfl

theorem finbettiA_res_inter_sub (hU : U ⊆ f ⁻¹' U') (hV : V ⊆ f ⁻¹' V') : U ∩ V ⊆ f ⁻¹' (U' ∩ V') :=
  fun _ hx => ⟨hU hx.1, hV hx.2⟩

/-- The map of two-subset small singular sets induced by `f` when `f` maps `U` into `U'` and `V`
into `V'`, glued from the restrictions along the Mayer–Vietoris pushout square.

Source: Hatcher, *Algebraic Topology*, §2.1, Proposition 2.21 (chains small for a cover are
carried to chains small for a cover containing the images). -/
def finbettiA_smallMap :
    TwoSubsetSmallSingularSet X U V ⟶ TwoSubsetSmallSingularSet X' U' V' :=
  (subsetSmallSingularSquare_isPushout X U V).desc
    (TopCat.toSSet.map (finbettiA_res f U U' hU) ≫ subsetLeftToSmallSingularSet X' U' V')
    (TopCat.toSSet.map (finbettiA_res f V V' hV) ≫ subsetRightToSmallSingularSet X' U' V') (by
      rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
      have h1 : subsetIntersectionToLeft X U V ≫ finbettiA_res f U U' hU =
          finbettiA_res f (U ∩ V) (U' ∩ V') (finbettiA_res_inter_sub f U V U' V' hU hV) ≫
            subsetIntersectionToLeft X' U' V' := rfl
      have h2 : subsetIntersectionToRight X U V ≫ finbettiA_res f V V' hV =
          finbettiA_res f (U ∩ V) (U' ∩ V') (finbettiA_res_inter_sub f U V U' V' hU hV) ≫
            subsetIntersectionToRight X' U' V' := rfl
      rw [h1, h2, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
        (subsetSmallSingularSquare_isPushout X' U' V').w])

theorem finbettiA_left_ι (X : TopCat.{0}) (U V : Set X) :
    subsetLeftToSmallSingularSet X U V ≫
        (subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V).ι =
      TopCat.toSSet.map (topologicalSubsetInclusion X U) := by
  rfl

theorem finbettiA_right_ι (X : TopCat.{0}) (U V : Set X) :
    subsetRightToSmallSingularSet X U V ≫
        (subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V).ι =
      TopCat.toSSet.map (topologicalSubsetInclusion X V) := by
  rfl

theorem finbettiA_smallMap_ι :
    finbettiA_smallMap f U V U' V' hU hV ≫
        (subsetSingularSubcomplex X' U' ⊔ subsetSingularSubcomplex X' V').ι =
      (subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V).ι ≫ TopCat.toSSet.map f := by
  apply (subsetSmallSingularSquare_isPushout X U V).hom_ext
  · rw [← Category.assoc, finbettiA_smallMap, IsPushout.inl_desc, Category.assoc,
      finbettiA_left_ι, ← Category.assoc, finbettiA_left_ι, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl
  · rw [← Category.assoc, finbettiA_smallMap, IsPushout.inr_desc, Category.assoc,
      finbettiA_right_ι, ← Category.assoc, finbettiA_right_ι, ← Functor.map_comp,
      ← Functor.map_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The morphism of Mayer–Vietoris short exact chain sequences induced by `f` when `f` maps `U`
into `U'` and `V` into `V'`.

Source: Hatcher, *Algebraic Topology*, §2.2, subsection "Mayer–Vietoris Sequences", and §2.1
(a map of short exact sequences of chain complexes gives a map of long exact sequences). -/
def finbettiA_mvMap :
    singularMayerVietorisShortComplex X U V ⟶ singularMayerVietorisShortComplex X' U' V' where
  τ₁ := SSet.chainComplexMap (TopCat.toSSet.map
    (finbettiA_res f (U ∩ V) (U' ∩ V') (finbettiA_res_inter_sub f U V U' V' hU hV)))
    (ModuleCat.of ℚ ℚ)
  τ₂ := biprod.map
    (SSet.chainComplexMap (TopCat.toSSet.map (finbettiA_res f U U' hU)) (ModuleCat.of ℚ ℚ))
    (SSet.chainComplexMap (TopCat.toSSet.map (finbettiA_res f V V' hV)) (ModuleCat.of ℚ ℚ))
  τ₃ := SSet.chainComplexMap (finbettiA_smallMap f U V U' V' hU hV) (ModuleCat.of ℚ ℚ)
  comm₁₂ := by
    have e1 : SSet.chainComplexMap (TopCat.toSSet.map
          (finbettiA_res f (U ∩ V) (U' ∩ V') (finbettiA_res_inter_sub f U V U' V' hU hV)))
          (ModuleCat.of ℚ ℚ) ≫
        SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToLeft X' U' V'))
          (ModuleCat.of ℚ ℚ) =
        SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToLeft X U V))
          (ModuleCat.of ℚ ℚ) ≫
        SSet.chainComplexMap (TopCat.toSSet.map (finbettiA_res f U U' hU)) (ModuleCat.of ℚ ℚ) := by
      simp only [SSet.chainComplexMap, ← Functor.map_comp]
      rfl
    have e2 : SSet.chainComplexMap (TopCat.toSSet.map
          (finbettiA_res f (U ∩ V) (U' ∩ V') (finbettiA_res_inter_sub f U V U' V' hU hV)))
          (ModuleCat.of ℚ ℚ) ≫
        SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToRight X' U' V'))
          (ModuleCat.of ℚ ℚ) =
        SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToRight X U V))
          (ModuleCat.of ℚ ℚ) ≫
        SSet.chainComplexMap (TopCat.toSSet.map (finbettiA_res f V V' hV)) (ModuleCat.of ℚ ℚ) := by
      simp only [SSet.chainComplexMap, ← Functor.map_comp]
      rfl
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.map_fst]
      erw [biprod.lift_fst, biprod.lift_fst_assoc]
      exact e1
    · simp only [Category.assoc, biprod.map_snd]
      erw [biprod.lift_snd, biprod.lift_snd_assoc]
      rw [Preadditive.comp_neg, Preadditive.neg_comp, e2]
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [singularMayerVietorisShortComplex, CommSq.shortComplex_g,
        biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc]
      rw [← Functor.map_comp, ← Functor.map_comp, finbettiA_smallMap, IsPushout.inl_desc]
    · simp only [singularMayerVietorisShortComplex, CommSq.shortComplex_g,
        biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc]
      rw [← Functor.map_comp, ← Functor.map_comp, finbettiA_smallMap, IsPushout.inr_desc]

example : (finbettiA_mvMap f U V U' V' hU hV).τ₃ =
    SSet.chainComplexMap (finbettiA_smallMap f U V U' V' hU hV) (ModuleCat.of ℚ ℚ) :=
  rfl

example : finbettiA_smallMap f U V U' V' hU hV ≫
    (subsetSingularSubcomplex X' U' ⊔ subsetSingularSubcomplex X' V').ι =
      (subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V).ι ≫ TopCat.toSSet.map f :=
  finbettiA_smallMap_ι f U V U' V' hU hV

set_option backward.isDefEq.respectTransparency false in
theorem finbettiA_smallHomologyIso_naturality (hUo : IsOpen U) (hVo : IsOpen V)
    (hUV : U ∪ V = Set.univ) (hU'o : IsOpen U') (hV'o : IsOpen V') (hU'V' : U' ∪ V' = Set.univ)
    (k : ℕ) :
    (twoSubsetSmallHomologyIso X U V hUo hVo hUV k).inv ≫
        HomologicalComplex.homologyMap (finbettiA_mvMap f U V U' V' hU hV).τ₃ k =
      HomologicalComplex.homologyMap (SSet.chainComplexMap (TopCat.toSSet.map f)
          (ModuleCat.of ℚ ℚ)) k ≫
        (twoSubsetSmallHomologyIso X' U' V' hU'o hV'o hU'V' k).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  simp only [twoSubsetSmallHomologyIso, asIso_hom, ← HomologicalComplex.homologyMap_comp]
  congr 1
  simp only [finbettiA_mvMap, twoSubsetSmallChainInclusion, SSet.chainComplexMap,
    ← Functor.map_comp]
  rw [finbettiA_smallMap_ι]

set_option backward.isDefEq.respectTransparency false in
theorem finbettiA_boundary_naturality (hUo : IsOpen U) (hVo : IsOpen V)
    (hUV : U ∪ V = Set.univ) (hU'o : IsOpen U') (hV'o : IsOpen V') (hU'V' : U' ∪ V' = Set.univ)
    (n : ℕ) :
    singularMayerVietorisBoundary X U V hUo hVo hUV n ≫
        HomologicalComplex.homologyMap (finbettiA_mvMap f U V U' V' hU hV).τ₁ n =
      HomologicalComplex.homologyMap (SSet.chainComplexMap (TopCat.toSSet.map f)
          (ModuleCat.of ℚ ℚ)) (n + 1) ≫
        singularMayerVietorisBoundary X' U' V' hU'o hV'o hU'V' n := by
  simp only [singularMayerVietorisBoundary, Category.assoc]
  rw [HomologicalComplex.HomologySequence.δ_naturality (finbettiA_mvMap f U V U' V' hU hV)
    (singularMayerVietorisShortComplex_shortExact X U V)
    (singularMayerVietorisShortComplex_shortExact X' U' V'), ← Category.assoc,
    ← Category.assoc, finbettiA_smallHomologyIso_naturality]

end MVNat

theorem finbettiA_homologyMap_comp_apply {A B C : TopCat.{0}} (n : ℕ) (g : A ⟶ B) (h : B ⟶ C)
    (y : Homology ℚ A n) :
    homologyMap ℚ n h (homologyMap ℚ n g y) = homologyMap ℚ n (g ≫ h) y := by
  simp only [homologyMap, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

set_option backward.isDefEq.respectTransparency false in
theorem finbetti_subsetMayerVietorisBoundary_naturality_aux {Y : Type} [TopologicalSpace Y]
    {V₁ V₂ W₁ W₂ : Set Y} (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂) (hW₁ : IsOpen W₁)
    (hW₂ : IsOpen W₂) (h₁ : V₁ ⊆ W₁) (h₂ : V₂ ⊆ W₂) (n : ℕ)
    (x : Homology ℚ (TopCat.of ↥(V₁ ∪ V₂)) (n + 1)) :
    subsetMayerVietorisBoundary hW₁ hW₂ n
        (homologyMap ℚ (n + 1) (subsetInclusionHom (Set.union_subset_union h₁ h₂)) x) =
      homologyMap ℚ n (subsetInclusionHom (Set.inter_subset_inter h₁ h₂))
        (subsetMayerVietorisBoundary hV₁ hV₂ n x) := by
  have key := finbettiA_boundary_naturality
    (subsetInclusionHom (Set.union_subset_union h₁ h₂)) (subsetUnionLeft V₁ V₂)
    (subsetUnionRight V₁ V₂) (subsetUnionLeft W₁ W₂) (subsetUnionRight W₁ W₂)
    (fun _ hp => h₁ hp) (fun _ hp => h₂ hp) (hV₁.preimage continuous_subtype_val)
    (hV₂.preimage continuous_subtype_val) (subsetUnionLeft_union_right V₁ V₂)
    (hW₁.preimage continuous_subtype_val) (hW₂.preimage continuous_subtype_val)
    (subsetUnionLeft_union_right W₁ W₂) n
  simp only [subsetMayerVietorisBoundary, LinearMap.comp_apply]
  change homologyMap ℚ n (subsetOverlapHom W₁ W₂)
      ((HomologicalComplex.homologyMap (SSet.chainComplexMap (TopCat.toSSet.map
        (subsetInclusionHom (Set.union_subset_union h₁ h₂))) (ModuleCat.of ℚ ℚ)) (n + 1) ≫
        singularMayerVietorisBoundary _ _ _ _ _ _ n).hom x) = _
  rw [← key, ModuleCat.hom_comp, LinearMap.comp_apply]
  change homologyMap ℚ n (subsetOverlapHom W₁ W₂) (homologyMap ℚ n (finbettiA_res
    (subsetInclusionHom (Set.union_subset_union h₁ h₂)) _ _
    (finbettiA_res_inter_sub _ _ _ _ _ (fun _ hp => h₁ hp) (fun _ hp => h₂ hp))) _) = _
  rw [finbettiA_homologyMap_comp_apply, finbettiA_homologyMap_comp_apply]
  rfl

theorem fb_homologyMap_comp_apply {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ)
    (x : Homology ℚ X n) :
    homologyMap ℚ n g (homologyMap ℚ n f x) = homologyMap ℚ n (f ≫ g) x := by
  rw [homologyMap_comp]; rfl

theorem fb_homologyMap_eq_zero_of_retract {X Y : TopCat} (f : X ⟶ Y) (g : Y ⟶ X)
    (h : f ≫ g = 𝟙 X) (n : ℕ) {x : Homology ℚ X n} (hx : homologyMap ℚ n f x = 0) :
    x = 0 := by
  have := congrArg (homologyMap ℚ n g) hx
  rwa [fb_homologyMap_comp_apply, h, homologyMap_id, map_zero] at this

open CategoryTheory.Limits in
theorem finbetti_subsetMayerVietoris_exact_aux {Y : Type} [TopologicalSpace Y] {U V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) (y : Homology ℚ (TopCat.of ↥(U ∪ V)) (n + 1))
    (hy : subsetMayerVietorisBoundary hU hV n y = 0) :
    ∃ (a : Homology ℚ (TopCat.of U) (n + 1)) (b : Homology ℚ (TopCat.of V) (n + 1)),
      y = homologyMap ℚ (n + 1) (subsetInclusionHom Set.subset_union_left) a +
        homologyMap ℚ (n + 1) (subsetInclusionHom Set.subset_union_right) b := by
  have hU' : IsOpen (subsetUnionLeft U V) := hU.preimage continuous_subtype_val
  have hV' : IsOpen (subsetUnionRight U V) := hV.preimage continuous_subtype_val
  have h0 : (singularMayerVietorisBoundary (TopCat.of ↥(U ∪ V)) (subsetUnionLeft U V)
      (subsetUnionRight U V) hU' hV' (subsetUnionLeft_union_right U V) n).hom y = 0 := by
    let g : TopCat.of ↥(U ∩ V) ⟶
        TopCat.of ↥(subsetUnionLeft U V ∩ subsetUnionRight U V) :=
      TopCat.ofHom ⟨fun p => ⟨⟨p.1, Or.inl p.2.1⟩, p.2.1, p.2.2⟩, by fun_prop⟩
    exact fb_homologyMap_eq_zero_of_retract (subsetOverlapHom U V) g (by ext; rfl) n hy
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (singularMayerVietoris_exact_ambient (TopCat.of ↥(U ∪ V)) (subsetUnionLeft U V)
      (subsetUnionRight U V) hU' hV' (subsetUnionLeft_union_right U V) n) y h0
  let φU : TopCat.of ↥(subsetUnionLeft U V) ⟶ TopCat.of U :=
    TopCat.ofHom ⟨fun p => ⟨p.1.1, p.2⟩, by fun_prop⟩
  let φV : TopCat.of ↥(subsetUnionRight U V) ⟶ TopCat.of V :=
    TopCat.ofHom ⟨fun p => ⟨p.1.1, p.2⟩, by fun_prop⟩
  let e := singularMayerVietorisHomologySumIso (TopCat.of ↥(U ∪ V)) (subsetUnionLeft U V)
    (subsetUnionRight U V) (n + 1)
  let w := e.hom z
  refine ⟨homologyMap ℚ (n + 1) φU (biprod.fst (C := ModuleCat ℚ) w),
    homologyMap ℚ (n + 1) φV (biprod.snd (C := ModuleCat ℚ) w), ?_⟩
  rw [fb_homologyMap_comp_apply, fb_homologyMap_comp_apply]
  have key := congrArg (fun f => f.hom w)
    (singularMayerVietoris_sum_map_eq (TopCat.of ↥(U ∪ V)) (subsetUnionLeft U V)
      (subsetUnionRight U V) (n + 1))
  simp only [biprod.desc_eq] at key
  have hzw : z = e.inv w := by simp [w]
  rw [← hz, hzw]
  exact key.trans rfl

/-- The projection from singular `0`-chains onto `H_0(X; ℚ)` (every `0`-chain is a cycle).

Source: Hatcher, *Algebraic Topology*, §2.1 (`H_0` is the quotient of `C_0` by boundaries). -/
def fbChainToH0 (X : TopCat) :
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).X 0 ⟶ Homology ℚ X 0 :=
  ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).pOpcycles 0 ≫
    ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).isoHomologyι₀.inv

example (X : TopCat) (c : ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).X 0) :
    homologyMap ℚ 0 (𝟙 X) (fbChainToH0 X c) = fbChainToH0 X c := by
  rw [homologyMap_id]; rfl

theorem fbChainToH0_naturality {X Y : TopCat} (f : X ⟶ Y) :
    fbChainToH0 X ≫ ModuleCat.ofHom (homologyMap ℚ 0 f) =
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f 0 ≫
        fbChainToH0 Y := by
  have h := congrArg
    (fun g => ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).pOpcycles 0 ≫ g)
    (ChainComplex.isoHomologyι₀_inv_naturality
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)))
  simp only [HomologicalComplex.p_opcyclesMap_assoc] at h
  exact h

theorem fbChainToH0_naturality_apply {X Y : TopCat} (f : X ⟶ Y) (c) :
    homologyMap ℚ 0 f (fbChainToH0 X c) =
      fbChainToH0 Y ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℚ ℚ)).f 0 c) :=
  congrArg (fun g => g.hom c) (fbChainToH0_naturality f)

theorem fbChainToH0_surjective (X : TopCat) : Function.Surjective (fbChainToH0 X) := by
  rw [← ModuleCat.epi_iff_surjective]
  exact epi_comp (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).pOpcycles 0)
    (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℚ ℚ)).isoHomologyι₀.inv)

open scoped Simplicial in
theorem finbetti_subsetMayerVietoris_surjective_zero_aux {Y : Type} [TopologicalSpace Y]
    (U V : Set Y) (y : Homology ℚ (TopCat.of ↥(U ∪ V)) 0) :
    ∃ (a : Homology ℚ (TopCat.of U) 0) (b : Homology ℚ (TopCat.of V) 0),
      y = homologyMap ℚ 0 (subsetInclusionHom Set.subset_union_left) a +
        homologyMap ℚ 0 (subsetInclusionHom Set.subset_union_right) b := by
  set S := LinearMap.range (homologyMap ℚ 0 (subsetInclusionHom (Set.subset_union_left (s := U)
    (t := V)))) ⊔ LinearMap.range (homologyMap ℚ 0 (subsetInclusionHom
      (Set.subset_union_right (s := U) (t := V)))) with hS
  -- the class of every singular `0`-simplex lies in `S`
  have hpt : ∀ x : (TopCat.toSSet.obj (TopCat.of ↥(U ∪ V))) _⦋0⦌,
      fbChainToH0 _ ((SSet.ιChainComplex (R := ModuleCat.of ℚ ℚ) _ x).hom 1) ∈ S := by
    intro x
    let t₀ : Convexity.StdSimplex ℝ (Fin 1) := default
    have hall : ∀ W : Set ↥(U ∪ V), (TopCat.of ↥(U ∪ V)).toSSetObjEquiv _ x t₀ ∈ W →
        x ∈ (subsetSingularSubcomplex (TopCat.of ↥(U ∪ V)) W).obj _ := by
      intro W hW
      rw [mem_subsetSingularSubcomplex_iff]
      intro t
      rwa [Subsingleton.elim t t₀]
    have key : ∀ (W : Set Y) (hW : W ⊆ U ∪ V),
        (TopCat.of ↥(U ∪ V)).toSSetObjEquiv _ x t₀ ∈
          (Subtype.val ⁻¹' W : Set ↥(U ∪ V)) →
        fbChainToH0 _ ((SSet.ιChainComplex (R := ModuleCat.of ℚ ℚ) _ x).hom 1) ∈
          LinearMap.range (homologyMap ℚ 0 (subsetInclusionHom hW)) := by
      intro W hW hx
      obtain ⟨x', hx'⟩ := hall _ hx
      let φ : TopCat.of ↥(Subtype.val ⁻¹' W : Set ↥(U ∪ V)) ⟶ TopCat.of W :=
        TopCat.ofHom ⟨fun p => ⟨p.1.1, p.2⟩, by fun_prop⟩
      refine ⟨homologyMap ℚ 0 φ
        (fbChainToH0 _ ((SSet.ιChainComplex (R := ModuleCat.of ℚ ℚ) _ x').hom 1)), ?_⟩
      rw [fb_homologyMap_comp_apply, fbChainToH0_naturality_apply]
      congr 1
      rw [← hx']
      have := SSet.ι_chainComplexMap_f (R := ModuleCat.of ℚ ℚ)
        (f := TopCat.toSSet.map (φ ≫ subsetInclusionHom hW)) (x := x')
      exact (congrArg (fun g => g.hom 1) this)
    rcases ((TopCat.of ↥(U ∪ V)).toSSetObjEquiv _ x t₀).2 with h | h
    · exact Submodule.mem_sup_left (key U _ h)
    · exact Submodule.mem_sup_right (key V _ h)
  have hall : ∀ c, fbChainToH0 _ c ∈ S := by
    have h0 : fbChainToH0 (TopCat.of ↥(U ∪ V)) ≫ ModuleCat.ofHom S.mkQ = 0 := by
      refine SSet.chainComplex_hom_ext fun x => ?_
      ext
      have := hpt x
      rw [← Submodule.Quotient.mk_eq_zero] at this
      exact this
    intro c
    have h1 : S.mkQ (fbChainToH0 _ c) = 0 := congrArg (fun g => g.hom c) h0
    exact (Submodule.Quotient.mk_eq_zero S).1 h1
  obtain ⟨c, rfl⟩ := fbChainToH0_surjective _ y
  obtain ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.1 (hall c)
  exact ⟨a, b, hab.symm⟩

theorem finbetti_finiteHomology_union_aux {Y : Type} [TopologicalSpace Y] {U V : Set Y}
    (hU : IsOpen U) (hV : IsOpen V) (hfU : FiniteHomology U) (hfV : FiniteHomology V)
    (hfUV : FiniteHomology ↥(U ∩ V)) :
    FiniteHomology ↥(U ∪ V) := by
  intro i
  let L := (homologyMap ℚ i (subsetInclusionHom (Set.subset_union_left (s := U) (t := V)))).coprod
    (homologyMap ℚ i (subsetInclusionHom (Set.subset_union_right (s := U) (t := V))))
  have := hfU i
  have := hfV i
  have hL : (LinearMap.range L).FG := by
    rw [LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map L
  rw [Module.finite_def]
  cases i with
  | zero =>
    refine Submodule.FG.of_le hL fun y _ => ?_
    obtain ⟨a, b, rfl⟩ := finbetti_subsetMayerVietoris_surjective_zero_aux U V y
    exact ⟨(a, b), rfl⟩
  | succ n =>
    have := hfUV n
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (subsetMayerVietorisBoundary hU hV n)
      (Submodule.FG.of_le (Module.Finite.fg_top) le_top) (Submodule.FG.of_le hL ?_)
    rintro y ⟨-, hy⟩
    obtain ⟨a, b, rfl⟩ := finbetti_subsetMayerVietoris_exact_aux hU hV n y hy
    exact ⟨(a, b), rfl⟩

theorem finbetti_finiteHomology_iUnion_convex_aux {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {m : ℕ} (K : Fin m → Set E) (hopen : ∀ j, IsOpen (K j))
    (hconv : ∀ j, Convex ℝ (K j)) :
    FiniteHomology ↥(⋃ j, K j) := by
  induction m with
  | zero =>
    rw [Set.iUnion_of_empty]
    exact finbetti_finiteHomology_of_convex_aux convex_empty
  | succ m ih =>
    have hsplit : (⋃ j, K j) = (⋃ j : Fin m, K j.castSucc) ∪ K (Fin.last m) := by
      ext p
      simp only [Set.mem_iUnion, Set.mem_union]
      constructor
      · rintro ⟨j, hj⟩
        cases j using Fin.lastCases with
        | last => exact Or.inr hj
        | cast j => exact Or.inl ⟨j, hj⟩
      · rintro (⟨j, hj⟩ | hj)
        · exact ⟨_, hj⟩
        · exact ⟨_, hj⟩
    have hinter : (⋃ j : Fin m, K j.castSucc) ∩ K (Fin.last m) =
        ⋃ j : Fin m, (K j.castSucc ∩ K (Fin.last m)) := Set.iUnion_inter _ _
    rw [hsplit]
    refine finbetti_finiteHomology_union_aux (isOpen_iUnion fun j => hopen _) (hopen _)
      (ih _ (fun j => hopen _) (fun j => hconv _))
      (finbetti_finiteHomology_of_convex_aux (hconv _)) ?_
    rw [hinter]
    exact ih _ (fun j => (hopen _).inter (hopen _)) (fun j => (hconv _).inter (hconv _))

/-- Homology maps of nested inclusions compose. -/
theorem finbetti_homologyMap_inclusion_trans {Y : Type} [TopologicalSpace Y] {A B C : Set Y}
    (h₁ : A ⊆ B) (h₂ : B ⊆ C) (h₃ : A ⊆ C) (n : ℕ) (x : Homology ℚ (TopCat.of A) n) :
    homologyMap ℚ n (subsetInclusionHom h₂) (homologyMap ℚ n (subsetInclusionHom h₁) x) =
      homologyMap ℚ n (subsetInclusionHom h₃) x := by
  rw [← LinearMap.comp_apply, ← homologyMap_comp]
  rfl

/-- A subspace of a finite-dimensional subspace is finite-dimensional. -/
theorem finbetti_finite_of_le {P : Type*} [AddCommGroup P] [Module ℚ P] {N N' : Submodule ℚ P}
    (h : N ≤ N') [Module.Finite ℚ N'] : Module.Finite ℚ N :=
  Module.Finite.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

/-- If `∂` maps `G` to a finite-dimensional space and `φ` maps `G ∩ ker ∂` to one, then `φ` maps
`G` to a finite-dimensional space. -/
theorem finbetti_finite_map_of_ker {P Q R : Type*} [AddCommGroup P] [Module ℚ P]
    [AddCommGroup Q] [Module ℚ Q] [AddCommGroup R] [Module ℚ R] (φ : P →ₗ[ℚ] Q)
    (d : P →ₗ[ℚ] R) (G : Submodule ℚ P) (hG : Module.Finite ℚ (G.map d))
    (hK : Module.Finite ℚ ((G ⊓ LinearMap.ker d).map φ)) : Module.Finite ℚ (G.map φ) := by
  let dG : G →ₗ[ℚ] R := d ∘ₗ G.subtype
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.ker dG)
  have hr : LinearMap.range dG = G.map d := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hR : Module.Finite ℚ (LinearMap.range dG) := hr ▸ hG
  have hCf : Module.Finite ℚ C :=
    Module.Finite.equiv ((Submodule.quotientEquivOfIsCompl _ _ hC).symm.trans
      dG.quotKerEquivRange).symm
  have hCm : Module.Finite ℚ (C.map (φ ∘ₗ G.subtype)) := Module.Finite.map _ _
  refine finbetti_finite_of_le (N' := (G ⊓ LinearMap.ker d).map φ ⊔ C.map (φ ∘ₗ G.subtype)) ?_
  rintro _ ⟨p, hp, rfl⟩
  have hmem : (⟨p, hp⟩ : G) ∈ LinearMap.ker dG ⊔ C := by
    rw [hC.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨k, hk, c, hc, hkc⟩ := Submodule.mem_sup.1 hmem
  have hp' : p = (k : P) + (c : P) := by rw [← Submodule.coe_add, hkc]
  rw [hp', map_add]
  exact Submodule.add_mem_sup ⟨k, ⟨k.2, hk⟩, rfl⟩ ⟨c, hc, rfl⟩

set_option linter.unusedVariables false in
theorem finbetti_finiteHomologyImage_union_aux {Y : Type} [TopologicalSpace Y]
    {V₁ V₂ W₁ W₂ U₁ U₂ : Set Y} (hV₁ : IsOpen V₁) (hV₂ : IsOpen V₂) (hW₁ : IsOpen W₁)
    (hW₂ : IsOpen W₂) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hVW₁ : V₁ ⊆ W₁) (hVW₂ : V₂ ⊆ W₂)
    (hWU₁ : W₁ ⊆ U₁) (hWU₂ : W₂ ⊆ U₂) (h₁ : FiniteHomologyImage hWU₁)
    (h₂ : FiniteHomologyImage hWU₂) (h₁₂ : FiniteHomologyImage (Set.inter_subset_inter hVW₁ hVW₂)) :
    FiniteHomologyImage
      (Set.union_subset_union (hVW₁.trans hWU₁) (hVW₂.trans hWU₂)) := by
  classical
  intro i
  -- `S` is the sum of the images of `H(W_k) → H(U_k) → H(U₁ ∪ U₂)`.
  let S : Submodule ℚ (Homology ℚ (TopCat.of ↥(U₁ ∪ U₂)) i) :=
    (LinearMap.range (homologyMap ℚ i (subsetInclusionHom hWU₁))).map
        (homologyMap ℚ i (subsetInclusionHom (Set.subset_union_left (t := U₂)))) ⊔
      (LinearMap.range (homologyMap ℚ i (subsetInclusionHom hWU₂))).map
        (homologyMap ℚ i (subsetInclusionHom (Set.subset_union_right (s := U₁))))
  have hS : Module.Finite ℚ S := by
    have := h₁ i
    have := h₂ i
    exact Submodule.finite_sup _ _
  have hWU : W₁ ∪ W₂ ⊆ U₁ ∪ U₂ := Set.union_subset_union hWU₁ hWU₂
  have hVW : V₁ ∪ V₂ ⊆ W₁ ∪ W₂ := Set.union_subset_union hVW₁ hVW₂
  -- Classes on `W₁ ∪ W₂` that are sums from `W₁` and `W₂` map into `S`.
  have hsum : ∀ (a : Homology ℚ (TopCat.of W₁) i) (b : Homology ℚ (TopCat.of W₂) i),
      homologyMap ℚ i (subsetInclusionHom hWU)
        (homologyMap ℚ i (subsetInclusionHom Set.subset_union_left) a +
          homologyMap ℚ i (subsetInclusionHom Set.subset_union_right) b) ∈ S := by
    intro a b
    rw [map_add, finbetti_homologyMap_inclusion_trans _ _ (hWU₁.trans Set.subset_union_left),
      finbetti_homologyMap_inclusion_trans _ _ (hWU₂.trans Set.subset_union_right),
      ← finbetti_homologyMap_inclusion_trans hWU₁ Set.subset_union_left,
      ← finbetti_homologyMap_inclusion_trans hWU₂ Set.subset_union_right]
    exact Submodule.add_mem_sup ⟨_, ⟨a, rfl⟩, rfl⟩ ⟨_, ⟨b, rfl⟩, rfl⟩
  cases i with
  | zero =>
    refine finbetti_finite_of_le (N' := S) ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨a, b, hab⟩ := finbetti_subsetMayerVietoris_surjective_zero_aux W₁ W₂
      (homologyMap ℚ 0 (subsetInclusionHom hVW) x)
    rw [← finbetti_homologyMap_inclusion_trans hVW hWU, hab]
    exact hsum a b
  | succ n =>
    let d := subsetMayerVietorisBoundary hW₁ hW₂ n
    let φ := homologyMap ℚ (n + 1) (subsetInclusionHom hWU)
    let G := (LinearMap.range (homologyMap ℚ n
      (subsetInclusionHom (Set.inter_subset_inter hVW₁ hVW₂)))).comap d
    have hG : Module.Finite ℚ (G.map d) := by
      have := h₁₂ n
      exact finbetti_finite_of_le (Submodule.map_comap_le _ _)
    have hK : Module.Finite ℚ ((G ⊓ LinearMap.ker d).map φ) := by
      refine finbetti_finite_of_le (N' := S) ?_
      rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
      obtain ⟨a, b, hab⟩ := finbetti_subsetMayerVietoris_exact_aux hW₁ hW₂ n y hy
      rw [hab]
      exact hsum a b
    have := finbetti_finite_map_of_ker φ d G hG hK
    refine finbetti_finite_of_le (N' := G.map φ) ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨homologyMap ℚ (n + 1) (subsetInclusionHom hVW) x, ?_,
      finbetti_homologyMap_inclusion_trans hVW hWU _ _ x⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    rw [finbetti_subsetMayerVietorisBoundary_naturality_aux hV₁ hV₂ hW₁ hW₂ hVW₁ hVW₂ n x]
    exact ⟨_, rfl⟩

/-- `FiniteHomologyImage` passes to smaller sources and larger targets. -/
theorem finbetti_finiteHomologyImage_mono {Y : Type} [TopologicalSpace Y] {A A' B' B : Set Y}
    (hAA' : A ⊆ A') (hA'B' : A' ⊆ B') (hB'B : B' ⊆ B) (hAB : A ⊆ B)
    (h : FiniteHomologyImage hA'B') : FiniteHomologyImage hAB := by
  intro i
  have := h i
  refine finbetti_finite_of_le (N' := (LinearMap.range (homologyMap ℚ i
    (subsetInclusionHom hA'B'))).map (homologyMap ℚ i (subsetInclusionHom hB'B))) ?_
  rintro _ ⟨a, rfl⟩
  refine ⟨homologyMap ℚ i (subsetInclusionHom hA'B')
    (homologyMap ℚ i (subsetInclusionHom hAA') a), ⟨_, rfl⟩, ?_⟩
  rw [finbetti_homologyMap_inclusion_trans hAA' hA'B' (hAA'.trans hA'B'),
    finbetti_homologyMap_inclusion_trans _ hB'B hAB]

/-- Finite homology of the source gives a finite image. -/
theorem finbetti_finiteHomologyImage_of_finiteHomology {Y : Type} [TopologicalSpace Y]
    {V U : Set Y} (h : V ⊆ U) (hV : FiniteHomology V) : FiniteHomologyImage h := by
  intro i
  have := hV i
  exact Module.Finite.range _

/-- Finite homology is invariant under homeomorphisms. -/
theorem finbetti_finiteHomology_of_homeomorph {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (h : FiniteHomology B) : FiniteHomology A := by
  intro i
  have := h i
  exact Module.Finite.equiv
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℚ) i).obj
      (ModuleCat.of ℚ ℚ)).mapIso
      (TopCat.isoOfHomeo (X := TopCat.of A) (Y := TopCat.of B) e)).toLinearEquiv.symm

set_option linter.unusedVariables false in
theorem finbetti_finiteHomologyImage_chart_aux {M E : Type} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E M] {V U : Set M}
    (hV : IsOpen V) (hU : IsOpen U) (hcpt : IsCompact (closure V)) (hVU : closure V ⊆ U) (x : M)
    (hUx : U ⊆ (chartAt E x).source) :
    FiniteHomologyImage (subset_closure.trans hVU) := by
  let e := chartAt E x
  have hVs : closure V ⊆ e.source := hVU.trans hUx
  have hKc : IsCompact (e '' closure V) := hcpt.image_of_continuousOn (e.continuousOn.mono hVs)
  have hO : IsOpen (e '' U) := e.isOpen_image_of_subset_source hU hUx
  have hball : ∀ y ∈ e '' closure V, ∃ r > 0, Metric.ball y r ⊆ e '' U :=
    fun y hy => Metric.isOpen_iff.1 hO y (Set.image_mono hVU hy)
  choose r hr hrU using hball
  obtain ⟨t, ht⟩ := hKc.elim_nhds_subcover' (fun y hy => Metric.ball y (r y hy))
    (fun y hy => Metric.ball_mem_nhds y (hr y hy))
  let c : Fin t.card → ↥(e '' closure V) := fun j => t.equivFin.symm j
  let K : Fin t.card → Set E := fun j => Metric.ball (c j : E) (r (c j) (c j).2)
  have hKB : e '' closure V ⊆ ⋃ j, K j := by
    intro y hy
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (ht hy)
    refine Set.mem_iUnion.2 ⟨t.equivFin ⟨z, hz⟩, ?_⟩
    simpa [K, c] using hyz
  have hBU : (⋃ j, K j) ⊆ e '' U := Set.iUnion_subset fun j => hrU _ _
  let W : Set M := e.source ∩ e ⁻¹' (⋃ j, K j)
  have hVW : V ⊆ W := fun v hv =>
    ⟨hVs (subset_closure hv), hKB ⟨v, subset_closure hv, rfl⟩⟩
  have hWU : W ⊆ U := by
    rintro w ⟨hws, hwB⟩
    obtain ⟨u, hu, hue⟩ := hBU hwB
    rw [← e.injOn (hUx hu) hws hue]
    exact hu
  have himage : e '' W = ⋃ j, K j := by
    rw [Set.image_inter_preimage, e.image_source_eq_target]
    refine Set.inter_eq_right.2 (hBU.trans ?_)
    rw [← e.image_source_eq_target]
    exact Set.image_mono hUx
  have hW : FiniteHomology W := finbetti_finiteHomology_of_homeomorph
    (e.homeomorphOfImageSubsetSource Set.inter_subset_left himage)
    (finbetti_finiteHomology_iUnion_convex_aux K (fun _ => Metric.isOpen_ball)
      (fun _ => convex_ball _ _))
  exact finbetti_finiteHomologyImage_mono hVW hWU subset_rfl _
    (finbetti_finiteHomologyImage_of_finiteHomology hWU hW)

theorem finbetti_finiteHomologyImage_of_subset_charts_aux {M E : Type} [TopologicalSpace M]
    [T2Space M] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] {m : ℕ} (x : Fin m → M) {V U : Set M} (hV : IsOpen V) (hU : IsOpen U)
    (hcpt : IsCompact (closure V)) (hVU : closure V ⊆ U)
    (hcover : closure V ⊆ ⋃ j, (chartAt E (x j)).source) :
    FiniteHomologyImage (subset_closure.trans hVU) := by
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  induction m generalizing V U with
  | zero =>
    have hV0 : V = ∅ := Set.subset_eq_empty (subset_closure.trans hcover) (by simp)
    subst hV0
    have : IsEmpty (∅ : Set M) := Set.isEmpty_coe_sort.2 rfl
    have : IsEmpty (∅ : Set E) := Set.isEmpty_coe_sort.2 rfl
    exact finbetti_finiteHomologyImage_of_finiteHomology _
      (finbetti_finiteHomology_of_homeomorph (Homeomorph.empty (Y := (∅ : Set E)))
        (finbetti_finiteHomology_of_convex_aux convex_empty))
  | succ m ih =>
    let S₁ : Set M := ⋃ j : Fin m, (chartAt E (x j.castSucc)).source
    let S₂ : Set M := (chartAt E (x (Fin.last m))).source
    have hS₁ : IsOpen S₁ := isOpen_iUnion fun j => (chartAt E _).open_source
    have hS₂ : IsOpen S₂ := (chartAt E _).open_source
    let U₁ := U ∩ S₁
    let U₂ := U ∩ S₂
    have hU₁ : IsOpen U₁ := hU.inter hS₁
    have hU₂ : IsOpen U₂ := hU.inter hS₂
    have hKU : closure V ⊆ U₁ ∪ U₂ := by
      intro y hy
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hcover hy)
      induction j using Fin.lastCases with
      | last => exact Or.inr ⟨hVU hy, hj⟩
      | cast j => exact Or.inl ⟨hVU hy, Set.mem_iUnion.2 ⟨j, hj⟩⟩
    obtain ⟨K₁, K₂, hK₁, hK₂, hK₁U, hK₂U, hK⟩ := hcpt.binary_compact_cover hU₁ hU₂ hKU
    obtain ⟨W₁, hW₁, hKW₁, hWU₁, hWc₁⟩ := exists_open_between_and_isCompact_closure hK₁ hU₁ hK₁U
    obtain ⟨W₂, hW₂, hKW₂, hWU₂, hWc₂⟩ := exists_open_between_and_isCompact_closure hK₂ hU₂ hK₂U
    obtain ⟨V₁, hV₁, hKV₁, hVW₁, hVc₁⟩ :=
      exists_open_between_and_isCompact_closure hK₁ hW₁ hKW₁
    obtain ⟨V₂, hV₂, hKV₂, hVW₂, hVc₂⟩ :=
      exists_open_between_and_isCompact_closure hK₂ hW₂ hKW₂
    have h₁ : FiniteHomologyImage (subset_closure.trans hWU₁) :=
      ih (fun j => x j.castSucc) hW₁ hU₁ hWc₁ hWU₁ (hWU₁.trans Set.inter_subset_right)
    have h₂ : FiniteHomologyImage (subset_closure.trans hWU₂) :=
      finbetti_finiteHomologyImage_chart_aux hW₂ hU₂ hWc₂ hWU₂ (x (Fin.last m))
        Set.inter_subset_right
    have hVW : closure (V₁ ∩ V₂) ⊆ W₁ ∩ W₂ :=
      (closure_inter_subset_inter_closure _ _).trans (Set.inter_subset_inter hVW₁ hVW₂)
    have h₁₂ : FiniteHomologyImage (subset_closure.trans hVW) :=
      finbetti_finiteHomologyImage_chart_aux (hV₁.inter hV₂) (hW₁.inter hW₂)
        (hVc₂.of_isClosed_subset isClosed_closure
          ((closure_mono Set.inter_subset_right)))
        hVW (x (Fin.last m))
        (Set.inter_subset_right.trans ((subset_closure.trans hWU₂).trans Set.inter_subset_right))
    have h := finbetti_finiteHomologyImage_union_aux hV₁ hV₂ hW₁ hW₂ hU₁ hU₂
      (subset_closure.trans hVW₁) (subset_closure.trans hVW₂) (subset_closure.trans hWU₁)
      (subset_closure.trans hWU₂) h₁ h₂ h₁₂
    have hVV : V ⊆ V₁ ∪ V₂ := subset_closure.trans
      (hK ▸ Set.union_subset_union hKV₁ hKV₂)
    exact finbetti_finiteHomologyImage_mono hVV _
      (Set.union_subset Set.inter_subset_left Set.inter_subset_left) _ h

theorem finbetti_finiteHomology_of_compact_aux {M : Type} (E : Type) [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E M] :
    FiniteHomology M := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x : M => (chartAt E x).source)
    (fun x => (chartAt E x).open_source) (fun x _ => Set.mem_iUnion.2 ⟨x, mem_chart_source E x⟩)
  have hcl : closure (Set.univ : Set M) ⊆ Set.univ := Set.subset_univ _
  have hcover : closure (Set.univ : Set M) ⊆
      ⋃ j, (chartAt E ((s.equivFin.symm j : M))).source := by
    intro y _
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
    exact Set.mem_iUnion.2 ⟨s.equivFin ⟨x, hx⟩, by simpa using hy⟩
  have h := finbetti_finiteHomologyImage_of_subset_charts_aux (E := E)
    (fun j => (s.equivFin.symm j : M)) isOpen_univ isOpen_univ
    (by rw [closure_univ]; exact isCompact_univ) hcl hcover
  have hid : subsetInclusionHom (subset_closure.trans hcl) = 𝟙 (TopCat.of (Set.univ : Set M)) :=
    rfl
  let e : TopCat.of (Set.univ : Set M) ≅ TopCat.of M :=
    TopCat.isoOfHomeo (Homeomorph.Set.univ M)
  intro i
  have hi := h i
  rw [hid, homologyMap, CategoryTheory.Functor.map_id, ModuleCat.hom_id, LinearMap.range_id] at hi
  have hi' : Module.Finite ℚ (Homology ℚ (TopCat.of (Set.univ : Set M)) i) :=
    Module.Finite.equiv (LinearEquiv.ofTop ⊤ rfl)
  exact Module.Finite.equiv
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℚ) i).obj
      (ModuleCat.of ℚ ℚ)).mapIso e).toLinearEquiv

theorem finbetti_finite_cohomology_of_finite_homology_aux (Y : Type) [TopologicalSpace Y]
    (n : ℕ) (h : Module.Finite ℚ (Homology ℚ (TopCat.of Y) n)) :
    Module.Finite ℚ (Cohomology ℚ (TopCat.of Y) n) :=
  Module.Finite.equiv (cohomologyEquivDualHomology ℚ (TopCat.of Y) n).symm

theorem finbetti_finiteBetti_aux (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    FiniteBetti X := by
  have (U : Opens (ComplexPoint X)) : ParacompactSpace U := openParacompactSpace X U
  refine ⟨fun n => ?_⟩
  obtain ⟨e⟩ := HodgeLean.Foundations.spec_fieldCohomology_linearEquiv_singular ℚ X n
  have := finbetti_finite_cohomology_of_finite_homology_aux _ n
    (finbetti_finiteHomology_of_compact_aux (M := ComplexPoint X) (Fin (dim X.left) → ℂ) n)
  exact Module.Finite.equiv ((HQ.linearEquiv X n).trans e).symm

theorem finbetti_not_finite_homology_zero_of_infinite_discrete_aux (Y : Type)
    [TopologicalSpace Y] [DiscreteTopology Y] [Infinite Y] :
    ¬ Module.Finite ℚ (Homology ℚ (TopCat.of Y) 0) := by
  classical
  intro h
  have hinj : Function.Injective (ZerothHomotopy.mk (X := TopCat.of Y)) := by
    intro a b hab
    obtain ⟨γ⟩ := Quotient.exact hab
    have hc : IsPreconnected (Set.range γ) := isPreconnected_range γ.continuous
    simpa using hc.subsingleton (Set.mem_range_self 0) (Set.mem_range_self 1)
  have : Infinite (ZerothHomotopy (TopCat.of Y)) := Infinite.of_injective _ hinj
  have e := (TopCat.singularHomology₀Iso (TopCat.of Y) (ModuleCat.of ℚ ℚ) ≪≫
    ModuleCat.coprodIsoDirectSum _).toLinearEquiv
  have h2 : Module.Finite ℚ (ZerothHomotopy (TopCat.of Y) →₀ ℚ) :=
    Module.Finite.equiv (e.trans (finsuppLequivDFinsupp ℚ).symm)
  rw [Module.finite_finsupp_self_iff] at h2
  rcases h2 with h2 | h2
  · exact zero_ne_one (Subsingleton.elim (0 : ℚ) 1)
  · exact not_finite (ZerothHomotopy (TopCat.of Y))

end HodgeLean.RealDefs
