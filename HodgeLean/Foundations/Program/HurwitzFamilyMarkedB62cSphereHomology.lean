import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.SphereSimplicialHomology

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory CategoryTheory.Limits Simplicial HomologicalComplex AlgebraicTopology.Singular
open scoped Simplicial
variable (R : Type) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
abbrev b6m_standardSimplexSuccNormalizedCoefficientChains (n : ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  (Δ[n + 2] : SSet.{0}).normalizedChainComplex (ModuleCat.of R R)

set_option backward.isDefEq.respectTransparency false in
abbrev b6m_standardSphereSuccNormalizedCoefficientChains (n : ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  (∂Δ[n + 2] : SSet.{0}).normalizedChainComplex (ModuleCat.of R R)

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSimplexSucc_normalizedChains_exactAt (n k : ℕ) (hk : k ≠ 0) :
    (b6m_standardSimplexSuccNormalizedCoefficientChains R n).ExactAt k := by
  let ed := (SSet.Augmented.StandardSimplex.extraDegeneracy
    (SimplexCategory.mk (n + 2))).map ((sigmaConst.obj (ModuleCat.of R R)))
  let e := ed.homotopyEquiv
  have hchains : ((Δ[n + 2] : SSet.{0}).chainComplex
      (ModuleCat.of R R)).ExactAt k :=
    (exactAt_iff_of_quasiIsoAt e.hom k).mpr (exactAt_single_obj _ _ _ _ hk)
  exact (exactAt_iff_of_quasiIsoAt
    ((Δ[n + 2] : SSet.{0}).toNormalizedChainComplex (ModuleCat.of R R)) k).mp hchains

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSimplexSuccNormalizedChainsToBoundary (n k : ℕ) (hk : k < n + 2) :
    (b6m_standardSimplexSuccNormalizedCoefficientChains R n).X k ⟶
      (b6m_standardSphereSuccNormalizedCoefficientChains R n).X k :=
  ((Δ[n + 2] : SSet.{0}).isColimitCofanNormalizedChainComplex
    (ModuleCat.of R R) k).desc
      (Cofan.mk _ (fun x ↦
        (∂Δ[n + 2] : SSet.{0}).ιNormalizedChainComplex
          ⟨x.1, by rw [SSet.boundary_obj_eq_univ k (n + 2) hk]; trivial⟩))

set_option backward.isDefEq.respectTransparency false in
lemma b6m_ιNormalizedChainComplex_standardSimplexSuccNormalizedChainsToBoundary
    (n k : ℕ) (hk : k < n + 2)
    (x : (Δ[n + 2] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk k)))
    (hx : x ∈ (Δ[n + 2] : SSet.{0}).nonDegenerate k) :
    (Δ[n + 2] : SSet.{0}).ιNormalizedChainComplex x ≫
        b6m_standardSimplexSuccNormalizedChainsToBoundary R n k hk =
      (∂Δ[n + 2] : SSet.{0}).ιNormalizedChainComplex
        ⟨x, by rw [SSet.boundary_obj_eq_univ k (n + 2) hk]; trivial⟩ :=
  ((Δ[n + 2] : SSet.{0}).isColimitCofanNormalizedChainComplex
    (ModuleCat.of R R) k).fac
      (Cofan.mk _ (fun x ↦
        (∂Δ[n + 2] : SSet.{0}).ιNormalizedChainComplex
          ⟨x.1, by rw [SSet.boundary_obj_eq_univ k (n + 2) hk]; trivial⟩)) ⟨x, hx⟩

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSphereSuccNormalizedChainsXIsoStandard
    (n k : ℕ) (hk : k < n + 2) :
    (b6m_standardSphereSuccNormalizedCoefficientChains R n).X k ≅
      (b6m_standardSimplexSuccNormalizedCoefficientChains R n).X k where
  hom := (SSet.normalizedChainComplexMap
    (SSet.boundary (n + 2) : SSet.Subcomplex (Δ[n + 2] : SSet.{0})).ι
      (ModuleCat.of R R)).f k
  inv := b6m_standardSimplexSuccNormalizedChainsToBoundary R n k hk
  hom_inv_id := by
    apply (∂Δ[n + 2] : SSet.{0}).normalizedChainComplex_hom_ext
    intro x hx
    rw [← Category.assoc, SSet.ι_normalizedChainComplexMap_f, Category.comp_id]
    have hx' : x.1 ∈ (Δ[n + 2] : SSet.{0}).nonDegenerate k := by
      rwa [← (SSet.boundary (n + 2)).mem_nonDegenerate_iff x]
    convert b6m_ιNormalizedChainComplex_standardSimplexSuccNormalizedChainsToBoundary R
      n k hk x.1 hx' using 1 <;> try rfl
  inv_hom_id := by
    apply (Δ[n + 2] : SSet.{0}).normalizedChainComplex_hom_ext
    intro x hx
    rw [← Category.assoc, Category.comp_id]
    rw [b6m_ιNormalizedChainComplex_standardSimplexSuccNormalizedChainsToBoundary R n k hk x hx]
    calc
      _ = (Δ[n + 2] : SSet.{0}).ιNormalizedChainComplex
          (((SSet.boundary (n + 2) : SSet.Subcomplex (Δ[n + 2] : SSet.{0})).ι).app _
            ⟨x, by rw [SSet.boundary_obj_eq_univ k (n + 2) hk]; trivial⟩) :=
        SSet.ι_normalizedChainComplexMap_f
          (f := (SSet.boundary (n + 2) : SSet.Subcomplex (Δ[n + 2] : SSet.{0})).ι)
          (R := ModuleCat.of R R) _
      _ = _ := by congr

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSphereSuccTopCyclesIsoStandardSimplexSuccTopCycles (n : ℕ) :
    kernel ((b6m_standardSphereSuccNormalizedCoefficientChains R n).d (n + 1) n) ≅
      kernel ((b6m_standardSimplexSuccNormalizedCoefficientChains R n).d (n + 1) n) :=
  let f := SSet.normalizedChainComplexMap
    (SSet.boundary (n + 2) : SSet.Subcomplex (Δ[n + 2] : SSet.{0})).ι
      (ModuleCat.of R R)
  let eTop := b6m_standardSphereSuccNormalizedChainsXIsoStandard R n (n + 1) (by lia)
  let eBelow := b6m_standardSphereSuccNormalizedChainsXIsoStandard R n n (by lia)
  letI : IsIso (f.f (n + 1)) := eTop.isIso_hom
  letI : IsIso (f.f n) := eBelow.isIso_hom
  let φ := (shortComplexFunctor' (ModuleCat R) (ComplexShape.down ℕ)
    (n + 2) (n + 1) n).map f
  letI : IsIso φ.τ₂ := by
    dsimp [φ, shortComplexFunctor']
    infer_instance
  letI : IsIso φ.τ₃ := by
    dsimp [φ, shortComplexFunctor']
    infer_instance
  ((b6m_standardSphereSuccNormalizedCoefficientChains R n).sc'
      (n + 2) (n + 1) n).cyclesIsoKernel.symm ≪≫
    asIso (ShortComplex.cyclesMap φ) ≪≫
      ((b6m_standardSimplexSuccNormalizedCoefficientChains R n).sc'
        (n + 2) (n + 1) n).cyclesIsoKernel

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSimplexSuccNormalizedChainsXTopIsoRing (n : ℕ) :
    (b6m_standardSimplexSuccNormalizedCoefficientChains R n).X (n + 2) ≅ ModuleCat.of R R :=
  let top : (Δ[n + 2] : SSet.{0}).nonDegenerate (n + 2) :=
    ⟨SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk (n + 2))),
      SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate (n + 2)⟩
  letI : Unique ((Δ[n + 2] : SSet.{0}).nonDegenerate (n + 2)) :=
    { default := top
      uniq := fun x ↦ by
        apply Subtype.ext
        have hx' : x.1 ∈
            ({SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk (n + 2)))} :
              Set ((Δ[n + 2] : SSet.{0}).obj
                (Opposite.op (SimplexCategory.mk (n + 2))))) := by
          rw [← SSet.stdSimplex.nonDegenerate_top_dim]
          exact x.2
        simpa [top] using hx' }
  IsColimit.coconePointUniqueUpToIso
    ((Δ[n + 2] : SSet.{0}).isColimitCofanNormalizedChainComplex
      (ModuleCat.of R R) (n + 2))
    (Cofan.isColimitMkOfUnique (Iso.refl (ModuleCat.of R R))
      ((Δ[n + 2] : SSet.{0}).nonDegenerate (n + 2)))

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSimplexSucc_normalized_d_top_mono (n : ℕ) :
    Mono ((b6m_standardSimplexSuccNormalizedCoefficientChains R n).d (n + 2) (n + 1)) := by
  have hTop := b6m_standardSimplexSucc_normalizedChains_exactAt R n (n + 2) (by lia)
  have hTop' : ((b6m_standardSimplexSuccNormalizedCoefficientChains R n).sc'
      (n + 3) (n + 2) (n + 1)).Exact :=
    ShortComplex.exact_of_iso
      ((b6m_standardSimplexSuccNormalizedCoefficientChains R n).isoSc'
        (n + 3) (n + 2) (n + 1) (by simp) (by simp)) hTop
  have hAbove : IsZero ((b6m_standardSimplexSuccNormalizedCoefficientChains R n).X (n + 3)) :=
    (Δ[n + 2] : SSet.{0}).isZero_normalizedChainComplex_X_of_hasDimensionLT
      (ModuleCat.of R R) (n + 3) (n + 3)
  exact hTop'.mono_g (hAbove.eq_of_src _ _)

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSimplexSuccNormalizedChainsXTopIsoTopCycles (n : ℕ) :
    (b6m_standardSimplexSuccNormalizedCoefficientChains R n).X (n + 2) ≅
      kernel ((b6m_standardSimplexSuccNormalizedCoefficientChains R n).d (n + 1) n) :=
  letI : Mono ((b6m_standardSimplexSuccNormalizedCoefficientChains R n).d (n + 2) (n + 1)) :=
    b6m_standardSimplexSucc_normalized_d_top_mono R n
  have h := b6m_standardSimplexSucc_normalizedChains_exactAt R n (n + 1) (by lia)
  have h' : ((b6m_standardSimplexSuccNormalizedCoefficientChains R n).sc'
      (n + 2) (n + 1) n).Exact :=
    ShortComplex.exact_of_iso
      ((b6m_standardSimplexSuccNormalizedCoefficientChains R n).isoSc'
        (n + 2) (n + 1) n (by simp) (by simp)) h
  letI : Mono ((b6m_standardSimplexSuccNormalizedCoefficientChains R n).sc'
      (n + 2) (n + 1) n).f := b6m_standardSimplexSucc_normalized_d_top_mono R n
  IsLimit.conePointUniqueUpToIso h'.fIsKernel
    (limit.isLimit (parallelPair
      ((b6m_standardSimplexSuccNormalizedCoefficientChains R n).d (n + 1) n) 0))

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSphereSuccTopCyclesIsoRing (n : ℕ) :
    kernel ((b6m_standardSphereSuccNormalizedCoefficientChains R n).d (n + 1) n) ≅
      ModuleCat.of R R :=
  b6m_standardSphereSuccTopCyclesIsoStandardSimplexSuccTopCycles R n ≪≫
    (b6m_standardSimplexSuccNormalizedChainsXTopIsoTopCycles R n).symm ≪≫
      b6m_standardSimplexSuccNormalizedChainsXTopIsoRing R n

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSphereSucc_normalizedChains_aboveTop_isZero (n : ℕ) :
    IsZero ((b6m_standardSphereSuccNormalizedCoefficientChains R n).X (n + 2)) :=
  (∂Δ[n + 2] : SSet.{0}).isZero_normalizedChainComplex_X_of_hasDimensionLT
    (ModuleCat.of R R) (n + 2) (n + 2)

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSphereSuccNormalizedHomologyTopIsoTopCycles (n : ℕ) :
    (b6m_standardSphereSuccNormalizedCoefficientChains R n).homology (n + 1) ≅
      kernel ((b6m_standardSphereSuccNormalizedCoefficientChains R n).d (n + 1) n) :=
  let K := b6m_standardSphereSuccNormalizedCoefficientChains R n
  let S := K.sc' (n + 2) (n + 1) n
  have hf : S.f = 0 :=
    (b6m_standardSphereSucc_normalizedChains_aboveTop_isZero R n).eq_of_src _ _
  K.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp) ≪≫
    (S.asIsoHomologyπ hf).symm ≪≫ S.cyclesIsoKernel

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSphereSuccNormalizedHomologyTopIsoRing (n : ℕ) :
    (b6m_standardSphereSuccNormalizedCoefficientChains R n).homology (n + 1) ≅
      ModuleCat.of R R :=
  b6m_standardSphereSuccNormalizedHomologyTopIsoTopCycles R n ≪≫
    b6m_standardSphereSuccTopCyclesIsoRing R n

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSphereSuccSimplicialHomologyTopIsoRing (n : ℕ) :
    ((∂Δ[n + 2] : SSet.{0}).chainComplex (ModuleCat.of R R)).homology (n + 1) ≅
      ModuleCat.of R R :=
  isoOfQuasiIsoAt
      ((∂Δ[n + 2] : SSet.{0}).toNormalizedChainComplex (ModuleCat.of R R)) (n + 1) ≪≫
    b6m_standardSphereSuccNormalizedHomologyTopIsoRing R n

end HodgeLean.Foundations.Program
