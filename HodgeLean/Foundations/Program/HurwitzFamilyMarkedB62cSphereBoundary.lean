import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cPrimitiveClass
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cSphereHomology
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.SphereAffineBoundary

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory CategoryTheory.Limits Simplicial Opposite AlgebraicTopology.Singular
open scoped Simplicial Classical
variable (R : Type) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
def b6m_standardAffineBoundaryChainMap (d : ℕ) :
    ((∂Δ[d] : SSet.{0}).chainComplex (ModuleCat.of R R)) ⟶
      (TopCat.toSSet.obj (puncturedPair ℝ d).snd).chainComplex
        (ModuleCat.of R R) :=
  SSet.chainComplexMap (standardAffineBoundarySimplicialMap d) (ModuleCat.of R R)

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSphereBoundaryChainRetractionComponent (d k : ℕ) :
    ((Δ[d] : SSet.{0}).chainComplex (ModuleCat.of R R)).X k ⟶
      ((∂Δ[d] : SSet.{0}).chainComplex (ModuleCat.of R R)).X k :=
  ((Δ[d] : SSet.{0}).isColimitChainComplexXCofan
    (ModuleCat.of R R) k).desc
      (Cofan.mk _ (fun x ↦ if hx : x ∈ (SSet.boundary d).obj _ then
        (∂Δ[d] : SSet.{0}).ιChainComplex ⟨x, hx⟩ else 0))

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSphereBoundaryChainInclusion_comp_retraction (d k : ℕ) :
    (SSet.chainComplexMap
        (SSet.boundary d : SSet.Subcomplex (Δ[d] : SSet.{0})).ι
        (ModuleCat.of R R)).f k ≫
      b6m_standardSphereBoundaryChainRetractionComponent R d k = 𝟙 _ := by
  apply (∂Δ[d] : SSet.{0}).chainComplex_hom_ext
  intro x
  rw [← Category.assoc, SSet.ι_chainComplexMap_f]
  change ((Δ[d] : SSet.{0}).chainComplexXCofan
      (ModuleCat.of R R) k).inj x.1 ≫
      b6m_standardSphereBoundaryChainRetractionComponent R d k = _
  simp [b6m_standardSphereBoundaryChainRetractionComponent, x.2]

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSphereBoundaryChainInclusionComponent_mono (d k : ℕ) :
    Mono ((SSet.chainComplexMap
      (SSet.boundary d : SSet.Subcomplex (Δ[d] : SSet.{0})).ι
      (ModuleCat.of R R)).f k) := by
  constructor
  intro Z f g h
  let inc := (SSet.chainComplexMap
    (SSet.boundary d : SSet.Subcomplex (Δ[d] : SSet.{0})).ι
    (ModuleCat.of R R)).f k
  let ret := b6m_standardSphereBoundaryChainRetractionComponent R d k
  have hret : inc ≫ ret = 𝟙 _ :=
    b6m_standardSphereBoundaryChainInclusion_comp_retraction R d k
  calc
    f = (f ≫ inc) ≫ ret := by rw [Category.assoc, hret, Category.comp_id]
    _ = (g ≫ inc) ≫ ret := by rw [h]
    _ = g := by rw [Category.assoc, hret, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSphereSimplicialBoundaryChain (n : ℕ) :
    ModuleCat.of R R ⟶
      ((∂Δ[n + 1] : SSet.{0}).chainComplex (ModuleCat.of R R)).X n :=
  ∑ i : Fin (n + 2), (-1) ^ i.val •
    (∂Δ[n + 1] : SSet.{0}).ιChainComplex
      (standardSphereBoundaryFaceSimplex n i)

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSphereSimplicialBoundaryChain_inclusion (n : ℕ) :
    b6m_standardSphereSimplicialBoundaryChain R n ≫
        (SSet.chainComplexMap
          (SSet.boundary (n + 1) : SSet.Subcomplex (Δ[n + 1] : SSet.{0})).ι
          (ModuleCat.of R R)).f n =
      (Δ[n + 1] : SSet.{0}).ιChainComplex
          (standardSimplexTopSimplexForLocalClass (n + 1)) ≫
        ((Δ[n + 1] : SSet.{0}).chainComplex
          (ModuleCat.of R R)).d (n + 1) n := by
  rw [b6m_standardSphereSimplicialBoundaryChain, Preadditive.sum_comp,
    SSet.ιChainComplex_d]
  apply Finset.sum_congr rfl
  intro i _
  rw [Preadditive.zsmul_comp]
  rw [SSet.ι_chainComplexMap_f]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSphereSimplicialBoundaryChain_boundary_succ (n : ℕ) :
    b6m_standardSphereSimplicialBoundaryChain R (n + 1) ≫
      ((∂Δ[n + 2] : SSet.{0}).chainComplex
        (ModuleCat.of R R)).d (n + 1) n = 0 := by
  let f := SSet.chainComplexMap
    (SSet.boundary (n + 2) : SSet.Subcomplex (Δ[n + 2] : SSet.{0})).ι
    (ModuleCat.of R R)
  let : Mono (f.f n) := b6m_standardSphereBoundaryChainInclusionComponent_mono R (n + 2) n
  rw [← cancel_mono (f.f n), Category.assoc, ← f.comm, ← Category.assoc,
    b6m_standardSphereSimplicialBoundaryChain_inclusion R, Category.assoc,
    HomologicalComplex.d_comp_d, comp_zero]
  simp

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSphereSimplicialBoundaryCycle (n : ℕ) :
    ModuleCat.of R R ⟶
      ((∂Δ[n + 2] : SSet.{0}).chainComplex
        (ModuleCat.of R R)).cycles (n + 1) :=
  ((∂Δ[n + 2] : SSet.{0}).chainComplex
    (ModuleCat.of R R)).liftCycles
      (b6m_standardSphereSimplicialBoundaryChain R (n + 1))
      ((ComplexShape.down ℕ).next (n + 1)) rfl
      (by
        rw [ChainComplex.next_nat_succ]
        exact b6m_standardSphereSimplicialBoundaryChain_boundary_succ R n)

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSphereSimplicialBoundaryClass (n : ℕ) :
    ((∂Δ[n + 2] : SSet.{0}).chainComplex
      (ModuleCat.of R R)).homology (n + 1) :=
  ((b6m_standardSphereSimplicialBoundaryCycle R n ≫
    ((∂Δ[n + 2] : SSet.{0}).chainComplex
      (ModuleCat.of R R)).homologyπ (n + 1)).hom) 1

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSphereSimplicialNormalizedBoundaryChain (n : ℕ) :
    ModuleCat.of R R ⟶
      (b6m_standardSphereSuccNormalizedCoefficientChains R n).X (n + 1) :=
  b6m_standardSphereSimplicialBoundaryChain R (n + 1) ≫
    ((∂Δ[n + 2] : SSet.{0}).toNormalizedChainComplex
      (ModuleCat.of R R)).f (n + 1)

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSphereSimplicialNormalizedBoundaryDetector (n : ℕ) :
    (b6m_standardSphereSuccNormalizedCoefficientChains R n).X (n + 1) ⟶
      ModuleCat.of R R :=
  Cofan.IsColimit.desc
    ((∂Δ[n + 2] : SSet.{0}).isColimitCofanNormalizedChainComplex
      (ModuleCat.of R R) (n + 1)) (fun x ↦
        if x.1 = standardSphereBoundaryFaceSimplex (n + 1) 0 then 𝟙 _ else 0)

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSphereSimplicialNormalizedBoundaryFace_detect
    (n : ℕ) (i : Fin (n + 3)) :
    (∂Δ[n + 2] : SSet.{0}).ιNormalizedChainComplex
        (standardSphereBoundaryFaceSimplex (n + 1) i) ≫
      b6m_standardSphereSimplicialNormalizedBoundaryDetector R n =
        if i = 0 then 𝟙 _ else 0 := by
  let x : (∂Δ[n + 2] : SSet.{0}).nonDegenerate (n + 1) :=
    ⟨standardSphereBoundaryFaceSimplex (n + 1) i,
      standardSphereBoundaryFaceSimplex_nonDegenerate (n + 1) i⟩
  have hiff : standardSphereBoundaryFaceSimplex (n + 1) i =
      standardSphereBoundaryFaceSimplex (n + 1) 0 ↔ i = 0 :=
    (standardSphereBoundaryFaceSimplex_injective (n + 1)).eq_iff
  change ((∂Δ[n + 2] : SSet.{0}).cofanNormalizedChainComplex
      (ModuleCat.of R R) (n + 1)).inj x ≫
        b6m_standardSphereSimplicialNormalizedBoundaryDetector R n = _
  rw [b6m_standardSphereSimplicialNormalizedBoundaryDetector,
    Cofan.IsColimit.fac]
  simp [x, hiff]

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSphereSimplicialNormalizedBoundaryChain_detect (n : ℕ) :
    b6m_standardSphereSimplicialNormalizedBoundaryChain R n ≫
      b6m_standardSphereSimplicialNormalizedBoundaryDetector R n = 𝟙 _ := by
  rw [b6m_standardSphereSimplicialNormalizedBoundaryChain,
    b6m_standardSphereSimplicialBoundaryChain, Preadditive.sum_comp,
    Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, Category.assoc,
    SSet.ιChainComplex_toNormalizedChainComplex_f_assoc,
    b6m_standardSphereSimplicialNormalizedBoundaryFace_detect R]
  rw [Finset.sum_eq_single (0 : Fin (n + 3))]
  · norm_num
  · intro i _ hi
    simp [hi]
  · simp

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSphereSimplicialNormalizedBoundaryChain_boundary (n : ℕ) :
    b6m_standardSphereSimplicialNormalizedBoundaryChain R n ≫
      (b6m_standardSphereSuccNormalizedCoefficientChains R n).d (n + 1) n = 0 := by
  let K := (∂Δ[n + 2] : SSet.{0}).chainComplex (ModuleCat.of R R)
  let L := (∂Δ[n + 2] : SSet.{0}).normalizedChainComplex (ModuleCat.of R R)
  let q : K ⟶ L :=
    (∂Δ[n + 2] : SSet.{0}).toNormalizedChainComplex (ModuleCat.of R R)
  calc
    _ = b6m_standardSphereSimplicialBoundaryChain R (n + 1) ≫
        (q.f (n + 1) ≫ L.d (n + 1) n) :=
      Category.assoc _ _ _
    _ = b6m_standardSphereSimplicialBoundaryChain R (n + 1) ≫
        (K.d (n + 1) n ≫ q.f n) := by
      rw [← q.comm]
    _ = (b6m_standardSphereSimplicialBoundaryChain R (n + 1) ≫
        K.d (n + 1) n) ≫ q.f n :=
      (Category.assoc _ _ _).symm
    _ = 0 := by
      rw [b6m_standardSphereSimplicialBoundaryChain_boundary_succ R, zero_comp]

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSphereSimplicialNormalizedBoundaryCycle (n : ℕ) :
    ModuleCat.of R R ⟶
      (b6m_standardSphereSuccNormalizedCoefficientChains R n).cycles (n + 1) :=
  (b6m_standardSphereSuccNormalizedCoefficientChains R n).liftCycles
    (b6m_standardSphereSimplicialNormalizedBoundaryChain R n)
    ((ComplexShape.down ℕ).next (n + 1)) rfl (by
      rw [ChainComplex.next_nat_succ]
      exact b6m_standardSphereSimplicialNormalizedBoundaryChain_boundary R n)

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSphereSimplicialNormalizedBoundaryCycle_inclusion (n : ℕ) :
    b6m_standardSphereSimplicialNormalizedBoundaryCycle R n ≫
      (b6m_standardSphereSuccNormalizedCoefficientChains R n).iCycles (n + 1) =
        b6m_standardSphereSimplicialNormalizedBoundaryChain R n :=
  (b6m_standardSphereSuccNormalizedCoefficientChains R n).liftCycles_i
    (b6m_standardSphereSimplicialNormalizedBoundaryChain R n)
    ((ComplexShape.down ℕ).next (n + 1)) rfl _

set_option backward.isDefEq.respectTransparency false in
def b6m_standardSphereSimplicialNormalizedBoundaryClass (n : ℕ) :
    (b6m_standardSphereSuccNormalizedCoefficientChains R n).homology (n + 1) :=
  ((b6m_standardSphereSimplicialNormalizedBoundaryCycle R n ≫
    (b6m_standardSphereSuccNormalizedCoefficientChains R n).homologyπ (n + 1)).hom) 1

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSphereSimplicialBoundaryCycle_normalization (n : ℕ) :
    b6m_standardSphereSimplicialBoundaryCycle R n ≫
        HomologicalComplex.cyclesMap
          ((∂Δ[n + 2] : SSet.{0}).toNormalizedChainComplex
            (ModuleCat.of R R)) (n + 1) =
      b6m_standardSphereSimplicialNormalizedBoundaryCycle R n := by
  apply (cancel_mono
    ((b6m_standardSphereSuccNormalizedCoefficientChains R n).iCycles (n + 1))).mp
  rw [Category.assoc, HomologicalComplex.cyclesMap_i,
    b6m_standardSphereSimplicialNormalizedBoundaryCycle_inclusion R, ← Category.assoc,
    b6m_standardSphereSimplicialBoundaryCycle, HomologicalComplex.liftCycles_i]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma b6m_standardSphereSimplicialBoundaryClass_normalization (n : ℕ) :
    (HomologicalComplex.homologyMap
      ((∂Δ[n + 2] : SSet.{0}).toNormalizedChainComplex
        (ModuleCat.of R R)) (n + 1)).hom
        (b6m_standardSphereSimplicialBoundaryClass R n) =
      b6m_standardSphereSimplicialNormalizedBoundaryClass R n := by
  let q := (∂Δ[n + 2] : SSet.{0}).toNormalizedChainComplex (ModuleCat.of R R)
  have hmor :
      b6m_standardSphereSimplicialBoundaryCycle R n ≫
          ((∂Δ[n + 2] : SSet.{0}).chainComplex
            (ModuleCat.of R R)).homologyπ (n + 1) ≫
          HomologicalComplex.homologyMap q (n + 1) =
        b6m_standardSphereSimplicialNormalizedBoundaryCycle R n ≫
          (b6m_standardSphereSuccNormalizedCoefficientChains R n).homologyπ (n + 1) := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      b6m_standardSphereSimplicialBoundaryCycle_normalization R]
  exact ConcreteCategory.congr_hom hmor 1

theorem b6m_span_standardSphereSimplicialNormalizedBoundaryClass (n : ℕ) :
    Submodule.span R {b6m_standardSphereSimplicialNormalizedBoundaryClass R n} = ⊤ := by
  let K := b6m_standardSphereSuccNormalizedCoefficientChains R n
  have hd : K.d (n + 2) (n + 1) = 0 :=
    (b6m_standardSphereSucc_normalizedChains_aboveTop_isZero R n).eq_of_src _ _
  letI : IsIso (K.homologyπ (n + 1)) :=
    K.isIso_homologyπ (n + 2) (n + 1) (by simp) hd
  let l : K.homology (n + 1) ⟶ ModuleCat.of R R :=
    inv (K.homologyπ (n + 1)) ≫ K.iCycles (n + 1) ≫
      b6m_standardSphereSimplicialNormalizedBoundaryDetector R n
  have hmor : b6m_standardSphereSimplicialNormalizedBoundaryCycle R n ≫
      K.homologyπ (n + 1) ≫ l = 𝟙 _ := by
    dsimp [l]
    rw [IsIso.hom_inv_id_assoc, ← Category.assoc,
      b6m_standardSphereSimplicialNormalizedBoundaryCycle_inclusion,
      b6m_standardSphereSimplicialNormalizedBoundaryChain_detect]
  apply b6m_span_eq_top_of_rank_one_detector
    (b6m_standardSphereSuccNormalizedHomologyTopIsoRing R n).toLinearEquiv l.hom
  exact ConcreteCategory.congr_hom hmor 1

theorem b6m_span_standardSphereSimplicialBoundaryClass (n : ℕ) :
    Submodule.span R {b6m_standardSphereSimplicialBoundaryClass R n} = ⊤ := by
  let q := (∂Δ[n + 2] : SSet.{0}).toNormalizedChainComplex (ModuleCat.of R R)
  let e := (isoOfQuasiIsoAt q (n + 1)).toLinearEquiv
  have he : e (b6m_standardSphereSimplicialBoundaryClass R n) =
      b6m_standardSphereSimplicialNormalizedBoundaryClass R n :=
    b6m_standardSphereSimplicialBoundaryClass_normalization R n
  apply Submodule.map_injective_of_injective e.injective
  rw [Submodule.map_span, Set.image_singleton, Submodule.map_top,
    LinearMap.range_eq_top.mpr e.surjective]
  change Submodule.span R {e (b6m_standardSphereSimplicialBoundaryClass R n)} = ⊤
  rw [he]
  exact b6m_span_standardSphereSimplicialNormalizedBoundaryClass R n

end HodgeLean.Foundations.Program
