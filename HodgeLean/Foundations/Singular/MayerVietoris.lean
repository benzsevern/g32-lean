import HodgeLean.Foundations.Singular.Cup
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.MayerVietoris
import HodgeLean.Foundations.Port.Algebra.Homology.LinearDual
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-!
# Mayer–Vietoris on singular cochains

The sequence is dualized before taking cohomology. Its connecting morphism
therefore comes from the cochain differential and can be used with cup products.
HC no distance; AV milestone no distance. No stated hypothesis is retired.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgebraicTopology.Singular

namespace HodgeLean.Foundations.Singular

/-- Reversing a short sequence of chain complexes and dualizing its maps.
Source: Hatcher, *Algebraic Topology*, §3.1, dual cochain complexes.
-/
def dualCochainShortComplex {R : Type} [CommRing R]
    (S : ShortComplex (ChainComplex (ModuleCat R) ℕ)) :
    ShortComplex (CochainComplex (ModuleCat R) ℕ) :=
  ShortComplex.mk (linearDualMap S.g) (linearDualMap S.f) (by
    rw [← linearDualMap_comp, S.zero]
    ext n φ
    apply LinearMap.ext
    intro x
    change Module.Dual R (S.X₃.X n) at φ
    change φ 0 = 0
    exact map_zero φ)

example {R : Type} [CommRing R]
    (S : ShortComplex (ChainComplex (ModuleCat R) ℕ)) :
    (dualCochainShortComplex S).f = linearDualMap S.g := rfl

/-- A degreewise split short exact chain sequence dualizes to a short exact cochain sequence.
Source: Hatcher, *Algebraic Topology*, §3.1; upstream
`HodgeConjecture/Lemmas/Algebra/Homology/LinearDual.lean`, `Splitting.linearDual`.
-/
theorem dualCochainShortComplex_shortExact {R : Type} [CommRing R]
    (S : ShortComplex (ChainComplex (ModuleCat R) ℕ))
    (hs : ∀ n, (S.map (eval (ModuleCat R) (ComplexShape.down ℕ) n)).Splitting) :
    (dualCochainShortComplex S).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro n
  exact (hs n).linearDual.shortExact

section Biprod
variable {R : Type} [CommRing R] (K L : ChainComplex (ModuleCat R) ℕ)
/-- Duality carries a chain biproduct to the biproduct of cochain complexes.
Source: Hatcher, *Algebraic Topology*, §3.1, dual cochains; the universal property of biproducts.
-/
def dualBiprodIso : (K ⊞ L).linearDualCochainComplex ≅
    K.linearDualCochainComplex ⊞ L.linearDualCochainComplex where
  hom := biprod.lift (linearDualMap biprod.inl) (linearDualMap biprod.inr)
  inv := biprod.desc (linearDualMap biprod.fst) (linearDualMap biprod.snd)
  hom_inv_id := by
    rw [biprod.lift_desc]
    ext n φ
    apply LinearMap.ext
    intro x
    change Module.Dual R ((K ⊞ L).X n) at φ
    change φ (((biprod.fst : K ⊞ L ⟶ K).f n ≫ (biprod.inl : K ⟶ K ⊞ L).f n) x) +
      φ (((biprod.snd : K ⊞ L ⟶ L).f n ≫ (biprod.inr : L ⟶ K ⊞ L).f n) x) = φ x
    rw [← map_add]
    congr 1
    exact ConcreteCategory.congr_hom (congrArg (fun f => f.f n) (biprod.total (X := K) (Y := L))) x
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext'
    all_goals simp only [Category.assoc, biprod.inl_desc_assoc, biprod.inr_desc_assoc,
      biprod.lift_fst, biprod.lift_snd, biprod.inl_fst, biprod.inr_fst,
      biprod.inl_snd, biprod.inr_snd, Category.id_comp]
    all_goals rw [← linearDualMap_comp]
    all_goals simp only [biprod.inl_fst, biprod.inr_fst, biprod.inl_snd,
      biprod.inr_snd, linearDualMap_id]
    all_goals ext n φ; apply LinearMap.ext; intro x
    all_goals change Module.Dual R _ at φ; change φ 0 = 0; exact map_zero φ

example : (dualBiprodIso K L).hom ≫ biprod.fst = linearDualMap biprod.inl :=
  biprod.lift_fst _ _
end Biprod

variable (Y : TopCat.{0}) (A B : Set Y)

/-- The cochain-level sequence from small cochains to the dual of the chain biproduct
and then to cochains on the intersection. Its second arrow is restriction difference.
Source: Hatcher, *Algebraic Topology*, §2.2 and §3.1, Mayer–Vietoris.
-/
def mvCochainShortComplex : ShortComplex (CochainComplex (ModuleCat ℚ) ℕ) :=
  dualCochainShortComplex (singularMayerVietorisShortComplex Y A B)

example : (mvCochainShortComplex Y A B).X₃ =
    SingularCochainComplex ℚ (TopCat.of ↥(A ∩ B)) := rfl

/-- The cochain Mayer–Vietoris sequence is short exact, even before imposing an open cover.
Source: Hatcher, *Algebraic Topology*, §3.1, cohomological Mayer–Vietoris.
-/
theorem mvCochainShortComplex_shortExact : (mvCochainShortComplex Y A B).ShortExact := by
  apply dualCochainShortComplex_shortExact
  intro n
  exact ((shortExact_iff_degreewise_shortExact _).mp
    (singularMayerVietorisShortComplex_shortExact Y A B) n).splittingOfProjective

private instance homology_preservesBinaryBiproducts (n : ℕ) :
    PreservesBinaryBiproducts (homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n) :=
  preservesBinaryBiproducts_of_preservesBiproducts _

/-- The middle cohomology term is canonically the biproduct of the cohomologies of
both cover members.
Source: Hatcher, *Algebraic Topology*, §3.1, Mayer–Vietoris sequence.
-/
def mvCohomologySumIso (n : ℕ) :
    (mvCochainShortComplex Y A B).X₂.homology n ≅
      Cohomology ℚ (TopCat.of A) n ⊞ Cohomology ℚ (TopCat.of B) n :=
  (homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso
    (dualBiprodIso (SingularChainComplex ℚ (TopCat.of A))
      (SingularChainComplex ℚ (TopCat.of B))) ≪≫
    (homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapBiprod _ _

example (n : ℕ) : (mvCohomologySumIso Y A B n).hom ≫
    (mvCohomologySumIso Y A B n).inv = 𝟙 _ := Iso.hom_inv_id _

set_option backward.isDefEq.respectTransparency false in
private lemma dualMap_neg {K L : ChainComplex (ModuleCat ℚ) ℕ} (f : K ⟶ L) :
    linearDualMap (-f) = -linearDualMap f := by
  ext n φ
  apply LinearMap.ext
  intro x
  change Module.Dual ℚ (L.X n) at φ
  change φ (-(f.f n).hom x) = -(φ ((f.f n).hom x))
  exact map_neg φ _

set_option backward.isDefEq.respectTransparency false in
private lemma dual_biprod_lift {K L M : ChainComplex (ModuleCat ℚ) ℕ}
    (f : M ⟶ K) (g : M ⟶ L) :
    (dualBiprodIso K L).inv ≫ linearDualMap (biprod.lift f (-g)) =
      biprod.desc (linearDualMap f) (-linearDualMap g) := by
  apply biprod.hom_ext'
  · simp only [dualBiprodIso, biprod.inl_desc_assoc, biprod.inl_desc]
    rw [← linearDualMap_comp, biprod.lift_fst]
  · simp only [dualBiprodIso, biprod.inr_desc_assoc, biprod.inr_desc]
    rw [← linearDualMap_comp, biprod.lift_snd, dualMap_neg]

set_option backward.isDefEq.respectTransparency false in
/-- Under the canonical biproduct comparison, the overlap map is precisely the
difference of pullbacks along the two subset inclusions.
Source: Hatcher, *Algebraic Topology*, §3.1, Mayer–Vietoris restriction maps.
-/
theorem mvDifference_sumIso_eq (n : ℕ) :
    (mvCohomologySumIso Y A B n).inv ≫
      homologyMap (mvCochainShortComplex Y A B).g n =
    biprod.desc (ModuleCat.ofHom (cohomologyMap ℚ n (subsetIntersectionToLeft Y A B)))
      (-ModuleCat.ofHom (cohomologyMap ℚ n (subsetIntersectionToRight Y A B))) := by
  let F := homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n
  change (F.mapBiprod _ _).inv ≫ F.map _ ≫ F.map _ = _
  rw [← F.map_comp]
  change (F.mapBiprod _ _).inv ≫ F.map
    ((dualBiprodIso _ _).inv ≫ linearDualMap
      (biprod.lift
        (SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToLeft Y A B)) (ModuleCat.of ℚ ℚ))
        (-(SSet.chainComplexMap (TopCat.toSSet.map (subsetIntersectionToRight Y A B)) (ModuleCat.of ℚ ℚ))))) = _
  rw [dual_biprod_lift]
  rw [biprod.mapBiprod_inv_map_desc, F.map_neg]
  rfl

variable (hA : IsOpen A) (hB : IsOpen B) (hAB : A ∪ B = Set.univ)

/-- Small cochains compute ambient cohomology by the dual of subdivision's chain
homotopy equivalence, without identifying cohomology with dual homology.
Source: Hatcher, *Algebraic Topology*, §2.1, subdivision theorem; upstream
`coverSmallRationalChainHomotopyEquiv_of_openCover`.
-/
def smallCochainCohomologyEquiv (n : ℕ) :
    (mvCochainShortComplex Y A B).X₁.homology n ≃ₗ[ℚ] Cohomology ℚ Y n := by
  have hopen : ∀ b : Bool, IsOpen (if b then A else B) := by
    intro b
    cases b <;> assumption
  have hcover : ⋃ b : Bool, (if b then A else B) = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    rcases (hAB.symm ▸ Set.mem_univ x : x ∈ A ∪ B) with hx | hx
    · exact Set.mem_iUnion.mpr ⟨true, hx⟩
    · exact Set.mem_iUnion.mpr ⟨false, hx⟩
  letI : IsIso (homologyMap (linearDualMap (twoSubsetSmallChainInclusion Y A B)) n) := by
    change IsIso (homologyMap (linearDualMap
      (SSet.chainComplexMap
        (subsetSingularSubcomplex Y A ⊔ subsetSingularSubcomplex Y B).ι
        (ModuleCat.of ℚ ℚ))) n)
    rw [subsetSingularSubcomplex_sup]
    change IsIso (homologyMap (linearDualMap
      (coverSmallRationalSingularChainInclusion Y (fun b : Bool => if b then A else B))) n)
    rw [← coverSmallRationalChainHomotopyEquiv_of_openCover_hom Y
      (fun b : Bool => if b then A else B) hopen hcover]
    exact inferInstanceAs (IsIso ((linearDualHomotopyEquiv
      (coverSmallRationalChainHomotopyEquiv_of_openCover Y
        (fun b : Bool => if b then A else B) hopen hcover)).toHomologyIso n).hom)
  exact (asIso (homologyMap (linearDualMap (twoSubsetSmallChainInclusion Y A B)) n)).symm.toLinearEquiv

example (n : ℕ) : smallCochainCohomologyEquiv Y A B hA hB hAB n 0 = 0 := map_zero _

/-- The inverse comparison is induced by restriction to small chains.
Source: constructed here from the open-cover subdivision equivalence.
-/
theorem smallCochainCohomologyEquiv_symm (n : ℕ) :
    (smallCochainCohomologyEquiv Y A B hA hB hAB n).symm.toLinearMap =
      (homologyMap (linearDualMap (twoSubsetSmallChainInclusion Y A B)) n).hom := rfl

/-- The cohomological Mayer–Vietoris connecting map, obtained from the cochain
short exact sequence and transported from small to ambient cohomology.
Source: Hatcher, *Algebraic Topology*, §3.1, cohomological Mayer–Vietoris.
-/
def mvδ (n : ℕ) :
    Cohomology ℚ (TopCat.of ↥(A ∩ B)) n →ₗ[ℚ] Cohomology ℚ Y (n + 1) :=
  (smallCochainCohomologyEquiv Y A B hA hB hAB (n + 1)).toLinearMap.comp
    ((mvCochainShortComplex_shortExact Y A B).δ n (n + 1) (by simp)).hom

example (n : ℕ) : mvδ Y A B hA hB hAB n 0 = 0 := map_zero _

/-- Restriction from ambient cohomology to the two cover members, represented by
the dual of their chain biproduct.
Source: Hatcher, *Algebraic Topology*, §3.1, Mayer–Vietoris restriction.
-/
def mvRestriction (n : ℕ) : Cohomology ℚ Y n →ₗ[ℚ]
    (mvCochainShortComplex Y A B).X₂.homology n :=
  (homologyMap (mvCochainShortComplex Y A B).f n).hom.comp
    (smallCochainCohomologyEquiv Y A B hA hB hAB n).symm.toLinearMap

example (n : ℕ) : mvRestriction Y A B hA hB hAB n 0 = 0 := map_zero _

set_option backward.isDefEq.respectTransparency false in
/-- The ambient restriction map is the pair of the actual subset pullbacks.
Source: Hatcher, *Algebraic Topology*, §3.1, Mayer–Vietoris restriction.
-/
theorem mvRestriction_sumIso_eq (n : ℕ) :
    ModuleCat.ofHom (mvRestriction Y A B hA hB hAB n) ≫
      (mvCohomologySumIso Y A B n).hom =
    biprod.lift (ModuleCat.ofHom (cohomologyMap ℚ n (topologicalSubsetInclusion Y A)))
      (ModuleCat.ofHom (cohomologyMap ℚ n (topologicalSubsetInclusion Y B))) := by
  let F := homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n
  have hd {K L M : ChainComplex (ModuleCat ℚ) ℕ} (f : K ⟶ M) (g : L ⟶ M) :
      linearDualMap (biprod.desc f g) ≫ (dualBiprodIso K L).hom =
        biprod.lift (linearDualMap f) (linearDualMap g) := by
    apply biprod.hom_ext
    · simp only [Category.assoc, dualBiprodIso, biprod.lift_fst]
      rw [← linearDualMap_comp, biprod.inl_desc]
    · simp only [Category.assoc, dualBiprodIso, biprod.lift_snd]
      rw [← linearDualMap_comp, biprod.inr_desc]
  change (F.map (linearDualMap (twoSubsetSmallChainInclusion Y A B)) ≫
    F.map (linearDualMap (singularMayerVietorisShortComplex Y A B).g)) ≫
      F.map (dualBiprodIso _ _).hom ≫ (F.mapBiprod _ _).hom = _
  rw [← F.map_comp, ← linearDualMap_comp]
  change F.map (linearDualMap (singularMayerVietorisSumChainMap Y A B)) ≫
    F.map (dualBiprodIso _ _).hom ≫ (F.mapBiprod _ _).hom = _
  rw [singularMayerVietorisSumChainMap_eq, ← Category.assoc, ← F.map_comp,
    hd, biprod.map_lift_mapBiprod]
  rfl

/-- The difference of the two restrictions to the intersection, on cohomology.
Source: Hatcher, *Algebraic Topology*, §3.1, Mayer–Vietoris restriction difference.
-/
def mvDifference (n : ℕ) : (mvCochainShortComplex Y A B).X₂.homology n →ₗ[ℚ]
    Cohomology ℚ (TopCat.of ↥(A ∩ B)) n :=
  (homologyMap (mvCochainShortComplex Y A B).g n).hom

example (n : ℕ) : mvDifference Y A B n 0 = 0 := map_zero _

set_option backward.isDefEq.respectTransparency false in
/-- The overlap difference evaluated on a pair of classes is first restriction minus second.
Source: Hatcher, *Algebraic Topology*, §3.1, the cohomological Mayer–Vietoris sequence.
-/
theorem mvDifference_sum_apply (n : ℕ)
    (a : Cohomology ℚ (TopCat.of A) n) (b : Cohomology ℚ (TopCat.of B) n) :
    mvDifference Y A B n
      (((mvCohomologySumIso Y A B n ≪≫
        ModuleCat.biprodIsoProd _ _).toLinearEquiv).symm (a, b)) =
      cohomologyMap ℚ n (subsetIntersectionToLeft Y A B) a -
        cohomologyMap ℚ n (subsetIntersectionToRight Y A B) b := by
  have h := mvDifference_sumIso_eq Y A B n
  have h' := congrArg (fun f => (ModuleCat.biprodIsoProd
    (Cohomology ℚ (TopCat.of A) n) (Cohomology ℚ (TopCat.of B) n)).inv ≫ f) h
  simp only [biprod.desc_eq, Preadditive.comp_add, ← Category.assoc,
    ModuleCat.biprodIsoProd_inv_comp_fst, ModuleCat.biprodIsoProd_inv_comp_snd,
    Preadditive.comp_neg] at h'
  convert ConcreteCategory.congr_hom h' (a, b) using 1
  · rfl
  · rfl
  · change cohomologyMap ℚ n (subsetIntersectionToLeft Y A B) a -
        cohomologyMap ℚ n (subsetIntersectionToRight Y A B) b =
      cohomologyMap ℚ n (subsetIntersectionToLeft Y A B) a +
        -(cohomologyMap ℚ n (subsetIntersectionToRight Y A B) b)
    exact sub_eq_add_neg _ _

set_option backward.isDefEq.respectTransparency false in
/-- Exactness at ambient cohomology after the connecting map.
Source: Hatcher, *Algebraic Topology*, §3.1, Mayer–Vietoris exact sequence.
-/
theorem mv_exact₁ (n : ℕ) :
    Function.Exact (mvδ Y A B hA hB hAB n)
      (mvRestriction Y A B hA hB hAB (n + 1)) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((mvCochainShortComplex_shortExact Y A B).homology_exact₁ n (n + 1) (by simp))
  let e := smallCochainCohomologyEquiv Y A B hA hB hAB (n + 1)
  intro x
  change (homologyMap (mvCochainShortComplex Y A B).f (n + 1)).hom (e.symm x) = 0 ↔ _
  rw [h (e.symm x)]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, (congrArg e hz).trans (e.apply_symm_apply x)⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply e.injective
    exact hz.trans (e.apply_symm_apply x).symm

/-- Exactness at the cohomology of the two cover members.
Source: Hatcher, *Algebraic Topology*, §3.1, Mayer–Vietoris exact sequence.
-/
theorem mv_exact₂ (n : ℕ) :
    Function.Exact (mvRestriction Y A B hA hB hAB n) (mvDifference Y A B n) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((mvCochainShortComplex_shortExact Y A B).homology_exact₂ n)
  let e := smallCochainCohomologyEquiv Y A B hA hB hAB n
  intro x
  change (homologyMap (mvCochainShortComplex Y A B).g n).hom x = 0 ↔ _
  rw [h x]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨e z, by simpa [mvRestriction, e] using hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨e.symm z, hz⟩

/-- Exactness at the cohomology of the intersection.
Source: Hatcher, *Algebraic Topology*, §3.1, Mayer–Vietoris exact sequence.
-/
theorem mv_exact₃ (n : ℕ) :
    Function.Exact (mvDifference Y A B n) (mvδ Y A B hA hB hAB n) := by
  have h := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((mvCochainShortComplex_shortExact Y A B).homology_exact₃ n (n + 1) (by simp))
  intro x
  change (smallCochainCohomologyEquiv Y A B hA hB hAB (n + 1)) _ = 0 ↔ _
  rw [map_eq_zero_iff _ (smallCochainCohomologyEquiv Y A B hA hB hAB (n + 1)).injective]
  exact h x

/-- Restriction to a cover is injective in degree zero, including the left endpoint
of the nonnegative cohomology sequence.
Source: Hatcher, *Algebraic Topology*, §3.1, the start of Mayer–Vietoris.
-/
theorem mvRestriction_zero_injective :
    Function.Injective (mvRestriction Y A B hA hB hAB 0) := by
  letI := (mvCochainShortComplex_shortExact Y A B).mono_f
  letI := mono_homologyMap_of_mono_of_not_rel (mvCochainShortComplex Y A B).f 0
    (by intro i; simp)
  exact ((ModuleCat.mono_iff_injective
    (homologyMap (mvCochainShortComplex Y A B).f 0)).mp inferInstance).comp
    (smallCochainCohomologyEquiv Y A B hA hB hAB 0).symm.injective

/-- Cochains of an empty space form a zero complex.
Source: Hatcher, *Algebraic Topology*, §3.1, the singular cochain complex.
-/
theorem isZero_singularCochainComplex_of_isEmpty (X : TopCat.{0}) [IsEmpty X] :
    IsZero (SingularCochainComplex ℚ X) := by
  rw [IsZero.iff_id_eq_zero]
  ext n φ
  exact cochain_eq_zero_of_isEmpty X n φ

/-- Cohomology is additive on a disjoint open cover, obtained directly from the
cochain Mayer–Vietoris sequence with empty overlap.
Source: Hatcher, *Algebraic Topology*, §3.1, additivity and Mayer–Vietoris.
-/
def cohomologyDisjointCoverEquiv (hd : Disjoint A B) (n : ℕ) :
    Cohomology ℚ Y n ≃ₗ[ℚ]
      (Cohomology ℚ (TopCat.of A) n × Cohomology ℚ (TopCat.of B) n) := by
  letI : IsEmpty ↥(A ∩ B) := ⟨fun x => Set.disjoint_left.mp hd x.2.1 x.2.2⟩
  letI : IsIso (mvCochainShortComplex Y A B).f :=
    (mvCochainShortComplex_shortExact Y A B).isIso_f_iff.mpr
      (isZero_singularCochainComplex_of_isEmpty (TopCat.of ↥(A ∩ B)))
  exact (smallCochainCohomologyEquiv Y A B hA hB hAB n).symm.trans
    (((homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso
      (asIso (mvCochainShortComplex Y A B).f) ≪≫ mvCohomologySumIso Y A B n ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv)

example (hd : Disjoint A B) (n : ℕ) :
    cohomologyDisjointCoverEquiv Y A B hA hB hAB hd n 0 = 0 := map_zero _

set_option backward.isDefEq.respectTransparency false in
/-- Under the product comparison, ambient restriction is the pair of subset pullbacks.
Source: Hatcher, *Algebraic Topology*, §3.1, the cohomological Mayer–Vietoris sequence.
-/
theorem mvRestriction_sum_apply (n : ℕ) (x : Cohomology ℚ Y n) :
    ((mvCohomologySumIso Y A B n ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv)
      (mvRestriction Y A B hA hB hAB n x) =
      (cohomologyMap ℚ n (topologicalSubsetInclusion Y A) x,
        cohomologyMap ℚ n (topologicalSubsetInclusion Y B) x) := by
  let f := ModuleCat.ofHom (cohomologyMap ℚ n (topologicalSubsetInclusion Y A))
  let g := ModuleCat.ofHom (cohomologyMap ℚ n (topologicalSubsetInclusion Y B))
  have hp : biprod.lift f g ≫ (ModuleCat.biprodIsoProd _ _).hom =
      ModuleCat.ofHom (f.hom.prod g.hom) := by
    apply (cancel_mono (ModuleCat.biprodIsoProd _ _).inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply biprod.hom_ext <;>
      simp only [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst,
        ModuleCat.biprodIsoProd_inv_comp_snd, biprod.lift_fst, biprod.lift_snd]
    all_goals rfl
  have h := congrArg (fun k => k ≫ (ModuleCat.biprodIsoProd _ _).hom)
    (mvRestriction_sumIso_eq Y A B hA hB hAB n)
  rw [hp] at h
  exact ConcreteCategory.congr_hom h x

set_option backward.isDefEq.respectTransparency false in
/-- The disjoint-cover equivalence takes a class to its restrictions on both pieces.
Source: Hatcher, *Algebraic Topology*, §3.1, additivity on disjoint unions.
-/
theorem cohomologyDisjointCoverEquiv_apply (hd : Disjoint A B) (n : ℕ)
    (x : Cohomology ℚ Y n) :
    cohomologyDisjointCoverEquiv Y A B hA hB hAB hd n x =
      (cohomologyMap ℚ n (topologicalSubsetInclusion Y A) x,
        cohomologyMap ℚ n (topologicalSubsetInclusion Y B) x) := by
  let f := ModuleCat.ofHom (cohomologyMap ℚ n (topologicalSubsetInclusion Y A))
  let g := ModuleCat.ofHom (cohomologyMap ℚ n (topologicalSubsetInclusion Y B))
  have hp : biprod.lift f g ≫ (ModuleCat.biprodIsoProd _ _).hom =
      ModuleCat.ofHom (f.hom.prod g.hom) := by
    apply (cancel_mono (ModuleCat.biprodIsoProd _ _).inv).mp
    rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply biprod.hom_ext <;>
      simp only [Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst,
        ModuleCat.biprodIsoProd_inv_comp_snd, biprod.lift_fst, biprod.lift_snd]
    all_goals rfl
  have h := congrArg (fun k => k ≫ (ModuleCat.biprodIsoProd _ _).hom)
    (mvRestriction_sumIso_eq Y A B hA hB hAB n)
  rw [hp] at h
  exact ConcreteCategory.congr_hom h x

set_option backward.isDefEq.respectTransparency false in
/-- Cochain formula for the connecting morphism: lift an overlap cocycle to the
two-piece cochains, take its coboundary, and descend the resulting small cocycle.
The last hypothesis merely records that the displayed representative is a cocycle.
Source: Hatcher, *Algebraic Topology*, §3.1, construction of the connecting homomorphism.
-/
theorem mvδ_cochain_formula (n : ℕ) {W : ModuleCat ℚ}
    (x₃ : W ⟶ (mvCochainShortComplex Y A B).X₃.X n)
    (hx₃ : x₃ ≫ (mvCochainShortComplex Y A B).X₃.d n (n + 1) = 0)
    (x₂ : W ⟶ (mvCochainShortComplex Y A B).X₂.X n)
    (hx₂ : x₂ ≫ (mvCochainShortComplex Y A B).g.f n = x₃)
    (x₁ : W ⟶ (mvCochainShortComplex Y A B).X₁.X (n + 1))
    (hx₁ : x₁ ≫ (mvCochainShortComplex Y A B).f.f (n + 1) =
      x₂ ≫ (mvCochainShortComplex Y A B).X₂.d n (n + 1))
    (hc₁ : x₁ ≫ (mvCochainShortComplex Y A B).X₁.d (n + 1) (n + 2) = 0) :
    (mvCochainShortComplex Y A B).X₃.liftCycles x₃ (n + 1) (by simp) hx₃ ≫
      (mvCochainShortComplex Y A B).X₃.homologyπ n ≫
      ModuleCat.ofHom (mvδ Y A B hA hB hAB n) =
    (mvCochainShortComplex Y A B).X₁.liftCycles x₁ (n + 2) (by simp) hc₁ ≫
      (mvCochainShortComplex Y A B).X₁.homologyπ (n + 1) ≫
      (smallCochainCohomologyEquiv Y A B hA hB hAB (n + 1)).toModuleIso.hom := by
  have h := (mvCochainShortComplex_shortExact Y A B).δ_eq n (n + 1) (by simp)
    x₃ hx₃ x₂ hx₂ x₁ hx₁ (n + 2) (by simp)
  have h' := congrArg (fun f => f ≫
    (smallCochainCohomologyEquiv Y A B hA hB hAB (n + 1)).toModuleIso.hom) h
  convert h' using 1 <;> rfl

#print axioms smallCochainCohomologyEquiv_symm
#print axioms mvRestriction_sumIso_eq
#print axioms cohomologyDisjointCoverEquiv_apply
#print axioms mvDifference_sum_apply
#print axioms mvδ_cochain_formula
#print axioms mvDifference_sumIso_eq
#print axioms mvRestriction_zero_injective
#print axioms mvRestriction
#print axioms mvDifference
#print axioms dualBiprodIso
#print axioms mvCohomologySumIso
#print axioms cohomologyDisjointCoverEquiv
#print axioms isZero_singularCochainComplex_of_isEmpty
#print axioms dualCochainShortComplex_shortExact
#print axioms mvCochainShortComplex_shortExact
#print axioms smallCochainCohomologyEquiv
#print axioms mvδ
#print axioms mv_exact₁
#print axioms mv_exact₂
#print axioms mv_exact₃

end HodgeLean.Foundations.Singular
