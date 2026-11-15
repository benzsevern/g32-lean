import HodgeLean.Foundations.Singular.Circle
import HodgeLean.Foundations.Singular.CupModule
import HodgeLean.Foundations.Singular.MayerVietorisNaturality
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Nat.Choose.Sum

/-!
# Cohomology of products with the circle and Betti numbers of tori

Mayer–Vietoris over the circle factor splits by projection pullback and cup
multiplication by the explicitly normalized circle generator. The result holds
for arbitrary spaces, before any finite-dimensionality assumptions. The signed
left-module identity identifies the connecting summand with the requested cup
map. Degree zero is treated separately; positive degrees use successor indexing.
The earlier dimension argument and binomial recurrence are retained independently.
HC no distance; AV milestone no distance. No stated hypothesis is retired.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open CategoryTheory Limits HomologicalComplex AlgebraicTopology.Singular

namespace HodgeLean.Foundations.Singular

private abbrev prodCircle (Y : TopCat.{0}) := TopCat.of (Y × UnitAddCircle)
private def prodArc (Y : TopCat.{0}) (a : ℝ) : Set (prodCircle Y) := Prod.snd ⁻¹' circleArc a
private abbrev U (Y : TopCat.{0}) := prodArc Y 0
private abbrev V (Y : TopCat.{0}) := prodArc Y (1 / 2)
private theorem prodArc_open (Y : TopCat.{0}) (a : ℝ) : IsOpen (prodArc Y a) :=
  (isOpen_circleArc a).preimage continuous_snd
private theorem prodArc_cover (Y : TopCat.{0}) : U Y ∪ V Y = Set.univ := by
  change Prod.snd ⁻¹' circleArc 0 ∪ Prod.snd ⁻¹' circleArc (1 / 2) = _
  rw [← Set.preimage_union, circleArc_cover]
  rfl

private def arcProjection (Y : TopCat.{0}) (a : ℝ) : TopCat.of (prodArc Y a) ⟶ Y :=
  TopCat.ofHom ⟨fun x => x.val.1, continuous_fst.comp continuous_subtype_val⟩
private def overlapProjection (Y : TopCat.{0}) : TopCat.of ↥(U Y ∩ V Y) ⟶ Y :=
  TopCat.ofHom ⟨fun x => x.val.1, continuous_fst.comp continuous_subtype_val⟩

private def prodArcEquiv (Y : TopCat.{0}) (a : ℝ) (n : ℕ) :
    Cohomology ℚ (TopCat.of (prodArc Y a)) n ≃ₗ[ℚ] Cohomology ℚ Y n :=
  let := contractibleSpace_circleArc a
  (cohomologyHomeomorphEquiv (prodSubsetHomeomorph Y UnitAddCircle (circleArc a)) n).trans
    (cohomologyProdContractibleEquiv Y (circleArc a) n)

private theorem prodArcEquiv_symm (Y : TopCat.{0}) (a : ℝ) (n : ℕ) :
    (prodArcEquiv Y a n).symm.toLinearMap = cohomologyMap ℚ n (arcProjection Y a) := by
  let := contractibleSpace_circleArc a
  change (cohomologyMap ℚ n (TopCat.ofHom ⟨prodSubsetHomeomorph Y UnitAddCircle (circleArc a),
    (prodSubsetHomeomorph Y UnitAddCircle (circleArc a)).continuous⟩)).comp
      (cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩)) = _
  rw [← cohomologyMap_comp]
  rfl

private def prodOverlapEquiv (Y : TopCat.{0}) (n : ℕ) :
    Cohomology ℚ (TopCat.of ↥(U Y ∩ V Y)) n ≃ₗ[ℚ]
      (Cohomology ℚ Y n × Cohomology ℚ Y n) :=
  (cohomologyHomeomorphEquiv
    (prodSubsetHomeomorph Y UnitAddCircle (circleArc 0 ∩ circleArc (1 / 2))) n).trans
    (cohomologyProdCircleOverlapEquiv Y n)

private def prodMiddleEquiv (Y : TopCat.{0}) (n : ℕ) :
    (mvCochainShortComplex (prodCircle Y) (U Y) (V Y)).X₂.homology n ≃ₗ[ℚ]
      (Cohomology ℚ Y n × Cohomology ℚ Y n) :=
  ((mvCohomologySumIso (prodCircle Y) (U Y) (V Y) n ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv).trans
      (LinearEquiv.prodCongr (prodArcEquiv Y 0 n) (prodArcEquiv Y (1 / 2) n))

private def overlapPoint : ↥(circleArc 0 ∩ circleArc (1 / 2)) :=
  ⟨((1 / 4 : ℝ) : UnitAddCircle), by
    constructor
    · intro h
      have := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
        (x := (1 / 4 : ℝ)) (y := 0) (by constructor <;> norm_num)
        (by constructor <;> norm_num)).mp h
      norm_num at this
    · intro h
      have := (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
        (x := (1 / 4 : ℝ)) (y := 1 / 2) (by constructor <;> norm_num)
        (by constructor <;> norm_num)).mp h
      norm_num at this⟩

private theorem overlapProjection_injective (Y : TopCat.{0}) (n : ℕ) :
    Function.Injective (cohomologyMap ℚ n (overlapProjection Y)) := by
  let sectionMap : Y ⟶ TopCat.of ↥(U Y ∩ V Y) :=
    TopCat.ofHom ⟨fun y => ⟨(y, overlapPoint.val), overlapPoint.2⟩,
      (continuous_id.prodMk continuous_const).subtype_mk _⟩
  have hc : sectionMap ≫ overlapProjection Y = 𝟙 Y := rfl
  have h := cohomologyMap_comp ℚ n sectionMap (overlapProjection Y)
  rw [hc, cohomologyMap_id] at h
  intro a b hab
  have he := LinearMap.congr_fun h a
  have he' := LinearMap.congr_fun h b
  rw [LinearMap.comp_apply, hab] at he
  exact he.trans he'.symm

set_option backward.isDefEq.respectTransparency false in
private theorem difference_sum_apply (Y : TopCat.{0}) (n : ℕ)
    (a : Cohomology ℚ (TopCat.of (U Y)) n) (b : Cohomology ℚ (TopCat.of (V Y)) n) :
    mvDifference (prodCircle Y) (U Y) (V Y) n
      (((mvCohomologySumIso (prodCircle Y) (U Y) (V Y) n ≪≫
        ModuleCat.biprodIsoProd _ _).toLinearEquiv).symm (a, b)) =
      cohomologyMap ℚ n (subsetIntersectionToLeft (prodCircle Y) (U Y) (V Y)) a -
        cohomologyMap ℚ n (subsetIntersectionToRight (prodCircle Y) (U Y) (V Y)) b := by
  have h := mvDifference_sumIso_eq (prodCircle Y) (U Y) (V Y) n
  have h' := congrArg (fun f => (ModuleCat.biprodIsoProd
    (Cohomology ℚ (TopCat.of (U Y)) n) (Cohomology ℚ (TopCat.of (V Y)) n)).inv ≫ f) h
  simp only [biprod.desc_eq, Preadditive.comp_add, ← Category.assoc,
    ModuleCat.biprodIsoProd_inv_comp_fst, ModuleCat.biprodIsoProd_inv_comp_snd,
    Preadditive.comp_neg] at h'
  convert ConcreteCategory.congr_hom h' (a, b) using 1
  · rfl
  · rfl
  · change cohomologyMap ℚ n (subsetIntersectionToLeft (prodCircle Y) (U Y) (V Y)) a -
        cohomologyMap ℚ n (subsetIntersectionToRight (prodCircle Y) (U Y) (V Y)) b =
      cohomologyMap ℚ n (subsetIntersectionToLeft (prodCircle Y) (U Y) (V Y)) a +
        -(cohomologyMap ℚ n (subsetIntersectionToRight (prodCircle Y) (U Y) (V Y)) b)
    exact sub_eq_add_neg _ _

private theorem prodDifference_apply (Y : TopCat.{0}) (n : ℕ)
    (a b : Cohomology ℚ Y n) :
    mvDifference (prodCircle Y) (U Y) (V Y) n ((prodMiddleEquiv Y n).symm (a, b)) =
      cohomologyMap ℚ n (overlapProjection Y) (a - b) := by
  change mvDifference _ _ _ n
    (((mvCohomologySumIso (prodCircle Y) (U Y) (V Y) n ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv).symm
      ((prodArcEquiv Y 0 n).symm a, (prodArcEquiv Y (1 / 2) n).symm b)) = _
  rw [difference_sum_apply]
  change cohomologyMap ℚ n (subsetIntersectionToLeft (prodCircle Y) (U Y) (V Y))
      ((prodArcEquiv Y 0 n).symm.toLinearMap a) -
    cohomologyMap ℚ n (subsetIntersectionToRight (prodCircle Y) (U Y) (V Y))
      ((prodArcEquiv Y (1 / 2) n).symm.toLinearMap b) = _
  rw [prodArcEquiv_symm, prodArcEquiv_symm]
  rw [← LinearMap.comp_apply, ← cohomologyMap_comp,
    ← LinearMap.comp_apply, ← cohomologyMap_comp, map_sub]
  rfl

private theorem prodDifference_range (Y : TopCat.{0}) (n : ℕ) :
    (mvDifference (prodCircle Y) (U Y) (V Y) n).range =
      (cohomologyMap ℚ n (overlapProjection Y)).range := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨⟨a, b⟩, rfl⟩ := (prodMiddleEquiv Y n).symm.surjective z
    exact ⟨a - b, (prodDifference_apply Y n a b).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨(prodMiddleEquiv Y n).symm (z, 0), ?_⟩
    simpa using prodDifference_apply Y n z 0

private instance prodMiddle_finite (Y : TopCat.{0}) (n : ℕ)
    [Module.Finite ℚ (Cohomology ℚ Y n)] :
    Module.Finite ℚ ((mvCochainShortComplex (prodCircle Y) (U Y) (V Y)).X₂.homology n) :=
  Module.Finite.equiv (prodMiddleEquiv Y n).symm

private instance prodOverlap_finite (Y : TopCat.{0}) (n : ℕ)
    [Module.Finite ℚ (Cohomology ℚ Y n)] :
    Module.Finite ℚ (Cohomology ℚ (TopCat.of ↥(U Y ∩ V Y)) n) :=
  Module.Finite.equiv (prodOverlapEquiv Y n).symm

private theorem prodMiddle_finrank (Y : TopCat.{0}) (n : ℕ)
    [Module.Finite ℚ (Cohomology ℚ Y n)] :
    Module.finrank ℚ ((mvCochainShortComplex (prodCircle Y) (U Y) (V Y)).X₂.homology n) =
      Module.finrank ℚ (Cohomology ℚ Y n) + Module.finrank ℚ (Cohomology ℚ Y n) := by
  rw [(prodMiddleEquiv Y n).finrank_eq, Module.finrank_prod]

private theorem prodOverlap_finrank (Y : TopCat.{0}) (n : ℕ)
    [Module.Finite ℚ (Cohomology ℚ Y n)] :
    Module.finrank ℚ (Cohomology ℚ (TopCat.of ↥(U Y ∩ V Y)) n) =
      Module.finrank ℚ (Cohomology ℚ Y n) + Module.finrank ℚ (Cohomology ℚ Y n) := by
  rw [(prodOverlapEquiv Y n).finrank_eq, Module.finrank_prod]

private theorem prodDifference_finrank (Y : TopCat.{0}) (n : ℕ) :
    Module.finrank ℚ (mvDifference (prodCircle Y) (U Y) (V Y) n).range =
      Module.finrank ℚ (Cohomology ℚ Y n) := by
  rw [prodDifference_range, LinearMap.finrank_range_of_inj (overlapProjection_injective Y n)]

private abbrev prodR (Y : TopCat.{0}) (n : ℕ) :=
  mvRestriction (prodCircle Y) (U Y) (V Y) (prodArc_open Y 0) (prodArc_open Y (1 / 2))
    (prodArc_cover Y) n
private abbrev prodδ (Y : TopCat.{0}) (n : ℕ) :=
  mvδ (prodCircle Y) (U Y) (V Y) (prodArc_open Y 0) (prodArc_open Y (1 / 2))
    (prodArc_cover Y) n

private def prodProjection (Y : TopCat.{0}) : prodCircle Y ⟶ Y :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

private def prodPullback (Y : TopCat.{0}) (n : ℕ) := cohomologyMap ℚ n (prodProjection Y)

private theorem prodRestriction_pullback (Y : TopCat.{0}) (n : ℕ) (a : Cohomology ℚ Y n) :
    prodMiddleEquiv Y n (prodR Y n (prodPullback Y n a)) = (a, a) := by
  change (LinearEquiv.prodCongr (prodArcEquiv Y 0 n) (prodArcEquiv Y (1 / 2) n))
    (((mvCohomologySumIso (prodCircle Y) (U Y) (V Y) n ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv) (prodR Y n (prodPullback Y n a))) = _
  rw [mvRestriction_sum_apply]
  apply Prod.ext
  · change prodArcEquiv Y 0 n
      (cohomologyMap ℚ n (topologicalSubsetInclusion (prodCircle Y) (U Y))
        (cohomologyMap ℚ n (prodProjection Y) a)) = a
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    change prodArcEquiv Y 0 n (cohomologyMap ℚ n (arcProjection Y 0) a) = a
    rw [← prodArcEquiv_symm]
    exact (prodArcEquiv Y 0 n).apply_symm_apply a
  · change prodArcEquiv Y (1 / 2) n
      (cohomologyMap ℚ n (topologicalSubsetInclusion (prodCircle Y) (V Y))
        (cohomologyMap ℚ n (prodProjection Y) a)) = a
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    change prodArcEquiv Y (1 / 2) n (cohomologyMap ℚ n (arcProjection Y (1 / 2)) a) = a
    rw [← prodArcEquiv_symm]
    exact (prodArcEquiv Y (1 / 2) n).apply_symm_apply a

private theorem prodOverlap_projection (Y : TopCat.{0}) (n : ℕ) (a : Cohomology ℚ Y n) :
    prodOverlapEquiv Y n (cohomologyMap ℚ n (overlapProjection Y) a) = (a, a) := by
  have hh : cohomologyHomeomorphEquiv
      (prodSubsetHomeomorph Y UnitAddCircle (circleArc 0 ∩ circleArc (1 / 2))) n
      (cohomologyMap ℚ n (overlapProjection Y) a) =
      cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a := by
    apply (cohomologyHomeomorphEquiv
      (prodSubsetHomeomorph Y UnitAddCircle (circleArc 0 ∩ circleArc (1 / 2))) n).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    change cohomologyMap ℚ n (overlapProjection Y) a =
      cohomologyMap ℚ n (TopCat.ofHom ⟨_, (prodSubsetHomeomorph Y UnitAddCircle
        (circleArc 0 ∩ circleArc (1 / 2))).continuous⟩)
        (cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a)
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    rfl
  change cohomologyProdCircleOverlapEquiv Y n
    (cohomologyHomeomorphEquiv
      (prodSubsetHomeomorph Y UnitAddCircle (circleArc 0 ∩ circleArc (1 / 2))) n
      (cohomologyMap ℚ n (overlapProjection Y) a)) = _
  rw [hh, cohomologyProdCircleOverlapEquiv_projection]

private theorem prodRestriction_diagonal (Y : TopCat.{0}) (n : ℕ)
    (a : Cohomology ℚ (prodCircle Y) n) :
    (prodMiddleEquiv Y n (prodR Y n a)).1 = (prodMiddleEquiv Y n (prodR Y n a)).2 := by
  have hz : mvDifference (prodCircle Y) (U Y) (V Y) n (prodR Y n a) = 0 :=
    (mv_exact₂ (prodCircle Y) (U Y) (V Y) (prodArc_open Y 0) (prodArc_open Y (1 / 2))
      (prodArc_cover Y) n _).mpr ⟨a, rfl⟩
  have he := prodDifference_apply Y n
    (prodMiddleEquiv Y n (prodR Y n a)).1 (prodMiddleEquiv Y n (prodR Y n a)).2
  rw [Prod.mk.eta, LinearEquiv.symm_apply_apply, hz] at he
  exact sub_eq_zero.mp ((overlapProjection_injective Y n)
    (he.symm.trans (map_zero _).symm))

private def prodRetraction (Y : TopCat.{0}) (n : ℕ) :
    Cohomology ℚ (prodCircle Y) n →ₗ[ℚ] Cohomology ℚ Y n :=
  (LinearMap.fst ℚ _ _).comp ((prodMiddleEquiv Y n).toLinearMap.comp (prodR Y n))

private def prodConnectingInclusion (Y : TopCat.{0}) (n : ℕ) :
    Cohomology ℚ Y n →ₗ[ℚ] Cohomology ℚ (prodCircle Y) (n + 1) :=
  (prodδ Y n).comp ((prodOverlapEquiv Y n).symm.toLinearMap.comp (LinearMap.inl ℚ _ _))

private theorem prodδ_diagonal (Y : TopCat.{0}) (n : ℕ) (a : Cohomology ℚ Y n) :
    prodδ Y n (cohomologyMap ℚ n (overlapProjection Y) a) = 0 := by
  apply (mv_exact₃ (prodCircle Y) (U Y) (V Y) (prodArc_open Y 0) (prodArc_open Y (1 / 2))
    (prodArc_cover Y) n _).mpr
  refine ⟨(prodMiddleEquiv Y n).symm (a, 0), ?_⟩
  simpa only [sub_zero] using prodDifference_apply Y n a 0

private theorem prodδ_pair (Y : TopCat.{0}) (n : ℕ) (a b : Cohomology ℚ Y n) :
    prodδ Y n ((prodOverlapEquiv Y n).symm (a, b)) =
      prodConnectingInclusion Y n (a - b) := by
  have hh : (prodOverlapEquiv Y n).symm (a, b) =
      (prodOverlapEquiv Y n).symm (a - b, 0) + cohomologyMap ℚ n (overlapProjection Y) b := by
    apply (prodOverlapEquiv Y n).injective
    rw [map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, prodOverlap_projection]
    ext <;> simp
  rw [hh, map_add, prodδ_diagonal, add_zero]
  rfl

private theorem prodConnectingInclusion_injective (Y : TopCat.{0}) (n : ℕ) :
    Function.Injective (prodConnectingInclusion Y n) := by
  suffices hz : ∀ b, prodConnectingInclusion Y n b = 0 → b = 0 by
    intro a b h
    exact sub_eq_zero.mp (hz (a - b) (by rw [map_sub, h, sub_self]))
  intro b hb
  obtain ⟨z, hz⟩ := (mv_exact₃ (prodCircle Y) (U Y) (V Y)
    (prodArc_open Y 0) (prodArc_open Y (1 / 2)) (prodArc_cover Y) n _).mp hb
  have hm : (prodOverlapEquiv Y n).symm (b, 0) ∈
      (cohomologyMap ℚ n (overlapProjection Y)).range := by
    rw [← prodDifference_range]
    exact ⟨z, hz⟩
  obtain ⟨a, ha⟩ := hm
  have hh := congrArg (prodOverlapEquiv Y n) ha
  rw [prodOverlap_projection, LinearEquiv.apply_symm_apply] at hh
  exact (congrArg Prod.fst hh).symm.trans (congrArg Prod.snd hh)

private theorem prodConnectingInclusion_exact (Y : TopCat.{0}) (n : ℕ) :
    Function.Exact (prodConnectingInclusion Y n) (prodRetraction Y (n + 1)) := by
  intro z
  constructor
  · intro hz
    have hr : prodR Y (n + 1) z = 0 := by
      apply (prodMiddleEquiv Y (n + 1)).injective
      rw [map_zero]
      apply Prod.ext
      · exact hz
      · exact (prodRestriction_diagonal Y (n + 1) z).symm.trans hz
    obtain ⟨w, hw⟩ := (mv_exact₁ (prodCircle Y) (U Y) (V Y)
      (prodArc_open Y 0) (prodArc_open Y (1 / 2)) (prodArc_cover Y) n z).mp hr
    obtain ⟨⟨a, b⟩, rfl⟩ := (prodOverlapEquiv Y n).symm.surjective w
    exact ⟨a - b, (prodδ_pair Y n a b).symm.trans hw⟩
  · rintro ⟨b, rfl⟩
    have hr : prodR Y (n + 1) (prodConnectingInclusion Y n b) = 0 :=
      (mv_exact₁ (prodCircle Y) (U Y) (V Y) (prodArc_open Y 0) (prodArc_open Y (1 / 2))
        (prodArc_cover Y) n _).mpr ⟨(prodOverlapEquiv Y n).symm (b, 0), rfl⟩
    change (prodMiddleEquiv Y (n + 1) (prodR Y (n + 1) _)).1 = 0
    rw [hr, map_zero]
    rfl

private theorem split_sum_bijective {A B C : Type} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] [AddCommGroup C] [Module ℚ C]
    (p : A →ₗ[ℚ] C) (j : B →ₗ[ℚ] C) (r : C →ₗ[ℚ] A)
    (hp : ∀ a, r (p a) = a) (hj : Function.Injective j) (he : Function.Exact j r) :
    Function.Bijective (p.coprod j) := by
  have hrj (b : B) : r (j b) = 0 := (he _).mpr ⟨b, rfl⟩
  constructor
  · suffices hz : ∀ z, p.coprod j z = 0 → z = 0 by
      intro a b h
      exact sub_eq_zero.mp (hz (a - b) (by rw [map_sub, h, sub_self]))
    rintro ⟨a, b⟩ h
    have ha := congrArg r h
    change r (p a + j b) = r 0 at ha
    rw [map_add, hp, hrj, map_zero, add_zero] at ha
    subst a
    change p 0 + j b = 0 at h
    rw [map_zero, zero_add] at h
    have hb := hj (h.trans (map_zero j).symm)
    subst b
    rfl
  · intro z
    have hz : r (z - p (r z)) = 0 := by rw [map_sub, hp, sub_self]
    obtain ⟨b, hb⟩ := (he _).mp hz
    refine ⟨(r z, b), ?_⟩
    change p (r z) + j b = z
    rw [hb]
    abel

private def prodCircleProjection (Y : TopCat.{0}) : prodCircle Y ⟶ TopCat.of UnitAddCircle :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

private def prodCircleClass (Y : TopCat.{0}) :=
  cohomologyMap ℚ 1 (prodCircleProjection Y) circleClass

private def prodIndicator (Y : TopCat.{0}) :=
  cohomologyMap ℚ 0 (preimageOverlapMap (prodCircleProjection Y) (circleArc 0) (circleArc (1 / 2)))
    circleOverlapIndicator

private theorem prodδ_indicator (Y : TopCat.{0}) : prodδ Y 0 (prodIndicator Y) = prodCircleClass Y :=
  (mvδ_preimage (prodCircleProjection Y) (circleArc 0) (circleArc (1 / 2))
    (isOpen_circleArc 0) (isOpen_circleArc (1 / 2)) circleArc_cover (prodArc_cover Y) 0
    circleOverlapIndicator).symm

private theorem prodOverlap_indicator (Y : TopCat.{0}) :
    prodOverlapEquiv Y 0 (prodIndicator Y) = (unit (R := ℚ) Y, 0) := by
  change cohomologyProdCircleOverlapEquiv Y 0
    (cohomologyHomeomorphEquiv
      (prodSubsetHomeomorph Y UnitAddCircle (circleArc 0 ∩ circleArc (1 / 2))) 0
      (prodIndicator Y)) = _
  change cohomologyProdCircleOverlapEquiv Y 0
    (cohomologyMap ℚ 0 (TopCat.ofHom (Y := TopCat.of ↥(U Y ∩ V Y)) ⟨_, (prodSubsetHomeomorph Y UnitAddCircle
      (circleArc 0 ∩ circleArc (1 / 2))).symm.continuous⟩)
      (cohomologyMap ℚ 0
        (preimageOverlapMap (prodCircleProjection Y) (circleArc 0) (circleArc (1 / 2)))
        circleOverlapIndicator)) = _
  change cohomologyProdCircleOverlapEquiv Y 0
    (cohomologyMap ℚ 0 (TopCat.ofHom (Y := TopCat.of ↥(U Y ∩ V Y))
      ⟨_, (prodSubsetHomeomorph Y UnitAddCircle
        (circleArc 0 ∩ circleArc (1 / 2))).symm.continuous⟩)
      (cohomologyMap ℚ 0 (TopCat.ofHom (X := TopCat.of ↥(U Y ∩ V Y))
        ⟨fun z => ⟨z.val.2, z.property⟩, (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩) circleOverlapIndicator)) = _
  rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
  exact cohomologyProdCircleOverlapEquiv_indicator Y

private theorem prodOverlap_cup (Y : TopCat.{0}) {p q k : ℕ} (h : p + q = k)
    (a : Cohomology ℚ (TopCat.of ↥(U Y ∩ V Y)) p)
    (b : Cohomology ℚ (TopCat.of ↥(U Y ∩ V Y)) q) :
    prodOverlapEquiv Y k (cup _ h a b) =
      (cup Y h (prodOverlapEquiv Y p a).1 (prodOverlapEquiv Y q b).1,
       cup Y h (prodOverlapEquiv Y p a).2 (prodOverlapEquiv Y q b).2) := by
  unfold prodOverlapEquiv
  simp only [LinearEquiv.trans_apply]
  change cohomologyProdCircleOverlapEquiv Y k
    (cohomologyMap ℚ k (TopCat.ofHom (Y := TopCat.of ↥(U Y ∩ V Y)) ⟨_, (prodSubsetHomeomorph Y UnitAddCircle
      (circleArc 0 ∩ circleArc (1 / 2))).symm.continuous⟩) (cup _ h a b)) = _
  rw [cohomologyMap_cup, cohomologyProdCircleOverlapEquiv_cup]
  rfl

private theorem prodConnectingInclusion_cup (Y : TopCat.{0}) (n : ℕ) (b : Cohomology ℚ Y n) :
    prodConnectingInclusion Y n b =
      (-1 : ℚ) ^ n • cup (prodCircle Y) rfl (prodPullback Y n b) (prodCircleClass Y) := by
  obtain ⟨β, hβ⟩ := cohomologyClass_surjective (prodCircle Y) n (prodPullback Y n b)
  have hr : cohomologyMap ℚ n (topologicalSubsetInclusion (prodCircle Y) (U Y ∩ V Y))
      (cohomologyClass (prodCircle Y) n β) = cohomologyMap ℚ n (overlapProjection Y) b := by
    rw [hβ]
    change cohomologyMap ℚ n _ (cohomologyMap ℚ n (prodProjection Y) b) = _
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    rfl
  have hi : cup (TopCat.of ↥(U Y ∩ V Y)) (Nat.add_zero n)
      (cohomologyMap ℚ n (overlapProjection Y) b) (prodIndicator Y) =
      (prodOverlapEquiv Y n).symm (b, 0) := by
    apply (prodOverlapEquiv Y n).injective
    rw [prodOverlap_cup, prodOverlap_projection, prodOverlap_indicator, LinearEquiv.apply_symm_apply]
    simp only [cup_one, map_zero]
  have hm := mvδ_cup_left_zero (prodCircle Y) (U Y) (V Y)
    (prodArc_open Y 0) (prodArc_open Y (1 / 2)) (prodArc_cover Y) n β (prodIndicator Y)
  rw [hr, hi, hβ, prodδ_indicator] at hm
  exact hm

private def prodCircleMVEquiv (Y : TopCat.{0}) (n : ℕ) :
    (Cohomology ℚ Y (n + 1) × Cohomology ℚ Y n) ≃ₗ[ℚ]
      Cohomology ℚ (prodCircle Y) (n + 1) :=
  LinearEquiv.ofBijective ((prodPullback Y (n + 1)).coprod (prodConnectingInclusion Y n))
    (split_sum_bijective _ _ (prodRetraction Y (n + 1))
      (fun a => congrArg Prod.fst (prodRestriction_pullback Y (n + 1) a))
      (prodConnectingInclusion_injective Y n) (prodConnectingInclusion_exact Y n))

private theorem sign_square (n : ℕ) : (-1 : ℚ) ^ n * (-1 : ℚ) ^ n = 1 := by
  rw [← mul_pow]
  norm_num

private def signEquiv (W : Type) [AddCommGroup W] [Module ℚ W] (n : ℕ) : W ≃ₗ[ℚ] W where
  toFun w := (-1 : ℚ) ^ n • w
  invFun w := (-1 : ℚ) ^ n • w
  map_add' _ _ := smul_add _ _ _
  map_smul' _ _ := smul_comm _ _ _
  left_inv w := by dsimp only; rw [smul_smul, sign_square, one_smul]
  right_inv w := by dsimp only; rw [smul_smul, sign_square, one_smul]

/-- The circle product theorem in positive degrees, without finite-dimensionality:
`(a,b)` maps to `p* a + p* b ∪ π* x`. Successor indexing avoids truncated natural-number
subtraction at degree zero. The inverse is obtained from the split Mayer–Vietoris sequence.
Source: Hatcher, *Algebraic Topology*, Theorem 3.15 for the Künneth shape and §3.2
for the cup product; the two-arc proof is constructed here.
HC no distance; AV milestone no distance. Stages S4 and S5 give C7 for the model torus;
this stage retires no stated hypothesis.
-/
def prodCircleCohomologyEquiv (Y : TopCat.{0}) (n : ℕ) :
    (Cohomology ℚ Y (n + 1) × Cohomology ℚ Y n) ≃ₗ[ℚ]
      Cohomology ℚ (TopCat.of (Y × UnitAddCircle)) (n + 1) :=
  (LinearEquiv.prodCongr (LinearEquiv.refl ℚ _) (signEquiv _ n)).trans (prodCircleMVEquiv Y n)

/-- The product equivalence is the specified cup-product map, not a basis-chosen isomorphism.
Source: constructed here from the signed left-module identity and the defining circle class.
-/
theorem prodCircleCohomologyEquiv_apply (Y : TopCat.{0}) (n : ℕ)
    (a : Cohomology ℚ Y (n + 1)) (b : Cohomology ℚ Y n) :
    prodCircleCohomologyEquiv Y n (a, b) =
      cohomologyMap ℚ (n + 1) (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a +
      cup (TopCat.of (Y × UnitAddCircle)) rfl
        (cohomologyMap ℚ n (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) b)
        (cohomologyMap ℚ 1 (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) circleClass) := by
  change prodPullback Y (n + 1) a + prodConnectingInclusion Y n ((-1 : ℚ) ^ n • b) = _
  rw [map_smul, prodConnectingInclusion_cup, smul_smul, sign_square, one_smul]
  rfl

example (Y : TopCat.{0}) (n : ℕ) : prodCircleCohomologyEquiv Y n (0, 0) = 0 := map_zero _

/-- In degree zero the product projection alone is an equivalence. This is the
zero-degree case of the circle product theorem, with negative cohomology omitted.
Source: Hatcher, *Algebraic Topology*, §3.1, degree-zero cohomology and Mayer–Vietoris.
HC no distance; AV milestone no distance.
-/
def prodCircleCohomologyZeroEquiv (Y : TopCat.{0}) :
    Cohomology ℚ Y 0 ≃ₗ[ℚ] Cohomology ℚ (TopCat.of (Y × UnitAddCircle)) 0 where
  toLinearMap := prodPullback Y 0
  invFun := prodRetraction Y 0
  left_inv a := congrArg Prod.fst (prodRestriction_pullback Y 0 a)
  right_inv a := by
    apply mvRestriction_zero_injective (prodCircle Y) (U Y) (V Y)
      (prodArc_open Y 0) (prodArc_open Y (1 / 2)) (prodArc_cover Y)
    apply (prodMiddleEquiv Y 0).injective
    change prodMiddleEquiv Y 0 (prodR Y 0 (prodPullback Y 0 (prodRetraction Y 0 a))) =
      prodMiddleEquiv Y 0 (prodR Y 0 a)
    rw [prodRestriction_pullback]
    apply Prod.ext
    · rfl
    · exact prodRestriction_diagonal Y 0 a

example (Y : TopCat.{0}) (a : Cohomology ℚ Y 0) :
    prodCircleCohomologyZeroEquiv Y a =
      cohomologyMap ℚ 0 (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) a := rfl

#print axioms prodCircleCohomologyEquiv
#print axioms prodCircleCohomologyEquiv_apply
#print axioms prodCircleCohomologyZeroEquiv

/-- Products with a circle preserve degreewise finite-dimensional rational cohomology.
Source: Hatcher, *Algebraic Topology*, §2.2 and §3.1, Mayer–Vietoris.
-/
theorem finite_cohomology_prod_circle (Y : TopCat.{0})
    [∀ k, Module.Finite ℚ (Cohomology ℚ Y k)] (k : ℕ) :
    Module.Finite ℚ (Cohomology ℚ (TopCat.of (Y × UnitAddCircle)) k) := by
  cases k with
  | zero =>
    exact Module.Finite.of_injective (prodR Y 0)
      (mvRestriction_zero_injective (prodCircle Y) (U Y) (V Y)
        (prodArc_open Y 0) (prodArc_open Y (1 / 2)) (prodArc_cover Y))
  | succ n =>
    let r := prodR Y (n + 1)
    have hk : r.ker = (prodδ Y n).range := LinearMap.exact_iff.mp
      (mv_exact₁ (prodCircle Y) (U Y) (V Y) (prodArc_open Y 0) (prodArc_open Y (1 / 2))
        (prodArc_cover Y) n)
    let : Module.Finite ℚ r.ker := by rw [hk]; infer_instance
    let : Module.Finite ℚ (Cohomology ℚ (prodCircle Y) (n + 1) ⧸ r.ker) :=
      Module.Finite.equiv r.quotKerEquivRange.symm
    exact Module.Finite.of_submodule_quotient r.ker

/-- The circle-factor recurrence for rational Betti numbers, obtained from the
Mayer–Vietoris sequence on the two arcs.
Source: Hatcher, *Algebraic Topology*, §2.2, §3.1, and Example 3.11.
HC no distance; AV milestone no distance.
-/
theorem finrank_cohomology_prod_circle (Y : TopCat.{0})
    [∀ k, FiniteDimensional ℚ (Cohomology ℚ Y k)] (k : ℕ) :
    Module.finrank ℚ (Cohomology ℚ (TopCat.of (Y × UnitAddCircle)) (k + 1)) =
      Module.finrank ℚ (Cohomology ℚ Y (k + 1)) + Module.finrank ℚ (Cohomology ℚ Y k) := by
  let := finite_cohomology_prod_circle Y (k + 1)
  let r := prodR Y (k + 1)
  let b := prodδ Y k
  let d := mvDifference (prodCircle Y) (U Y) (V Y) k
  let d' := mvDifference (prodCircle Y) (U Y) (V Y) (k + 1)
  have hk₁ : r.ker = b.range := LinearMap.exact_iff.mp
    (mv_exact₁ (prodCircle Y) (U Y) (V Y) (prodArc_open Y 0) (prodArc_open Y (1 / 2))
      (prodArc_cover Y) k)
  have hk₂ : d'.ker = r.range := LinearMap.exact_iff.mp
    (mv_exact₂ (prodCircle Y) (U Y) (V Y) (prodArc_open Y 0) (prodArc_open Y (1 / 2))
      (prodArc_cover Y) (k + 1))
  have hk₃ : b.ker = d.range := LinearMap.exact_iff.mp
    (mv_exact₃ (prodCircle Y) (U Y) (V Y) (prodArc_open Y 0) (prodArc_open Y (1 / 2))
      (prodArc_cover Y) k)
  have hd' := d'.finrank_range_add_finrank_ker
  rw [hk₂, prodDifference_finrank, prodMiddle_finrank] at hd'
  have hr : Module.finrank ℚ r.range = Module.finrank ℚ (Cohomology ℚ Y (k + 1)) :=
    Nat.add_left_cancel hd'
  have hb := b.finrank_range_add_finrank_ker
  rw [hk₃, prodDifference_finrank, prodOverlap_finrank] at hb
  have hb' : Module.finrank ℚ b.range = Module.finrank ℚ (Cohomology ℚ Y k) :=
    Nat.add_right_cancel hb
  have h := r.finrank_range_add_finrank_ker
  rw [hk₁, hr, hb'] at h
  exact h.symm

/-- Separate the last circle coordinate of the finite-dimensional unit torus.
Source: Mathlib `Homeomorph.sumArrowHomeomorphProdArrow` and `finSumFinEquiv`.
-/
def unitAddTorusSuccHomeomorph (n : ℕ) :
    UnitAddTorus (Fin (n + 1)) ≃ₜ UnitAddTorus (Fin n) × UnitAddCircle :=
  (Homeomorph.piCongrLeft (Y := fun _ => UnitAddCircle)
    (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))).symm.trans
      (Homeomorph.sumArrowHomeomorphProdArrow.trans
        ((Homeomorph.refl _).prodCongr (Homeomorph.funUnique (Fin 1) UnitAddCircle)))

example : unitAddTorusSuccHomeomorph 0 (fun _ => 0) = (fun _ => 0, 0) := rfl

/-- Every rational cohomology group of a finite-dimensional torus is finite-dimensional.
Source: Hatcher, *Algebraic Topology*, §2.2 and Example 3.11, induction over circle factors.
-/
theorem finite_cohomology_unitAddTorus (n k : ℕ) :
    Module.Finite ℚ (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) k) := by
  induction n generalizing k with
  | zero => exact finite_cohomology_of_contractible (UnitAddTorus (Fin 0)) k
  | succ n ih =>
    let : ∀ k, Module.Finite ℚ (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) k) := ih
    let := finite_cohomology_prod_circle (TopCat.of (UnitAddTorus (Fin n))) k
    exact Module.Finite.equiv (cohomologyHomeomorphEquiv (unitAddTorusSuccHomeomorph n) k).symm

/-- T11: the rational Betti numbers of the standard real torus are binomial coefficients.
Source: Hatcher, *Algebraic Topology*, Example 3.11 and §2.2, Mayer–Vietoris.
HC no distance; AV milestone no distance. This is a step toward C7 and retires no hypothesis.
-/
theorem finrank_cohomology_unitAddTorus (n k : ℕ) :
    Module.finrank ℚ (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) k) = n.choose k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simpa using finrank_cohomology_of_contractible (UnitAddTorus (Fin 0)) 0
    | succ k => simpa using finrank_cohomology_of_contractible (UnitAddTorus (Fin 0)) (k + 1)
  | succ n ih =>
    cases k with
    | zero => simpa using finrank_cohomology_zero_of_pathConnected (TopCat.of (UnitAddTorus (Fin (n + 1))))
    | succ k =>
      let := finite_cohomology_unitAddTorus n
      rw [(cohomologyHomeomorphEquiv (unitAddTorusSuccHomeomorph n) (k + 1)).finrank_eq,
        finrank_cohomology_prod_circle (TopCat.of (UnitAddTorus (Fin n))), ih, ih, Nat.choose_succ_succ']
      exact Nat.add_comm _ _

example : Cohomology ℚ (TopCat.of (UnitAddTorus (Fin 0))) 0 ≃ₗ[ℚ] ℚ :=
  (cohomologyHomeomorphEquiv
    (Homeomorph.homeomorphOfUnique (UnitAddTorus (Fin 0)) PUnit) 0).trans
    (pointCohomologyZeroEquiv (R := ℚ))

example : Module.finrank ℚ (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin 0))) 0) = 1 := by
  simpa using finrank_cohomology_unitAddTorus 0 0

example : Module.finrank ℚ (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin 2))) 2) = 1 := by
  rw [finrank_cohomology_unitAddTorus]
  decide

example : Module.finrank ℚ (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin 3))) 1) = 3 := by
  rw [finrank_cohomology_unitAddTorus]
  decide

example (n k : ℕ) (h : n < k) :
    Module.finrank ℚ (Cohomology ℚ (TopCat.of (UnitAddTorus (Fin n))) k) = 0 := by
  rw [finrank_cohomology_unitAddTorus, Nat.choose_eq_zero_of_lt h]

#print axioms unitAddTorusSuccHomeomorph
#print axioms finite_cohomology_unitAddTorus
#print axioms finrank_cohomology_unitAddTorus
#print axioms finite_cohomology_prod_circle
#print axioms finrank_cohomology_prod_circle

end HodgeLean.Foundations.Singular
