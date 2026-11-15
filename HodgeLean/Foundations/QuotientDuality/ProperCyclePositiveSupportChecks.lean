import Mathlib.LinearAlgebra.Dual.Lemmas
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeForgetNaturality
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian9OrientationProofs
import HodgeLean.Foundations.Singular.TorusRingChecks
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapOpenCollar
import HodgeLean.Foundations.QuotientDuality.ProperCycleCapPairing
import HodgeLean.Foundations.AlgebraicTopology.Singular.CohomologyWithSupport

/-! # Positive-degree supported cap on an actual factor subtorus

HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Singular
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.QuotientDuality.ProperCyclePositiveSupportChecks

private abbrev N := TopCat.of (UnitAddTorus (Fin 2))
private abbrev X := TopCat.of (N × N)
private def p : N := bh9_squareTorus 0
private def z := (relativeHomologyProjection ℚ (pointComplementPair p) 2).hom bh9_cellClass
private lemma z_ne_zero : z ≠ 0 := by
  intro hz
  apply bh9_squareTorus_diskClass_ne_zero
  apply bh9_torusCellToLocal_injective
  rw [← bh9_cellClass_relative, bh9_torusProjection_local]
  exact hz.trans (map_zero _).symm

private def aN : CohomologyWithSupport ℚ N {p} 2 := normalizedRelativeCoclass z z_ne_zero
private def aAbs := forgetSupport ℚ N {p} 2 aN
private lemma aAbs_pairing : cohomologyEquivDualHomology ℚ N 2 aAbs bh9_cellClass = 1 := by
  rw [show aAbs = forgetSupport ℚ N {p} 2 aN from rfl,
    cohomologyEquivDualHomology_forgetSupport]
  exact normalizedRelativeCoclass_pairing_self z z_ne_zero
private lemma aAbs_ne_zero : aAbs ≠ 0 := by
  intro h
  have hh := aAbs_pairing
  rw [h, map_zero, LinearMap.zero_apply] at hh
  exact zero_ne_one hh

private def pr₁ : X ⟶ N := TopCat.ofHom ⟨Prod.fst, continuous_fst⟩
private def pr₂ : X ⟶ N := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
private def S : Set X := pr₁ ⁻¹' {p}
private def a : CohomologyWithSupport ℚ X S 2 := cohomologyWithSupportMap ℚ 2 pr₁ {p} aN
private def u : Cohomology ℚ X 2 := cohomologyMap ℚ 2 pr₂ aAbs
private def aX := forgetSupport ℚ X S 2 a
private lemma aX_formula : aX = cohomologyMap ℚ 2 pr₁ aAbs := by
  exact properCycle_relative_forget_naturality
    (TopPair.ofSubsetHom pr₁ (fun _ h => h)) 2 aN
private def cupTop : Cohomology ℚ X 4 := cup (R := ℚ) (p := 2) (q := 2) (k := 4) X rfl aX u

private lemma aAbs_top : aAbs = cupMulti N 2 torusCoordinateClass := by
  let t := cup (R := ℚ) (p := 1) (q := 1) (k := 2) N rfl
    (torusCoordinateClass 0) (torusCoordinateClass 1)
  have ht : t ≠ 0 := torus_coordinate_two_cup_ne_zero
  have hspan : Submodule.span ℚ {t} = ⊤ :=
    (finrank_eq_one_iff_of_nonzero t ht).mp
      ((finrank_cohomology_unitAddTorus 2 2).trans (by decide))
  obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp
    (show aAbs ∈ Submodule.span ℚ {t} by rw [hspan]; exact Submodule.mem_top)
  have hp := aAbs_pairing
  rw [← hq, map_smul, LinearMap.smul_apply,
    show cohomologyEquivDualHomology ℚ N 2 t bh9_cellClass = 1 from
      bh9_cellClass_topCup_pairing, smul_eq_mul, mul_one] at hp
  have he : aAbs = t := by rw [← hq, hp, one_smul]
  rw [he, cupMulti_succ N 1 rfl, cupMulti_succ N 0 rfl, cupMulti_zero, cup_one]
  rfl

private lemma lambda_ne_zero : cupTop ≠ 0 := by
  let T4 := TopCat.of (UnitAddTorus (Fin 4))
  let front := cupMulti T4 2 (fun i => torusCoordinateClass (Fin.castAdd 2 i))
  let back := cupMulti T4 2 (fun i => torusCoordinateClass (Fin.natAdd 2 i))
  let f : T4 ⟶ X := TopCat.ofHom
    ⟨fun t => ((fun i => t (Fin.castAdd 2 i)), (fun i => t (Fin.natAdd 2 i))),
      (continuous_pi fun i => continuous_apply _).prodMk
        (continuous_pi fun i => continuous_apply _)⟩
  have hfront : cohomologyMap ℚ 2 f aX = front := by
    rw [aX_formula, ← LinearMap.comp_apply, ← cohomologyMap_comp, aAbs_top,
      cohomologyMap_cupMulti]
    apply congrArg (cupMulti T4 2)
    funext i
    unfold torusCoordinateClass
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    rfl
  have hback : cohomologyMap ℚ 2 f u = back := by
    change cohomologyMap ℚ 2 f (cohomologyMap ℚ 2 pr₂ aAbs) = _
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp, aAbs_top, cohomologyMap_cupMulti]
    apply congrArg (cupMulti T4 2)
    funext i
    unfold torusCoordinateClass
    rw [← LinearMap.comp_apply, ← cohomologyMap_comp]
    rfl
  have hcup : cup (R := ℚ) (p := 2) (q := 2) (k := 4) T4 rfl front back ≠ 0 := by
    have ht := torus_top_cupMulti_ne_zero 4
    rw [cupMulti_append T4 2 (fun i => torusCoordinateClass (Fin.natAdd 2 i))
      2 (fun i => torusCoordinateClass (Fin.castAdd 2 i)) 4 rfl _
      (fun _ => rfl) (fun _ => rfl)] at ht
    exact ht
  intro h
  apply hcup
  have hh := congrArg (cohomologyMap ℚ 4 f) h
  change cohomologyMap ℚ 4 f (cup (R := ℚ) (p := 2) (q := 2) (k := 4) X rfl aX u) = _ at hh
  rw [cohomologyMap_cup, hfront, hback, map_zero] at hh
  exact hh

private lemma normalized_top_exists : ∃ c : Homology ℚ X 4,
    cohomologyEquivDualHomology ℚ X 4 cupTop c = 1 := by
  classical
  have hf : cohomologyEquivDualHomology ℚ X 4 cupTop ≠ 0 := by
    intro h
    apply lambda_ne_zero
    exact (cohomologyEquivDualHomology ℚ X 4).injective (h.trans (map_zero _).symm)
  have hex : ∃ c, cohomologyEquivDualHomology ℚ X 4 cupTop c ≠ 0 := by
    by_contra! h
    apply hf
    ext c
    exact h c
  obtain ⟨c, hc⟩ := hex
  refine ⟨(cohomologyEquivDualHomology ℚ X 4 cupTop c)⁻¹ • c, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hc]
private def c : Homology ℚ X 4 := normalized_top_exists.choose
private lemma c_pairing : cohomologyEquivDualHomology ℚ X 4 cupTop c = 1 :=
  normalized_top_exists.choose_spec
private def cap : Homology ℚ X 2 := capCohomologyLinear ℚ X 2 2
  ((cochainCohomologyEquiv ℚ X 2).symm aX) c
private lemma cap_pairing : cohomologyEquivDualHomology ℚ X 2 u cap = 1 := by
  exact (properCycle_cup_cap X 2 2 aX u c).symm.trans c_pairing
private lemma cap_ne_zero : cap ≠ 0 := by
  intro h
  have hh := cap_pairing
  rw [h, map_zero] at hh
  exact zero_ne_one hh

/-- A genuine degree-two class supported on a factor two-torus has nonzero actual cap in the compact connected four-torus, detected by the other factor's degree-two class.
Source: Hatcher, Algebraic Topology, sections 3.2 and 3.3; the checked normalized torus cell and field-coefficient product comparison.
HC no distance; AV milestone no distance. -/
theorem global_support_factorization_positive_cap :
    CompactSpace X ∧ ConnectedSpace X ∧
      cohomologyEquivDualHomology ℚ X 2 u cap = 1 ∧ cap ≠ 0 :=
  ⟨inferInstance, inferInstance, cap_pairing, cap_ne_zero⟩

example : CompactSpace X ∧ ConnectedSpace X ∧
    cohomologyEquivDualHomology ℚ X 2 u cap = 1 ∧ cap ≠ 0 :=
  global_support_factorization_positive_cap

private def Un : Set N := bh9_torusSkeletonᶜ
private lemma p_mem_Un : p ∈ Un := by
  let mid : Set.Ioo (0 : ℝ) 1 × Set.Ioo (0 : ℝ) 1 :=
    (⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩,
      ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩)
  have hm := bh9_squareTorus_openCell mid
  have hp : p = (bh9_openCellHomeomorph mid).val := by
    convert hm using 1
    congr 1
    ext i
    norm_num [p, mid]
    rfl
  rw [hp]
  exact (bh9_openCellHomeomorph mid).property
private lemma Un_open : IsOpen Un :=
  ((isClosed_eq (continuous_apply (0 : Fin 2)) continuous_const).union
    (isClosed_eq (continuous_apply (1 : Fin 2)) continuous_const)).isOpen_compl
private abbrev U := TopCat.of (Un × N)
private def collarMap : U ⟶ X := TopCat.ofHom
  ⟨fun v => (v.1.val, v.2),
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd⟩
private def collarInclusion : TopCat.of S ⟶ U := TopCat.ofHom
  ⟨fun v => (⟨p, p_mem_Un⟩, v.val.2),
    continuous_const.prodMk (continuous_snd.comp continuous_subtype_val)⟩
private def collarRetraction : U ⟶ TopCat.of S := TopCat.ofHom
  ⟨fun v => ⟨(p, v.2), rfl⟩, (continuous_const.prodMk continuous_snd).subtype_mk _⟩
private lemma collar_inclusion : collarInclusion ≫ collarMap = (TopPair.ofSubset (X := X) S).map := by
  ext v : 1
  apply Prod.ext
  · exact (show v.val.1 = p from v.property).symm
  · rfl
private lemma collar_openEmbedding : Topology.IsOpenEmbedding collarMap :=
  Un_open.isOpenEmbedding_subtypeVal.prodMap Topology.IsOpenEmbedding.id
private def collar_homotopy : TopCat.Homotopy (𝟙 U) (collarRetraction ≫ collarInclusion) := by
  letI : ContractibleSpace (Set.Ioo (0 : ℝ) 1) :=
    (convex_Ioo (0 : ℝ) 1).contractibleSpace ⟨(1 / 2 : ℝ), by constructor <;> norm_num⟩
  letI : ContractibleSpace Un := bh9_openCellHomeomorph.symm.contractibleSpace
  let q := (id_nullhomotopic Un).choose
  let Hq := Classical.choice (id_nullhomotopic Un).choose_spec
  let Hn := Hq.trans ((PathConnectedSpace.somePath q ⟨p, p_mem_Un⟩).toHomotopyConst)
  exact Hn.prodMap (ContinuousMap.Homotopy.refl (ContinuousMap.id N))
private lemma support_cap_lift : ∃ b : Homology ℚ (TopCat.of S) 2,
    homologyMap ℚ 2 (TopPair.ofSubset (X := X) S).map b = cap :=
  properCycle_cap_factor_through_open_collar X S
    (isClosed_singleton.preimage continuous_fst) U collarInclusion collarMap
    collar_inclusion collar_openEmbedding collarRetraction collar_homotopy 2 2 a c
private def b : Homology ℚ (TopCat.of S) 2 := support_cap_lift.choose
private lemma b_image : homologyMap ℚ 2 (TopPair.ofSubset (X := X) S).map b = cap :=
  support_cap_lift.choose_spec
private lemma b_ne_zero : b ≠ 0 := by
  intro h
  have hh := b_image
  rw [h, map_zero] at hh
  exact cap_ne_zero hh.symm

/-- The actual positive-degree cap factors through a nonzero class of the proper factor subtorus, with its literal support inclusion equation.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3; the constructed open collar and original supported cap.
HC no distance; AV milestone no distance. -/
theorem global_support_factorization_supported_example : b ≠ 0 ∧
    homologyMap ℚ 2 (TopPair.ofSubset (X := X) S).map b = cap ∧
    cohomologyEquivDualHomology ℚ X 2 u cap = 1 := ⟨b_ne_zero, b_image, cap_pairing⟩

example : b ≠ 0 ∧ homologyMap ℚ 2 (TopPair.ofSubset (X := X) S).map b = cap ∧
    cohomologyEquivDualHomology ℚ X 2 u cap = 1 := global_support_factorization_supported_example

/-- Erasing the intrinsic supported homology class breaks the actual inclusion/cap equation in degree two.
Source: Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance. -/
theorem global_support_factorization_supported_zero_falsification :
    homologyMap ℚ 2 (TopPair.ofSubset (X := X) S).map
      (0 : Homology ℚ (TopCat.of S) 2) ≠ cap := by
  rw [map_zero]
  exact Ne.symm cap_ne_zero

example : homologyMap ℚ 2 (TopPair.ofSubset (X := X) S).map
    (0 : Homology ℚ (TopCat.of S) 2) ≠ cap := global_support_factorization_supported_zero_falsification

/-- Reversing the intrinsic supported orientation also breaks the actual positive-degree factorization.
Source: Hatcher, Algebraic Topology, section 3.3.
HC no distance; AV milestone no distance. -/
theorem global_support_factorization_supported_sign_falsification :
    homologyMap ℚ 2 (TopPair.ofSubset (X := X) S).map (-b) ≠ cap := by
  rw [map_neg, b_image]
  intro h
  have hz : (2 : ℚ) • cap = 0 := by
    rw [show (2 : ℚ) = 1 + 1 by norm_num, add_smul, one_smul]
    exact neg_eq_iff_add_eq_zero.mp h
  exact (smul_ne_zero (by norm_num : (2 : ℚ) ≠ 0) cap_ne_zero) hz

example : homologyMap ℚ 2 (TopPair.ofSubset (X := X) S).map (-b) ≠ cap :=
  global_support_factorization_supported_sign_falsification

private def T : Set X := S ∪ {v | v.1 = 0}
private lemma hST : S ⊆ T := Set.subset_union_left
private def supportMap : TopCat.of S ⟶ TopCat.of T := TopCat.ofHom
  ⟨fun v => ⟨v.val, hST v.property⟩, continuous_subtype_val.subtype_mk _⟩
private def bT := homologyMap ℚ 2 supportMap b
private lemma bT_image : homologyMap ℚ 2 (TopPair.ofSubset (X := X) T).map bT = cap := by
  have he : supportMap ≫ (TopPair.ofSubset (X := X) T).map =
      (TopPair.ofSubset (X := X) S).map := by ext v : 1; rfl
  have hh := LinearMap.congr_fun
    (homologyMap_comp ℚ 2 supportMap (TopPair.ofSubset (X := X) T).map) b
  rw [he] at hh
  exact hh.symm.trans b_image

/-- Enlarging one factor subtorus to two disjoint factor subtori preserves both the actual supported homology image and the nonzero cap. The support inclusion is strict and both components have real dimension two.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.1, support inclusions and their forgetful square.
HC no distance; AV milestone no distance. -/
theorem global_support_factorization_enlargement_square : S ≠ T ∧
    homologyMap ℚ 2 (TopPair.ofSubset (X := X) T).map bT = cap ∧
    capCohomologyLinear ℚ X 2 2 ((cochainCohomologyEquiv ℚ X 2).symm
      (forgetSupport ℚ X T 2 (enlargeSupport ℚ X hST 2 a))) c = cap := by
  refine ⟨?_, bT_image, ?_⟩
  · intro h
    have hxT : ((0 : N), (0 : N)) ∈ T := Or.inr rfl
    have hxS : ((0 : N), (0 : N)) ∈ S := h.symm ▸ hxT
    have hp0 : (0 : N) = p := hxS
    have hpSk : p ∈ bh9_torusSkeleton := hp0 ▸ (Or.inl rfl : (0 : N) ∈ bh9_torusSkeleton)
    exact p_mem_Un hpSk
  · rw [AlgebraicTopology.Singular.SupportedClasses.forget_enlarge]
    rfl

example : S ≠ T ∧ homologyMap ℚ 2 (TopPair.ofSubset (X := X) T).map bT = cap ∧
    capCohomologyLinear ℚ X 2 2 ((cochainCohomologyEquiv ℚ X 2).symm
      (forgetSupport ℚ X T 2 (enlargeSupport ℚ X hST 2 a))) c = cap :=
  global_support_factorization_enlargement_square

private def supportFactorHomeomorph : TopCat.of S ≃ₜ N where
  toFun v := v.val.2
  invFun v := ⟨(p, v), rfl⟩
  left_inv v := Subtype.ext (Prod.ext v.property.symm rfl)
  right_inv _ := rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk _
private def supportFactorHomology :
    Homology ℚ (TopCat.of S) 2 ≃ₗ[ℚ] Homology ℚ N 2 :=
  (((AlgebraicTopology.singularHomologyFunctor.{0} (ModuleCat.{0} ℚ) 2).obj (ModuleCat.of ℚ ℚ)).mapIso
    (TopCat.isoOfHomeo supportFactorHomeomorph)).toLinearEquiv
private lemma support_factor_pairing :
    cohomologyEquivDualHomology ℚ N 2 aAbs (supportFactorHomology b) = 1 := by
  change cohomologyEquivDualHomology ℚ N 2 aAbs
    (homologyMap ℚ 2 ((TopPair.ofSubset (X := X) S).map ≫ pr₂) b) = 1
  rw [homologyMap_comp, LinearMap.comp_apply, b_image,
    ← cohomologyEquivDualHomology_cohomologyMap]
  exact cap_pairing
private lemma support_factor_normalization : supportFactorHomology b = bh9_cellClass := by
  have ht := support_factor_pairing
  rw [aAbs_top, cupMulti_succ N 1 rfl, cupMulti_succ N 0 rfl,
    cupMulti_zero, cup_one] at ht
  apply Module.eval_apply_injective ℚ
  ext φ
  obtain ⟨α, rfl⟩ := (cohomologyEquivDualHomology ℚ N 2).surjective φ
  change cohomologyEquivDualHomology ℚ N 2 α (supportFactorHomology b) =
    cohomologyEquivDualHomology ℚ N 2 α bh9_cellClass
  exact (bh9_torus_pairing_of_topCup _ ht α).trans
    (bh9_torus_pairing_of_topCup _ bh9_cellClass_topCup_pairing α).symm

/-- The original positive-degree collar lift is exactly the prescribed normalized torus factor class, transported to its literal support; its actual support inclusion gives the original cap.
Source: Bredon, Sheaf Theory, V.9; Hatcher, Algebraic Topology, sections 3.2 and 3.3; bh9_cellClass_topCup_pairing.
HC no distance; AV milestone no distance. -/
theorem global_support_factorization_intrinsic_factor_example :
    b = supportFactorHomology.symm bh9_cellClass ∧
    homologyMap ℚ 2 (TopPair.ofSubset (X := X) S).map
      (supportFactorHomology.symm bh9_cellClass) = cap := by
  have hb : b = supportFactorHomology.symm bh9_cellClass := by
    apply supportFactorHomology.injective
    rw [supportFactorHomology.apply_symm_apply]
    exact support_factor_normalization
  exact ⟨hb, by rw [← hb]; exact b_image⟩

example : b = supportFactorHomology.symm bh9_cellClass ∧
    homologyMap ℚ 2 (TopPair.ofSubset (X := X) S).map
      (supportFactorHomology.symm bh9_cellClass) = cap :=
  global_support_factorization_intrinsic_factor_example

end HodgeLean.Foundations.QuotientDuality.ProperCyclePositiveSupportChecks
