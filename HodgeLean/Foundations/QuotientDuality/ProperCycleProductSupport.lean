import HodgeLean.Foundations.QuotientDuality.OrientationDefs
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeGenerator
import HodgeConjecture.Lemmas.AlgebraicTopology.LocalHomology.NormalSlicePurity

/-! # Product support reduction with arbitrary normal spaces -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- Projection of a product support pair to its actual normal-space pair.
Source: Hatcher, Algebraic Topology, sections 2.1 and 2.2, homotopy invariance of pairs.
HC no distance; AV milestone no distance. -/
def properCycle_product_support_projection
    (E : Type) [NormedAddCommGroup E] (Y : TopCat.{0}) (S : Set Y) :
    TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' Sᶜ) ⟶
      TopPair.ofSubset (X := Y) Sᶜ :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) (fun _ h => h)

/-- The zero tangential section is a map of the actual support-complement pairs.
Source: Hatcher, Algebraic Topology, sections 2.1 and 2.2, homotopy invariance of pairs.
HC no distance; AV milestone no distance. -/
def properCycle_product_support_section
    (E : Type) [NormedAddCommGroup E] (Y : TopCat.{0}) (S : Set Y) :
    TopPair.ofSubset (X := Y) Sᶜ ⟶
      TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' Sᶜ) :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun y => (0, y), continuous_const.prodMk continuous_id⟩) (fun _ h => h)

/-- Tangential contraction preserves an arbitrary normal support complement throughout the homotopy.
Source: Hatcher, Algebraic Topology, section 2.1, homotopy invariance of pairs;
normalSliceContraction, with the Euclidean normal space replaced by the actual normal space.
HC no distance; AV milestone no distance. -/
def properCycle_product_support_contraction
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (S : Set Y) :
    TopPair.Homotopy
      (properCycle_product_support_projection E Y S ≫ properCycle_product_support_section E Y S)
      (𝟙 (TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' Sᶜ))) where
  fst :=
    { toFun := fun tz : unitInterval × (E × Y) => ((tz.1 : ℝ) • tz.2.1, tz.2.2)
      continuous_toFun := by fun_prop
      map_zero_left := fun z => Prod.ext (zero_smul ℝ z.1) rfl
      map_one_left := fun z => Prod.ext (one_smul ℝ z.1) rfl }
  snd :=
    { toFun := fun tz => ⟨((tz.1 : ℝ) • tz.2.1.1, tz.2.1.2), tz.2.2⟩
      continuous_toFun := by fun_prop
      map_zero_left := fun z => Subtype.ext (Prod.ext (zero_smul ℝ z.1.1) rfl)
      map_one_left := fun z => Subtype.ext (Prod.ext (one_smul ℝ z.1.1) rfl) }
  w := rfl

/-- The actual relative-chain complexes of a product support and its normal support are homotopy equivalent.
Source: Hatcher, Algebraic Topology, section 2.1, relative homotopy invariance.
HC no distance; AV milestone no distance. -/
def properCycle_product_support_chain_equiv
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (S : Set Y) :
    HomotopyEquiv
      ((relativeChainFunctor ℚ).obj
        (TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' Sᶜ)))
      ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := Y) Sᶜ)) where
  hom := (relativeChainFunctor ℚ).map (properCycle_product_support_projection E Y S)
  inv := (relativeChainFunctor ℚ).map (properCycle_product_support_section E Y S)
  homotopyHomInvId :=
    (Homotopy.ofEq ((relativeChainFunctor ℚ).map_comp
      (properCycle_product_support_projection E Y S)
      (properCycle_product_support_section E Y S)).symm).trans
      (((properCycle_product_support_contraction E Y S).relativeChainHomotopy (R := ℚ)).trans
        (Homotopy.ofEq ((relativeChainFunctor ℚ).map_id _)))
  homotopyInvHomId := Homotopy.ofEq (by
    rw [← CategoryTheory.Functor.map_comp]
    change (relativeChainFunctor ℚ).map (𝟙 _) = 𝟙 _
    exact (relativeChainFunctor ℚ).map_id _)

/-- Product-support homology is identified with actual homology of the normal-space support pair.
Source: Hatcher, Algebraic Topology, section 2.1, relative homotopy invariance.
HC no distance; AV milestone no distance. -/
def properCycle_product_support_homology_iso
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (S : Set Y) (n : ℕ) :
    RelativeHomology ℚ
        (TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' Sᶜ)) n ≅
      RelativeHomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) n :=
  (properCycle_product_support_chain_equiv E Y S).toHomologyIso n

/-- The supported cohomology comparison uses universal coefficients and the actual normal projection.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.1, homotopy invariance and universal coefficients.
HC no distance; AV milestone no distance. -/
def properCycle_product_support_cohomology_equiv
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (S : Set Y) (n : ℕ) :
    CohomologyWithSupport ℚ Y S n ≃ₗ[ℚ]
      CohomologyWithSupport ℚ (TopCat.of (E × Y)) (Prod.snd ⁻¹' S) n :=
  (relativeCohomologyEquivDualHomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) n).trans
    ((properCycle_product_support_homology_iso E Y S n).toLinearEquiv.dualMap.trans
      (relativeCohomologyEquivDualHomology ℚ
        (TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' Sᶜ)) n).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The supported comparison is the literal pullback along normal projection.
Source: Hatcher, Algebraic Topology, section 3.1, naturality of universal coefficients.
HC no distance; AV milestone no distance. -/
lemma properCycle_product_support_cohomology_equiv_apply
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (S : Set Y) (n : ℕ) (a : CohomologyWithSupport ℚ Y S n) :
    properCycle_product_support_cohomology_equiv E Y S n a =
      cohomologyWithSupportMap ℚ n
        (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ : TopCat.of (E × Y) ⟶ Y) S a := by
  change properCycle_product_support_cohomology_equiv E Y S n a =
    relativeCohomologyMap ℚ n (properCycle_product_support_projection E Y S) a
  apply (relativeCohomologyEquivDualHomology ℚ
    (TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' Sᶜ)) n).injective
  ext z
  simp only [properCycle_product_support_cohomology_equiv,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap]
  exact LinearMap.congr_fun
    ((relativeCohomologyEquivDualHomology ℚ
      (TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' Sᶜ)) n).apply_symm_apply _) z

/-- Vanishing in the actual normal local homology gives vanishing for the positive-dimensional product support.
Source: Bredon, Sheaf Theory, second edition, V.9, local product support calculations;
Hatcher, Algebraic Topology, section 3.1, universal coefficients over a field.
HC no distance; AV milestone no distance. -/
lemma properCycle_product_point_support_subsingleton
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (y : Y) (n : ℕ)
    (hvan : Subsingleton (orientationGroup Y n y)) :
    Subsingleton (CohomologyWithSupport ℚ (TopCat.of (E × Y))
      (Prod.snd ⁻¹' ({y} : Set Y)) n) := by
  letI : Subsingleton (CohomologyWithSupport ℚ Y {y} n) :=
    relativeCohomology_subsingleton ℚ (TopPair.ofSubset ({y} : Set Y)ᶜ) n hvan
  exact (properCycle_product_support_cohomology_equiv E Y {y} n).symm.injective.subsingleton

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A normal homology line gives a product-support generator normalized on the literal zero section.
Source: Bredon, Sheaf Theory, second edition, V.9, normal product models;
Hatcher, Algebraic Topology, section 3.1, universal coefficients over a field.
HC no distance; AV milestone no distance. -/
lemma properCycle_product_point_normalized_generator
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (y : Y) (n : ℕ) (z : orientationGroup Y n y)
    (hgen : Function.Bijective (LinearMap.toSpanSingleton ℚ (orientationGroup Y n y) z)) :
    ∃ a : CohomologyWithSupport ℚ (TopCat.of (E × Y)) (Prod.snd ⁻¹' ({y} : Set Y)) n,
      relativeCohomologyEquivDualHomology ℚ
        (TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' ({y} : Set Y)ᶜ)) n a
          (relativeHomologyMap ℚ n (properCycle_product_support_section E Y {y}) z) = 1 ∧
      Function.Bijective (LinearMap.toSpanSingleton ℚ
        (CohomologyWithSupport ℚ (TopCat.of (E × Y)) (Prod.snd ⁻¹' ({y} : Set Y)) n) a) := by
  let P := TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' ({y} : Set Y)ᶜ)
  let H := properCycle_product_support_homology_iso E Y {y} n
  let w := relativeHomologyMap ℚ n (properCycle_product_support_section E Y {y}) z
  have hmap : LinearMap.toSpanSingleton ℚ (RelativeHomology ℚ P n) w =
      H.inv.hom.comp (LinearMap.toSpanSingleton ℚ (orientationGroup Y n y) z) := by
    apply LinearMap.ext
    intro q
    change q • w = H.inv.hom (q • z)
    rw [map_smul]
    rfl
  have hw : Function.Bijective (LinearMap.toSpanSingleton ℚ (RelativeHomology ℚ P n) w) := by
    rw [hmap]
    exact ((ConcreteCategory.isIso_iff_bijective H.inv).mp inferInstance).comp hgen
  exact properCycle_relative_normalized_generator P n w hw

end HodgeLean.Foundations.QuotientDuality
