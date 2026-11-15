import HodgeLean.Foundations.Program.SchoenTransferC1a5CollarExcisionHelpers
import Mathlib.Topology.Category.TopCat.Limits.Products

/-! Collar deformation data on arbitrary small topological disjoint unions.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- The actual continuous map on topological disjoint unions, preserving the summand index.
Source: Mathlib continuous_sigma_map. -/
def c1a5_sigma_map {I : Type} {A B : I → TopCat.{0}} (f : ∀ i, A i ⟶ B i) :
    TopCat.of (Σ i, A i) ⟶ TopCat.of (Σ i, B i) :=
  TopCat.ofHom ⟨Sigma.map id (fun i ↦ f i),
    Continuous.sigma_map (fun i ↦ (f i).hom.continuous)⟩

example {I : Type} (A : I → TopCat.{0}) := c1a5_sigma_map (fun i ↦ 𝟙 (A i))

/-- Summand retractions give a retraction of the actual disjoint unions.
Source: the index-preserving disjoint-union map formula. -/
lemma c1a5_sigma_retract {I : Type} {A U : I → TopCat.{0}}
    (j : ∀ i, A i ⟶ U i) (q : ∀ i, U i ⟶ A i) (hq : ∀ i, j i ≫ q i = 𝟙 (A i)) :
    c1a5_sigma_map j ≫ c1a5_sigma_map q = 𝟙 (TopCat.of (Σ i, A i)) := by
  apply ConcreteCategory.hom_ext
  rintro ⟨i, x⟩
  exact congrArg (fun z : A i ↦ (⟨i, z⟩ : Σ i, A i)) (ConcreteCategory.congr_hom (hq i) x)

/-- Summand boundary deformations give a continuous deformation on their actual disjoint union.
Source: Mathlib Homeomorph.sigmaProdDistrib; Hatcher §2.1, disjoint unions of cell collars. -/
def c1a5_sigma_collar_homotopy {I : Type} {A U : I → TopCat.{0}}
    (j : ∀ i, A i ⟶ U i) (q : ∀ i, U i ⟶ A i)
    (H : ∀ i, TopCat.Homotopy (𝟙 (U i)) (q i ≫ j i)) :
    TopCat.Homotopy (𝟙 (TopCat.of (Σ i, U i))) (c1a5_sigma_map q ≫ c1a5_sigma_map j) where
  toFun z := ⟨z.2.1, H z.2.1 (z.1, z.2.2)⟩
  continuous_toFun := by
    have hh : Continuous (fun z : Σ i, U i × unitInterval ↦
        (⟨z.1, H z.1 (z.2.2, z.2.1)⟩ : Σ i, U i)) :=
      continuous_sigma (fun i ↦ continuous_sigmaMk.comp ((H i).continuous.comp continuous_swap))
    exact hh.comp (Homeomorph.sigmaProdDistrib.continuous.comp continuous_swap)
  map_zero_left x := by
    rcases x with ⟨i, x⟩
    exact congrArg (Sigma.mk i) ((H i).map_zero_left x)
  map_one_left x := by
    rcases x with ⟨i, x⟩
    exact congrArg (Sigma.mk i) ((H i).map_one_left x)

example := @c1a5_sigma_collar_homotopy

/-- The disjoint-union deformation fixes every point of the disjoint-union boundary.
Source: the summandwise fixed boundary deformation formula. -/
lemma c1a5_sigma_collar_homotopy_fixed {I : Type} {A U : I → TopCat.{0}}
    (j : ∀ i, A i ⟶ U i) (q : ∀ i, U i ⟶ A i)
    (H : ∀ i, TopCat.Homotopy (𝟙 (U i)) (q i ≫ j i))
    (hfixed : ∀ i (s : unitInterval) (a : A i), H i (s, j i a) = j i a)
    (s : unitInterval) (a : TopCat.of (Σ i, A i)) :
    c1a5_sigma_collar_homotopy j q H (s, c1a5_sigma_map j a) = c1a5_sigma_map j a := by
  rcases a with ⟨i, a⟩
  exact congrArg (Sigma.mk i) (hfixed i s a)

/-- Disjoint unions of open collar embeddings are open embeddings.
Source: Mathlib Topology.isOpenEmbedding_sigmaMap. -/
lemma c1a5_sigma_map_isOpenEmbedding {I : Type} {U C : I → TopCat.{0}}
    (k : ∀ i, U i ⟶ C i) (hk : ∀ i, Topology.IsOpenEmbedding (k i)) :
    Topology.IsOpenEmbedding (c1a5_sigma_map k) := by
  change Topology.IsOpenEmbedding
    (@Sigma.map I I (fun i ↦ U i) (fun i ↦ C i) id (fun i x ↦ k i x))
  exact (Topology.isOpenEmbedding_sigmaMap Function.injective_id).2 hk

/-- The disjoint-union map pulls each summand back to the range of that summand map.
Source: the index-preserving disjoint-union map formula and equality of sigma components. -/
lemma c1a5_sigma_map_range_preimage {I : Type} {A B : I → TopCat.{0}}
    (f : ∀ i, A i ⟶ B i) (i : I) :
    Sigma.mk i ⁻¹' Set.range (c1a5_sigma_map f) = Set.range (f i) := by
  ext x
  constructor
  · rintro ⟨⟨j, y⟩, h⟩
    have hi : j = i := congrArg Sigma.fst h
    subst j
    exact ⟨y, eq_of_heq (Sigma.mk.inj h).2⟩
  · rintro ⟨y, rfl⟩
    exact ⟨⟨i, y⟩, rfl⟩

/-- Disjoint unions of maps with closed image have closed image.
Source: Mathlib isClosed_sigma_iff and the actual summand range preimage. -/
lemma c1a5_sigma_map_range_isClosed {I : Type} {A B : I → TopCat.{0}}
    (f : ∀ i, A i ⟶ B i) (hf : ∀ i, IsClosed (Set.range (f i))) :
    IsClosed (Set.range (c1a5_sigma_map f)) := by
  apply isClosed_sigma_iff.mpr
  intro i
  rw [c1a5_sigma_map_range_preimage]
  exact hf i

/-- Disjoint unions of injective maps remain injective.
Source: equality of the index and value components of the actual disjoint-union map. -/
lemma c1a5_sigma_map_injective {I : Type} {A B : I → TopCat.{0}}
    (f : ∀ i, A i ⟶ B i) (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (c1a5_sigma_map f) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  have hi : i = j := congrArg Sigma.fst h
  subst j
  exact congrArg (Sigma.mk i) (hf i (eq_of_heq (Sigma.mk.inj h).2))

/-- The actual disjoint-union maps preserve composition.
Source: the index-preserving disjoint-union map formula. -/
lemma c1a5_sigma_map_comp {I : Type} {A B C : I → TopCat.{0}}
    (f : ∀ i, A i ⟶ B i) (g : ∀ i, B i ⟶ C i) :
    c1a5_sigma_map f ≫ c1a5_sigma_map g = c1a5_sigma_map (fun i ↦ f i ≫ g i) := by
  rfl

end HodgeLean.Foundations.Program
