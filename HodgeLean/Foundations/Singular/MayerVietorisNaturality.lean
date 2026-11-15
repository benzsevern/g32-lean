import HodgeLean.Foundations.Singular.MayerVietoris
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Naturality for inverse-image Mayer–Vietoris covers

The small-chain map is supplied by the pushout of the two cover members.
HC no distance; AV milestone no distance. Stage S4 retires no stated hypothesis.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Singular
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A continuous map restricted to the inverse image of a subset.
Source: constructed here from the subspace topology for naturality of Mayer–Vietoris.
-/
def preimageSubsetMap {X Y : TopCat.{0}} (f : X ⟶ Y) (A : Set Y) :
    TopCat.of (f ⁻¹' A) ⟶ TopCat.of A :=
  TopCat.ofHom ⟨fun x => ⟨f x.val, x.2⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

example {X Y : TopCat.{0}} (f : X ⟶ Y) (A : Set Y) (x : f ⁻¹' A) :
    (preimageSubsetMap f A x).val = f x.val := rfl

/-- The restricted map on the overlap of two inverse-image cover members.
Source: constructed here from the subspace topology for naturality of Mayer–Vietoris.
-/
def preimageOverlapMap {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set Y) :
    TopCat.of ↥(f ⁻¹' A ∩ f ⁻¹' B) ⟶ TopCat.of ↥(A ∩ B) :=
  TopCat.ofHom ⟨fun x => ⟨f x.val, x.2⟩,
    (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

example {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set Y) (x : ↥(f ⁻¹' A ∩ f ⁻¹' B)) :
    (preimageOverlapMap f A B x).val = f x.val := rfl

private def chains : TopCat.{0} ⥤ ChainComplex (ModuleCat ℚ) ℕ :=
  TopCat.toSSet ⋙ (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)

private theorem preimage_left_square {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set Y) :
    chains.map (subsetIntersectionToLeft X (f ⁻¹' A) (f ⁻¹' B)) ≫
      chains.map (preimageSubsetMap f A) =
    chains.map (preimageOverlapMap f A B) ≫ chains.map (subsetIntersectionToLeft Y A B) := by
  rw [← chains.map_comp, ← chains.map_comp]
  rfl

private theorem preimage_right_square {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set Y) :
    chains.map (subsetIntersectionToRight X (f ⁻¹' A) (f ⁻¹' B)) ≫
      chains.map (preimageSubsetMap f B) =
    chains.map (preimageOverlapMap f A B) ≫ chains.map (subsetIntersectionToRight Y A B) := by
  rw [← chains.map_comp, ← chains.map_comp]
  rfl

private abbrev smallLeft (X : TopCat.{0}) (A B : Set X) :=
  SSet.chainComplexMap (subsetLeftToSmallSingularSet X A B) (ModuleCat.of ℚ ℚ)
private abbrev smallRight (X : TopCat.{0}) (A B : Set X) :=
  SSet.chainComplexMap (subsetRightToSmallSingularSet X A B) (ModuleCat.of ℚ ℚ)

private def preimageSmallChainMap {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set Y) :
    (singularMayerVietorisShortComplex X (f ⁻¹' A) (f ⁻¹' B)).X₃ ⟶
      (singularMayerVietorisShortComplex Y A B).X₃ :=
  (subsetSmallChainSquare_isPushout X (f ⁻¹' A) (f ⁻¹' B)).desc
    (chains.map (preimageSubsetMap f A) ≫ smallLeft Y A B)
    (chains.map (preimageSubsetMap f B) ≫ smallRight Y A B) (by
      change chains.map (subsetIntersectionToLeft X (f ⁻¹' A) (f ⁻¹' B)) ≫ _ =
        chains.map (subsetIntersectionToRight X (f ⁻¹' A) (f ⁻¹' B)) ≫ _
      rw [← Category.assoc, preimage_left_square, Category.assoc]
      rw [← Category.assoc (chains.map (subsetIntersectionToRight X (f ⁻¹' A) (f ⁻¹' B))),
        preimage_right_square, Category.assoc]
      exact congrArg (fun g => chains.map (preimageOverlapMap f A B) ≫ g)
        (subsetSmallChainSquare_isPushout Y A B).w)

private def preimageMVChainMap {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set Y) :
    singularMayerVietorisShortComplex X (f ⁻¹' A) (f ⁻¹' B) ⟶
      singularMayerVietorisShortComplex Y A B where
  τ₁ := chains.map (preimageOverlapMap f A B)
  τ₂ := biprod.map (chains.map (preimageSubsetMap f A)) (chains.map (preimageSubsetMap f B))
  τ₃ := preimageSmallChainMap f A B
  comm₁₂ := by
    change _ ≫ biprod.lift _ _ = biprod.lift _ _ ≫ _
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst]
      rw [← Category.assoc, biprod.lift_fst]
      exact (preimage_left_square f A B).symm
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
        Preadditive.comp_neg, Preadditive.neg_comp]
      rw [← Category.assoc, biprod.lift_snd, Preadditive.neg_comp]
      exact congrArg Neg.neg (preimage_right_square f A B).symm
  comm₂₃ := by
    change biprod.map _ _ ≫ biprod.desc _ _ = biprod.desc _ _ ≫ _
    apply biprod.hom_ext'
    · simp only [biprod.inl_map_assoc, biprod.inl_desc_assoc, Category.assoc, biprod.inl_desc]
      exact ((subsetSmallChainSquare_isPushout X (f ⁻¹' A) (f ⁻¹' B)).inl_desc _ _ _).symm
    · simp only [biprod.inr_map_assoc, biprod.inr_desc_assoc, Category.assoc, biprod.inr_desc]
      exact ((subsetSmallChainSquare_isPushout X (f ⁻¹' A) (f ⁻¹' B)).inr_desc _ _ _).symm

private def dualShortComplexMap {S T : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ)}
    (f : S ⟶ T) : dualCochainShortComplex T ⟶ dualCochainShortComplex S where
  τ₁ := linearDualMap f.τ₃
  τ₂ := linearDualMap f.τ₂
  τ₃ := linearDualMap f.τ₁
  comm₁₂ := by
    change linearDualMap f.τ₃ ≫ linearDualMap S.g = linearDualMap T.g ≫ linearDualMap f.τ₂
    rw [← linearDualMap_comp, ← linearDualMap_comp, f.comm₂₃]
  comm₂₃ := by
    change linearDualMap f.τ₂ ≫ linearDualMap S.f = linearDualMap T.f ≫ linearDualMap f.τ₁
    rw [← linearDualMap_comp, ← linearDualMap_comp, f.comm₁₂]

private theorem smallLeft_inclusion (X : TopCat.{0}) (A B : Set X) :
    smallLeft X A B ≫ twoSubsetSmallChainInclusion X A B =
      chains.map (topologicalSubsetInclusion X A) := by
  change ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map _ ≫
    ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map _ = _
  rw [← Functor.map_comp]
  rfl

private theorem smallRight_inclusion (X : TopCat.{0}) (A B : Set X) :
    smallRight X A B ≫ twoSubsetSmallChainInclusion X A B =
      chains.map (topologicalSubsetInclusion X B) := by
  change ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map _ ≫
    ((SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).map _ = _
  rw [← Functor.map_comp]
  rfl

private theorem preimageSmallChainMap_inclusion {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set Y) :
    preimageSmallChainMap f A B ≫ twoSubsetSmallChainInclusion Y A B =
      twoSubsetSmallChainInclusion X (f ⁻¹' A) (f ⁻¹' B) ≫ chains.map f := by
  apply (subsetSmallChainSquare_isPushout X (f ⁻¹' A) (f ⁻¹' B)).hom_ext
  · rw [← Category.assoc, show smallLeft X (f ⁻¹' A) (f ⁻¹' B) ≫ preimageSmallChainMap f A B =
        chains.map (preimageSubsetMap f A) ≫ smallLeft Y A B from
        (subsetSmallChainSquare_isPushout X (f ⁻¹' A) (f ⁻¹' B)).inl_desc _ _ _,
      Category.assoc, smallLeft_inclusion, ← Category.assoc, smallLeft_inclusion,
      ← chains.map_comp, ← chains.map_comp]
    rfl
  · rw [← Category.assoc, show smallRight X (f ⁻¹' A) (f ⁻¹' B) ≫ preimageSmallChainMap f A B =
        chains.map (preimageSubsetMap f B) ≫ smallRight Y A B from
        (subsetSmallChainSquare_isPushout X (f ⁻¹' A) (f ⁻¹' B)).inr_desc _ _ _,
      Category.assoc, smallRight_inclusion, ← Category.assoc, smallRight_inclusion,
      ← chains.map_comp, ← chains.map_comp]
    rfl

/-- The Mayer–Vietoris connecting map is natural for an inverse-image open cover.
This is degree-preserving naturality; degree-shifting cup operations instead use
the explicit lift comparison in `ConnectingMap.lean`.
Source: Hatcher, *Algebraic Topology*, §3.1, naturality of the cohomology exact sequence.
HC no distance; AV milestone no distance.
-/
theorem mvδ_preimage {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set Y)
    (hA : IsOpen A) (hB : IsOpen B) (hc : A ∪ B = Set.univ)
    (hX : f ⁻¹' A ∪ f ⁻¹' B = Set.univ) (n : ℕ)
    (α : Cohomology ℚ (TopCat.of ↥(A ∩ B)) n) :
    cohomologyMap ℚ (n + 1) f (mvδ Y A B hA hB hc n α) =
      mvδ X (f ⁻¹' A) (f ⁻¹' B) (hA.preimage f.hom.continuous)
        (hB.preimage f.hom.continuous) hX n
        (cohomologyMap ℚ n (preimageOverlapMap f A B) α) := by
  let eX (k : ℕ) := (smallCochainCohomologyEquiv X (f ⁻¹' A) (f ⁻¹' B)
    (hA.preimage f.hom.continuous) (hB.preimage f.hom.continuous) hX k).toModuleIso
  let eY (k : ℕ) := (smallCochainCohomologyEquiv Y A B hA hB hc k).toModuleIso
  let φ := dualShortComplexMap (preimageMVChainMap f A B)
  have hi (k : ℕ) : ModuleCat.ofHom (cohomologyMap ℚ k f) ≫ (eX k).inv =
      (eY k).inv ≫ homologyMap φ.τ₁ k := by
    change homologyMap (linearDualMap (chains.map f)) k ≫
      homologyMap (linearDualMap (twoSubsetSmallChainInclusion X (f ⁻¹' A) (f ⁻¹' B))) k =
      homologyMap (linearDualMap (twoSubsetSmallChainInclusion Y A B)) k ≫
        homologyMap (linearDualMap (preimageSmallChainMap f A B)) k
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← linearDualMap_comp, ← linearDualMap_comp, preimageSmallChainMap_inclusion]
  have ht (k : ℕ) : homologyMap φ.τ₁ k ≫ (eX k).hom =
      (eY k).hom ≫ ModuleCat.ofHom (cohomologyMap ℚ k f) := by
    apply (cancel_epi (eY k).inv).mp
    rw [← Category.assoc, ← hi, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hd := HomologySequence.δ_naturality φ (mvCochainShortComplex_shortExact Y A B)
    (mvCochainShortComplex_shortExact X (f ⁻¹' A) (f ⁻¹' B)) n (n + 1) (by simp)
  have h := congrArg (fun t => t ≫ (eX (n + 1)).hom) hd
  simp only [Category.assoc] at h
  rw [ht] at h
  exact ConcreteCategory.congr_hom h α

#print axioms preimageSubsetMap
#print axioms preimageOverlapMap
#print axioms mvδ_preimage
end HodgeLean.Foundations.Singular
