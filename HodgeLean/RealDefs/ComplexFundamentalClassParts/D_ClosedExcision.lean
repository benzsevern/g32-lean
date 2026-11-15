/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativePairExcision

/-! Ported, with modifications, from upstream's
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/RelativePairExcision.lean` at `2ead713`
(the upstream licence and notice are in `LICENSE` and `NOTICE` beside this file). Changes: the
point `x` is replaced by a closed set `A ⊆ U` (cover `{U, Aᶜ}` instead of `{U, {x}ᶜ}`), the
`T1Space` assumption is dropped, the declarations are renamed (`point` to `closed`,
`neighborhood` to `closedNbhd`), the pair map is `TopPair.ofSubsetHom`, the `module` header and
public/expose markers are removed, and the file is placed in this repository's namespace.

# Excision of a closed set

If `U` is open, `A` is closed and `A ⊆ U`, inclusion induces an isomorphism
`Hₙ(U, U ∖ A; ℚ) ≅ Hₙ(X, X ∖ A; ℚ)` (Hatcher, Theorem 2.20).
-/

noncomputable section

open CategoryTheory AlgebraicTopology.Singular

namespace HodgeLean.RealDefs.ClosedExcision

/-- The pair `(X, X ∖ A)`.
Source: Hatcher, Algebraic Topology, §2.1 (relative homology of a pair). -/
abbrev closedComplementPair {X : Type} [TopologicalSpace X] (A : Set X) : TopPair :=
  TopPair.ofSubset (X := TopCat.of X) Aᶜ

example : closedComplementPair (∅ : Set ℝ) = TopPair.ofSubset (X := TopCat.of ℝ) Set.univ := by
  simp [closedComplementPair]


variable {X : Type} [TopologicalSpace X]

section Port

open CategoryTheory.Limits Simplicial Set
open scoped Simplicial

/-- The pair `(U, U ∖ A)` for a subset `U` containing `A`. -/
private abbrev closedNbhdClosedComplementPair (U : Set X) (A : Set X) : TopPair :=
  TopPair.ofSubset (X := TopCat.of U) {u | u.1 ∉ A}

/-- The inclusion from a closedNbhd point-complement pair into the ambient point-complement
pair. -/
private def closedNbhdClosedComplementPairMap (U : Set X) (A : Set X) :
    closedNbhdClosedComplementPair U A ⟶ closedComplementPair A :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of U ⟶ TopCat.of X)
    (fun _ ha => ha)

/-- The two-set cover used in point excision: the closedNbhd and the complement of the
point. -/
private def closedExcisionCover (U : Set X) (A : Set X) : Bool → Set (TopCat.of X) :=
  fun b ↦ if b then U else Aᶜ

lemma closedExcisionCover_isOpen (U : Set X) (A : Set X) (hU : IsOpen U) (hA : IsClosed A) :
    ∀ b, IsOpen (closedExcisionCover U A b) := by
  intro b
  cases b with
  | false => exact hA.isOpen_compl
  | true => exact hU

lemma closedExcisionCover_iUnion (U : Set X) (A : Set X) (hAU : A ⊆ U) :
    ⋃ b, closedExcisionCover U A b = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  by_cases hy : y ∈ A
  · exact Set.mem_iUnion.2 ⟨true, by simpa [closedExcisionCover] using hAU hy⟩
  · exact Set.mem_iUnion.2 ⟨false, by simpa [closedExcisionCover]⟩

/-- Rational chains on the small singular subcomplex for the point-excision cover. -/
private abbrev ClosedExcisionSmallChainComplex (U : Set X) (A : Set X) :
    ChainComplex (ModuleCat ℚ) ℕ :=
  CoverSmallRationalSingularChainComplex (TopCat.of X) (closedExcisionCover U A)

/-- The inclusion of the point complement into the ambient space, with its codomain fixed
explicitly to avoid transports between definitionally equal presentations of the subspace. -/
private def closedComplementAmbientInclusion (A : Set X) :
    (closedComplementPair A).snd ⟶ TopCat.of X :=
  TopCat.ofHom ⟨fun y ↦ y.1, continuous_subtype_val⟩

/-- The identity-on-points map from the point complement to the `false` member of the
point-excision cover. -/
private def closedComplementToFalseCoverMember (U : Set X) (A : Set X) :
    (closedComplementPair A).snd ⟶ TopCat.of (closedExcisionCover U A false) :=
  TopCat.ofHom ⟨Set.codRestrict (closedComplementAmbientInclusion A)
      (closedExcisionCover U A false) (fun y ↦ by change y.1 ∈ Aᶜ; exact y.2),
    (closedComplementAmbientInclusion A).hom.continuous.codRestrict _⟩

/-- The chain map from the point complement into the small chains. -/
private def closedComplementToExcisionSmallSingularSet (U : Set X) (A : Set X) :
    TopCat.toSSet.obj (closedComplementPair A).snd ⟶
      coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A) :=
  SSet.Subcomplex.lift
    (TopCat.toSSet.map (closedComplementAmbientInclusion A)) (by
      intro n z hz
      rw [mem_coverSmallSingularSubcomplex_iff]
      refine ⟨false, ?_⟩
      change z ∈ Set.range ((TopCat.toSSet.map
        (topologicalSubsetInclusion (TopCat.of X) (closedExcisionCover U A false))).app n)
      obtain ⟨a, rfl⟩ := hz
      refine ⟨(TopCat.toSSet.map (closedComplementToFalseCoverMember U A)).app n a, ?_⟩
      apply ((TopCat.of X).toSSetObjEquiv n).injective
      ext t
      rfl)

@[reassoc (attr := simp)]
lemma closedComplementToExcisionSmallSingularSet_comp_inclusion
    (U : Set X) (A : Set X) :
    closedComplementToExcisionSmallSingularSet U A ≫
        (coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A)).ι =
      TopCat.toSSet.map (closedComplementAmbientInclusion A) := rfl

private def closedComplementToExcisionSmallChains (U : Set X) (A : Set X) :
    (TopCat.toSSet.obj (closedComplementPair A).snd).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      ClosedExcisionSmallChainComplex U A :=
  SSet.chainComplexMap
    (closedComplementToExcisionSmallSingularSet U A)
    (ModuleCat.of ℚ ℚ)

/-- The arrow whose cokernel is the small relative chain complex for point excision. -/
private def closedExcisionSmallChainArrow (U : Set X) (A : Set X) :
    Arrow (ChainCategory ℚ) :=
  Arrow.mk (closedComplementToExcisionSmallChains U A)

/-- The relative quotient of point-excision-small chains by chains avoiding the point. -/
private abbrev ClosedExcisionSmallRelativeChainComplex (U : Set X) (A : Set X) :
    ChainCategory ℚ :=
  (Limits.coker (C := ChainCategory ℚ)).obj (closedExcisionSmallChainArrow U A)

/-- A small simplex lies away from `A` when it comes from the point-complement member of the
cover. -/
private def ClosedExcisionSmallSimplex.AvoidsSet (U : Set X) (A : Set X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A) : SSet)
      _⦋n⦌) : Prop :=
  ∃ a : (TopCat.toSSet.obj (closedComplementPair A).snd) _⦋n⦌,
    (TopCat.toSSet.map (closedComplementAmbientInclusion A)).app _ a =
      σ.1

instance (U : Set X) (A : Set X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A) : SSet)
      _⦋n⦌) : Decidable (ClosedExcisionSmallSimplex.AvoidsSet U A σ) :=
  Classical.propDecidable _

lemma ClosedExcisionSmallSimplex.avoidsSet_face (U : Set X) (A : Set X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A) : SSet)
      _⦋n + 1⦌)
    (hσ : ClosedExcisionSmallSimplex.AvoidsSet U A σ) (i : Fin (n + 2)) :
    ClosedExcisionSmallSimplex.AvoidsSet U A
      ((coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A) : SSet).δ i σ) := by
  obtain ⟨a, ha⟩ := hσ
  exact ⟨(TopCat.toSSet.obj (closedComplementPair A).snd).δ i a,
    congrArg (fun z ↦ (TopCat.toSSet.obj (TopCat.of X)).δ i z) ha⟩

/-- A small simplex which does not avoid `A` comes from the closedNbhd member of the cover. -/
lemma ClosedExcisionSmallSimplex.exists_closedNbhdPreimage (U : Set X) (A : Set X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A) : SSet)
      _⦋n⦌)
    (hσ : ¬ ClosedExcisionSmallSimplex.AvoidsSet U A σ) :
    ∃ y : (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌,
      (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U)).app _ y = σ.1 := by
  obtain ⟨b, y, hy⟩ :=
    (mem_coverSmallSingularSubcomplex_iff_exists_preimage
      (TopCat.of X) (closedExcisionCover U A) σ.1).mp σ.2
  cases b with
  | false =>
      dsimp [closedExcisionCover] at y hy
      exact False.elim (hσ ⟨y, hy⟩)
  | true =>
      dsimp [closedExcisionCover] at y hy
      exact ⟨y, hy⟩

/-- The chosen closedNbhd lift of a small simplex which does not avoid `A`. -/
private def ClosedExcisionSmallSimplex.closedNbhdPreimage (U : Set X) (A : Set X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A) : SSet)
      _⦋n⦌)
    (hσ : ¬ ClosedExcisionSmallSimplex.AvoidsSet U A σ) :
    (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌ :=
  Classical.choose (ClosedExcisionSmallSimplex.exists_closedNbhdPreimage U A σ hσ)

lemma ClosedExcisionSmallSimplex.closedNbhdPreimage_map (U : Set X) (A : Set X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A) : SSet)
      _⦋n⦌)
    (hσ : ¬ ClosedExcisionSmallSimplex.AvoidsSet U A σ) :
    (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U)).app _
        (ClosedExcisionSmallSimplex.closedNbhdPreimage U A σ hσ) = σ.1 :=
  Classical.choose_spec (ClosedExcisionSmallSimplex.exists_closedNbhdPreimage U A σ hσ)

/-- A singular simplex of `U` which avoids `A` lifts to the subspace `U ∖ A`. -/
private def closedNbhdClosedComplementSimplexOfAvoids (U : Set X) (A : Set X) {n : ℕ}
    (u : (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌)
    (hu : ∀ t, (((TopCat.of U).toSSetObjEquiv _ u) t).1 ∉ A) :
    (TopCat.toSSet.obj (closedNbhdClosedComplementPair U A).snd) _⦋n⦌ :=
  ((closedNbhdClosedComplementPair U A).snd.toSSetObjEquiv _).symm
    ⟨fun t ↦ ⟨((TopCat.of U).toSSetObjEquiv _ u) t, hu t⟩,
      ((TopCat.of U).toSSetObjEquiv _ u).continuous.subtype_mk _⟩

lemma closedNbhdClosedComplementSimplexOfAvoids_map (U : Set X) (A : Set X) {n : ℕ}
    (u : (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌)
    (hu : ∀ t, (((TopCat.of U).toSSetObjEquiv _ u) t).1 ∉ A) :
    (TopCat.toSSet.map (closedNbhdClosedComplementPair U A).map).app _
        (closedNbhdClosedComplementSimplexOfAvoids U A u hu) = u := rfl

/-- Equality with a simplex in `X ∖ A` shows that a simplex of `U` avoids `A`. -/
lemma closedNbhdSimplex_avoids_of_ambient_eq (U : Set X) (A : Set X) {n : ℕ}
    (u : (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌)
    (a : (TopCat.toSSet.obj (closedComplementPair A).snd) _⦋n⦌)
    (h : (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U)).app _ u =
      (TopCat.toSSet.map (closedComplementAmbientInclusion A)).app _ a) :
    ∀ t, (((TopCat.of U).toSSetObjEquiv _ u) t).1 ∉ A := by
  intro t hut
  have ht := congrArg (fun z ↦ ((TopCat.of X).toSSetObjEquiv _ z) t) h
  change (((TopCat.of U).toSSetObjEquiv _ u) t).1 =
    (((closedComplementPair A).snd.toSSetObjEquiv _ a) t).1 at ht
  exact (((closedComplementPair A).snd.toSSetObjEquiv _ a) t).2
    (ht ▸ hut)

lemma closedNbhdInclusion_singular_injective (U : Set X) {n : ℕ} :
    Function.Injective
      ((TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U)).app
        (Opposite.op (SimplexCategory.mk n))) := by
  intro a b h
  apply ((TopCat.of U).toSSetObjEquiv _).injective
  ext t
  exact congrArg (fun z ↦ ((TopCat.of X).toSSetObjEquiv _ z) t) h

/-- A closedNbhd simplex which is also represented in the point complement vanishes after
projection to the closedNbhd relative chain complex. -/
private abbrev closedNbhdSubspaceChainMap (U : Set X) (A : Set X) :
    (TopCat.toSSet.obj (closedNbhdClosedComplementPair U A).snd).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      (TopCat.toSSet.obj (TopCat.of U)).chainComplex (ModuleCat.of ℚ ℚ) :=
  SSet.chainComplexMap (TopCat.toSSet.map (closedNbhdClosedComplementPair U A).map)
    (ModuleCat.of ℚ ℚ)

/-- The relative-chain projection for the closedNbhd pair, with the absolute closedNbhd
chain complex exposed as its source. -/
private abbrev closedNbhdRelativeProjection (U : Set X) (A : Set X) :
    (TopCat.toSSet.obj (TopCat.of U)).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      (relativeChainFunctor ℚ).obj (closedNbhdClosedComplementPair U A) :=
  relativeChainProjection ℚ (closedNbhdClosedComplementPair U A)

private def closedNbhdRelativeProjectionComponent (U : Set X) (A : Set X) (n : ℕ) :
    ((TopCat.toSSet.obj (TopCat.of U)).chainComplex (ModuleCat.of ℚ ℚ)).X n ⟶
      (relativeChainFunctor ℚ).obj (closedNbhdClosedComplementPair U A) |>.X n :=
  (closedNbhdRelativeProjection U A).f n

lemma closedNbhdRelativeProjectionComponent_comm (U : Set X) (A : Set X) (n : ℕ) :
    closedNbhdRelativeProjectionComponent U A (n + 1) ≫
        ((relativeChainFunctor ℚ).obj
          (closedNbhdClosedComplementPair U A)).d (n + 1) n =
      ((TopCat.toSSet.obj (TopCat.of U)).chainComplex
        (ModuleCat.of ℚ ℚ)).d (n + 1) n ≫
        closedNbhdRelativeProjectionComponent U A n :=
  (relativeChainProjection ℚ (closedNbhdClosedComplementPair U A)).comm (n + 1) n

lemma closedNbhdSubspaceChainMap_comp_relativeProjection (U : Set X) (A : Set X) :
    closedNbhdSubspaceChainMap U A ≫
      closedNbhdRelativeProjection U A = 0 :=
  subspaceChainMap_relativeChainProjection ℚ (closedNbhdClosedComplementPair U A)

lemma closedNbhdSimplex_projection_zero_of_ambient_eq
    (U : Set X) (A : Set X) {n : ℕ}
    (u : (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌)
    (a : (TopCat.toSSet.obj (closedComplementPair A).snd) _⦋n⦌)
    (h : (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U)).app _ u =
      (TopCat.toSSet.map (closedComplementAmbientInclusion A)).app _ a) :
    (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex u ≫
        closedNbhdRelativeProjectionComponent U A n = 0 := by
  let hu := closedNbhdSimplex_avoids_of_ambient_eq U A u a h
  let v := closedNbhdClosedComplementSimplexOfAvoids U A u hu
  have hv := closedNbhdClosedComplementSimplexOfAvoids_map U A u hu
  have hvchain :
      (TopCat.toSSet.obj (closedNbhdClosedComplementPair U A).snd).ιChainComplex v ≫
          (closedNbhdSubspaceChainMap U A).f n =
        (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex u := by
    change (TopCat.toSSet.obj (closedNbhdClosedComplementPair U A).snd).ιChainComplex v ≫
      (SSet.chainComplexMap
        (TopCat.toSSet.map (closedNbhdClosedComplementPair U A).map)
        (ModuleCat.of ℚ ℚ)).f n = _
    rw [SSet.ι_chainComplexMap_f, hv]
    rfl
  have hc := congrArg (fun f ↦ f.f n)
    (closedNbhdSubspaceChainMap_comp_relativeProjection U A)
  change (closedNbhdSubspaceChainMap U A).f n ≫
    closedNbhdRelativeProjectionComponent U A n = 0 at hc
  calc
    (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex u ≫
        closedNbhdRelativeProjectionComponent U A n =
      ((TopCat.toSSet.obj (closedNbhdClosedComplementPair U A).snd).ιChainComplex v ≫
        (closedNbhdSubspaceChainMap U A).f n) ≫
          closedNbhdRelativeProjectionComponent U A n := by
            rw [hvchain]
    _ = (TopCat.toSSet.obj (closedNbhdClosedComplementPair U A).snd).ιChainComplex v ≫
        ((closedNbhdSubspaceChainMap U A).f n ≫
          closedNbhdRelativeProjectionComponent U A n) := Category.assoc _ _ _
    _ = 0 := by rw [hc, comp_zero]

/-- On a basis simplex, send a point-avoiding simplex to zero and otherwise lift it to the
closedNbhd before projecting to relative chains. -/
private def closedExcisionSmallToClosedNbhdRelativeComponent (U : Set X) (A : Set X) (n : ℕ) :
    (ClosedExcisionSmallChainComplex U A).X n ⟶
      ((relativeChainFunctor ℚ).obj (closedNbhdClosedComplementPair U A)).X n :=
  ((coverSmallSingularSubcomplex (TopCat.of X)
    (closedExcisionCover U A) : SSet).isColimitChainComplexXCofan
      (ModuleCat.of ℚ ℚ) n).desc
      (Cofan.mk _ fun σ ↦
        if hσ : ClosedExcisionSmallSimplex.AvoidsSet U A σ then 0 else
          (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex
              (ClosedExcisionSmallSimplex.closedNbhdPreimage U A σ hσ) ≫
            closedNbhdRelativeProjectionComponent U A n)

@[reassoc]
lemma iota_closedExcisionSmallToClosedNbhdRelativeComponent
    (U : Set X) (A : Set X) (n : ℕ)
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A) : SSet)
      _⦋n⦌) :
    (coverSmallSingularSubcomplex (TopCat.of X)
      (closedExcisionCover U A) : SSet).ιChainComplex σ ≫
        closedExcisionSmallToClosedNbhdRelativeComponent U A n =
      if hσ : ClosedExcisionSmallSimplex.AvoidsSet U A σ then 0 else
        (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex
            (ClosedExcisionSmallSimplex.closedNbhdPreimage U A σ hσ) ≫
          closedNbhdRelativeProjectionComponent U A n :=
  ((coverSmallSingularSubcomplex (TopCat.of X)
    (closedExcisionCover U A) : SSet).isColimitChainComplexXCofan
      (ModuleCat.of ℚ ℚ) n).fac _ (Discrete.mk σ)

lemma closedExcisionSmallToClosedNbhdRelativeComponent_comm
    (U : Set X) (A : Set X) (n : ℕ) :
    closedExcisionSmallToClosedNbhdRelativeComponent U A (n + 1) ≫
        ((relativeChainFunctor ℚ).obj
          (closedNbhdClosedComplementPair U A)).d (n + 1) n =
      (ClosedExcisionSmallChainComplex U A).d (n + 1) n ≫
        closedExcisionSmallToClosedNbhdRelativeComponent U A n := by
  apply SSet.chainComplex_hom_ext
  intro σ
  by_cases hσ : ClosedExcisionSmallSimplex.AvoidsSet U A σ
  · rw [← Category.assoc,
      iota_closedExcisionSmallToClosedNbhdRelativeComponent U A (n + 1) σ,
      dif_pos hσ, zero_comp, ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [Preadditive.zsmul_comp,
      iota_closedExcisionSmallToClosedNbhdRelativeComponent U A n,
      dif_pos (ClosedExcisionSmallSimplex.avoidsSet_face U A σ hσ i)]
    simp
  · rw [← Category.assoc,
      iota_closedExcisionSmallToClosedNbhdRelativeComponent U A (n + 1) σ,
      dif_neg hσ, Category.assoc, closedNbhdRelativeProjectionComponent_comm U A n,
      ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp,
      ← Category.assoc, SSet.ιChainComplex_d, Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [Preadditive.zsmul_comp, Preadditive.zsmul_comp]
    congr 1
    by_cases hi : ClosedExcisionSmallSimplex.AvoidsSet U A
        ((coverSmallSingularSubcomplex (TopCat.of X)
          (closedExcisionCover U A) : SSet).δ i σ)
    · rw [iota_closedExcisionSmallToClosedNbhdRelativeComponent U A n, dif_pos hi]
      obtain ⟨a, ha⟩ := hi
      apply closedNbhdSimplex_projection_zero_of_ambient_eq U A _ a
      have hp := ClosedExcisionSmallSimplex.closedNbhdPreimage_map U A σ hσ
      exact (congrArg (fun z ↦ (TopCat.toSSet.obj (TopCat.of X)).δ i z) hp).trans ha.symm
    · rw [iota_closedExcisionSmallToClosedNbhdRelativeComponent U A n, dif_neg hi]
      congr 1
      apply congrArg (fun z ↦ (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex z)
      apply closedNbhdInclusion_singular_injective U
      have hp := ClosedExcisionSmallSimplex.closedNbhdPreimage_map U A σ hσ
      exact (congrArg (fun z ↦ (TopCat.toSSet.obj (TopCat.of X)).δ i z) hp).trans
        (ClosedExcisionSmallSimplex.closedNbhdPreimage_map U A _ hi).symm

/-- The chain map from small relative chains to closedNbhd relative chains obtained by
discarding simplices which avoid the distinguished point. -/
private def closedExcisionSmallToClosedNbhdRelativeChainMap (U : Set X) (A : Set X) :
    ClosedExcisionSmallChainComplex U A ⟶
      (relativeChainFunctor ℚ).obj (closedNbhdClosedComplementPair U A) where
  f n := closedExcisionSmallToClosedNbhdRelativeComponent U A n
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    subst i
    exact closedExcisionSmallToClosedNbhdRelativeComponent_comm U A j

/-- A simplex entering the small complex through the point-complement cover member is recognized
as point-avoiding. -/
lemma closedComplementCoverMember_avoidsSet (U : Set X) (A : Set X) {n : ℕ}
    (a : (TopCat.toSSet.obj (closedComplementPair A).snd) _⦋n⦌) :
    ClosedExcisionSmallSimplex.AvoidsSet U A
      ((closedComplementToExcisionSmallSingularSet U A).app _ a) := by
  refine ⟨a, ?_⟩
  have h := congr_app
    (closedComplementToExcisionSmallSingularSet_comp_inclusion U A)
    (Opposite.op (SimplexCategory.mk n))
  exact (ConcreteCategory.congr_hom h a).symm

/-- The small-to-closedNbhd chain map kills all chains from the point complement. -/
lemma closedComplementToExcisionSmallChains_comp_smallToClosedNbhd
    (U : Set X) (A : Set X) :
    closedComplementToExcisionSmallChains U A ≫
      closedExcisionSmallToClosedNbhdRelativeChainMap U A = 0 := by
  apply HomologicalComplex.hom_ext
  intro n
  change (SSet.chainComplexMap (closedComplementToExcisionSmallSingularSet U A)
      (ModuleCat.of ℚ ℚ)).f n ≫
        closedExcisionSmallToClosedNbhdRelativeComponent U A n = 0
  apply SSet.chainComplex_hom_ext
  intro a
  rw [← Category.assoc, SSet.ι_chainComplexMap_f,
    iota_closedExcisionSmallToClosedNbhdRelativeComponent,
    dif_pos (closedComplementCoverMember_avoidsSet U A a)]
  rfl

/-- Projection from small chains to the small relative quotient. -/
private abbrev closedExcisionSmallRelativeProjection (U : Set X) (A : Set X) :
    ClosedExcisionSmallChainComplex U A ⟶
      ClosedExcisionSmallRelativeChainComplex U A :=
  cokernel.π (closedComplementToExcisionSmallChains U A)

/-- The chain map from the small relative quotient back to closedNbhd relative chains. -/
private def closedExcisionSmallRelativeToClosedNbhdRelativeChainMap (U : Set X) (A : Set X) :
    ClosedExcisionSmallRelativeChainComplex U A ⟶
      (relativeChainFunctor ℚ).obj (closedNbhdClosedComplementPair U A) :=
  cokernel.desc (closedComplementToExcisionSmallChains U A)
    (closedExcisionSmallToClosedNbhdRelativeChainMap U A)
    (closedComplementToExcisionSmallChains_comp_smallToClosedNbhd U A)

@[reassoc (attr := simp)]
lemma closedExcisionSmallRelativeProjection_comp_toClosedNbhd
    (U : Set X) (A : Set X) :
    closedExcisionSmallRelativeProjection U A ≫
        closedExcisionSmallRelativeToClosedNbhdRelativeChainMap U A =
      closedExcisionSmallToClosedNbhdRelativeChainMap U A :=
  cokernel.π_desc _ _ _

/-- The inclusion from `U ∖ A` to `X ∖ A`. -/
private def closedNbhdClosedComplementToClosedComplement (U : Set X) (A : Set X) :
    (closedNbhdClosedComplementPair U A).snd ⟶ (closedComplementPair A).snd :=
  TopCat.ofHom ⟨fun u ↦ ⟨u.1.1, u.2⟩,
    continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _⟩

/-- The identity-on-points map from the closedNbhd to the `true` member of the
point-excision cover. -/
private def closedNbhdToTrueCoverMember (U : Set X) (A : Set X) :
    TopCat.of U ⟶ TopCat.of (closedExcisionCover U A true) :=
  TopCat.ofHom ⟨Set.codRestrict (topologicalSubsetInclusion (TopCat.of X) U)
      (closedExcisionCover U A true) (fun y ↦ by change y.1 ∈ U; exact y.2),
    (topologicalSubsetInclusion (TopCat.of X) U).hom.continuous.codRestrict _⟩

/-- The chain map from closedNbhd chains to the point-excision-small chains. -/
private def closedNbhdToClosedExcisionSmallSingularSet (U : Set X) (A : Set X) :
    TopCat.toSSet.obj (TopCat.of U) ⟶
      coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A) :=
  SSet.Subcomplex.lift
    (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U)) (by
      intro n z hz
      rw [mem_coverSmallSingularSubcomplex_iff]
      refine ⟨true, ?_⟩
      change z ∈ Set.range ((TopCat.toSSet.map
        (topologicalSubsetInclusion (TopCat.of X) (closedExcisionCover U A true))).app n)
      obtain ⟨a, rfl⟩ := hz
      refine ⟨(TopCat.toSSet.map (closedNbhdToTrueCoverMember U A)).app n a, ?_⟩
      apply ((TopCat.of X).toSSetObjEquiv n).injective
      ext t
      rfl)

@[reassoc (attr := simp)]
lemma closedNbhdToClosedExcisionSmallSingularSet_comp_inclusion
    (U : Set X) (A : Set X) :
    closedNbhdToClosedExcisionSmallSingularSet U A ≫
        (coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A)).ι =
      TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U) := rfl

private def closedNbhdToClosedExcisionSmallChains (U : Set X) (A : Set X) :
    (TopCat.toSSet.obj (TopCat.of U)).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      ClosedExcisionSmallChainComplex U A :=
  SSet.chainComplexMap
    (closedNbhdToClosedExcisionSmallSingularSet U A)
    (ModuleCat.of ℚ ℚ)

/-- The chain map from `U ∖ A` to `X ∖ A`. -/
private def closedNbhdClosedComplementToClosedComplementChains (U : Set X) (A : Set X) :
    (TopCat.toSSet.obj (closedNbhdClosedComplementPair U A).snd).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      (TopCat.toSSet.obj (closedComplementPair A).snd).chainComplex (ModuleCat.of ℚ ℚ) :=
  SSet.chainComplexMap
    (TopCat.toSSet.map (closedNbhdClosedComplementToClosedComplement U A))
    (ModuleCat.of ℚ ℚ)

lemma closedNbhdClosedComplementToSmall_sSet_square (U : Set X) (A : Set X) :
    TopCat.toSSet.map (closedNbhdClosedComplementToClosedComplement U A) ≫
        closedComplementToExcisionSmallSingularSet U A =
      TopCat.toSSet.map (closedNbhdClosedComplementPair U A).map ≫
        closedNbhdToClosedExcisionSmallSingularSet U A := rfl

lemma closedNbhdClosedComplementToSmall_chain_square (U : Set X) (A : Set X) :
    closedNbhdClosedComplementToClosedComplementChains U A ≫
        closedComplementToExcisionSmallChains U A =
      closedNbhdSubspaceChainMap U A ≫
        closedNbhdToClosedExcisionSmallChains U A := by
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  have h := F.congr_map (closedNbhdClosedComplementToSmall_sSet_square U A)
  calc
    closedNbhdClosedComplementToClosedComplementChains U A ≫
        closedComplementToExcisionSmallChains U A =
      F.map (TopCat.toSSet.map (closedNbhdClosedComplementToClosedComplement U A) ≫
        closedComplementToExcisionSmallSingularSet U A) :=
          (F.map_comp _ _).symm
    _ = F.map (TopCat.toSSet.map (closedNbhdClosedComplementPair U A).map ≫
        closedNbhdToClosedExcisionSmallSingularSet U A) := h
    _ = closedNbhdSubspaceChainMap U A ≫
        closedNbhdToClosedExcisionSmallChains U A := F.map_comp _ _

/-- The morphism of chain-complex arrows from the closedNbhd pair to the small pair. -/
private def closedNbhdPairChainsToClosedExcisionSmallArrow (U : Set X) (A : Set X) :
    (chainPairFunctor ℚ).obj (closedNbhdClosedComplementPair U A) ⟶
      closedExcisionSmallChainArrow U A :=
  Arrow.homMk
    (closedNbhdClosedComplementToClosedComplementChains U A)
    (closedNbhdToClosedExcisionSmallChains U A)
    (closedNbhdClosedComplementToSmall_chain_square U A)

/-- Inclusion of the closedNbhd pair into the small relative quotient. -/
private def closedNbhdRelativeToClosedExcisionSmallRelativeChainMap (U : Set X) (A : Set X) :
    (relativeChainFunctor ℚ).obj (closedNbhdClosedComplementPair U A) ⟶
      ClosedExcisionSmallRelativeChainComplex U A :=
  (Limits.coker (C := ChainCategory ℚ)).map
    (closedNbhdPairChainsToClosedExcisionSmallArrow U A)

@[reassoc]
lemma closedNbhdRelativeProjection_comp_toClosedExcisionSmall
    (U : Set X) (A : Set X) :
    closedNbhdRelativeProjection U A ≫
        closedNbhdRelativeToClosedExcisionSmallRelativeChainMap U A =
      closedNbhdToClosedExcisionSmallChains U A ≫
        closedExcisionSmallRelativeProjection U A :=
  ((coker.π (C := ChainCategory ℚ)).naturality
    (closedNbhdPairChainsToClosedExcisionSmallArrow U A)).symm

lemma closedComplementCoverMember_eq_of_avoidsSet
    (U : Set X) (A : Set X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A) : SSet)
      _⦋n⦌)
    (a : (TopCat.toSSet.obj (closedComplementPair A).snd) _⦋n⦌)
    (ha : (TopCat.toSSet.map (closedComplementAmbientInclusion A)).app _ a = σ.1) :
    (closedComplementToExcisionSmallSingularSet U A).app _ a = σ := by
  apply Subtype.ext
  have h := congr_app
    (closedComplementToExcisionSmallSingularSet_comp_inclusion U A)
    (Opposite.op (SimplexCategory.mk n))
  exact (ConcreteCategory.congr_hom h a).trans ha

lemma closedNbhdCoverMember_eq_of_not_avoidsSet
    (U : Set X) (A : Set X) {n : ℕ}
    (σ : (coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A) : SSet)
      _⦋n⦌)
    (hσ : ¬ ClosedExcisionSmallSimplex.AvoidsSet U A σ) :
    (closedNbhdToClosedExcisionSmallSingularSet U A).app _
        (ClosedExcisionSmallSimplex.closedNbhdPreimage U A σ hσ) = σ := by
  apply Subtype.ext
  have h := congr_app
    (closedNbhdToClosedExcisionSmallSingularSet_comp_inclusion U A)
    (Opposite.op (SimplexCategory.mk n))
  exact (ConcreteCategory.congr_hom h
    (ClosedExcisionSmallSimplex.closedNbhdPreimage U A σ hσ)).trans
      (ClosedExcisionSmallSimplex.closedNbhdPreimage_map U A σ hσ)

/-- Going from small chains to closedNbhd relative chains and back to the small relative
quotient is the canonical small-relative projection. -/
lemma closedExcisionSmallToClosedNbhd_comp_toSmallRelative
    (U : Set X) (A : Set X) :
    closedExcisionSmallToClosedNbhdRelativeChainMap U A ≫
        closedNbhdRelativeToClosedExcisionSmallRelativeChainMap U A =
      closedExcisionSmallRelativeProjection U A := by
  apply HomologicalComplex.hom_ext
  intro n
  change closedExcisionSmallToClosedNbhdRelativeComponent U A n ≫
      (closedNbhdRelativeToClosedExcisionSmallRelativeChainMap U A).f n =
    (closedExcisionSmallRelativeProjection U A).f n
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, iota_closedExcisionSmallToClosedNbhdRelativeComponent]
  by_cases hσ : ClosedExcisionSmallSimplex.AvoidsSet U A σ
  · rw [dif_pos hσ, zero_comp]
    symm
    obtain ⟨a, ha⟩ := hσ
    rw [← closedComplementCoverMember_eq_of_avoidsSet U A σ a ha,
      ← SSet.ι_chainComplexMap_f, Category.assoc]
    have hc := congrArg (fun f ↦ f.f n)
      (cokernel.condition (closedComplementToExcisionSmallChains U A))
    change (closedComplementToExcisionSmallChains U A).f n ≫
      (closedExcisionSmallRelativeProjection U A).f n = 0 at hc
    change (TopCat.toSSet.obj (closedComplementPair A).snd).ιChainComplex a ≫
      ((closedComplementToExcisionSmallChains U A).f n ≫
        (closedExcisionSmallRelativeProjection U A).f n) = 0
    rw [hc, comp_zero]
  · rw [dif_neg hσ, Category.assoc]
    have hc := congrArg (fun f ↦ f.f n)
      (closedNbhdRelativeProjection_comp_toClosedExcisionSmall U A)
    change closedNbhdRelativeProjectionComponent U A n ≫
        (closedNbhdRelativeToClosedExcisionSmallRelativeChainMap U A).f n =
      (closedNbhdToClosedExcisionSmallChains U A).f n ≫
        (closedExcisionSmallRelativeProjection U A).f n at hc
    rw [hc, ← Category.assoc]
    change ((TopCat.toSSet.obj (TopCat.of U)).ιChainComplex
        (ClosedExcisionSmallSimplex.closedNbhdPreimage U A σ hσ) ≫
      (SSet.chainComplexMap (closedNbhdToClosedExcisionSmallSingularSet U A)
        (ModuleCat.of ℚ ℚ)).f n) ≫
      (closedExcisionSmallRelativeProjection U A).f n = _
    rw [SSet.ι_chainComplexMap_f,
      closedNbhdCoverMember_eq_of_not_avoidsSet U A σ hσ]

/-- Restricting closedNbhd chains to the small complex and then applying the explicit
small-to-relative map is the ordinary closedNbhd-relative projection. -/
lemma closedNbhdToClosedExcisionSmall_comp_smallToClosedNbhd
    (U : Set X) (A : Set X) :
    closedNbhdToClosedExcisionSmallChains U A ≫
        closedExcisionSmallToClosedNbhdRelativeChainMap U A =
      closedNbhdRelativeProjection U A := by
  apply HomologicalComplex.hom_ext
  intro n
  change (closedNbhdToClosedExcisionSmallChains U A).f n ≫
      closedExcisionSmallToClosedNbhdRelativeComponent U A n =
    closedNbhdRelativeProjectionComponent U A n
  apply SSet.chainComplex_hom_ext
  intro u
  change ((TopCat.toSSet.obj (TopCat.of U)).ιChainComplex u ≫
      (SSet.chainComplexMap (closedNbhdToClosedExcisionSmallSingularSet U A)
        (ModuleCat.of ℚ ℚ)).f n) ≫
      closedExcisionSmallToClosedNbhdRelativeComponent U A n = _
  rw [SSet.ι_chainComplexMap_f]
  let σ := (closedNbhdToClosedExcisionSmallSingularSet U A).app _ u
  rw [iota_closedExcisionSmallToClosedNbhdRelativeComponent]
  have hs := congr_app
    (closedNbhdToClosedExcisionSmallSingularSet_comp_inclusion U A)
    (Opposite.op (SimplexCategory.mk n))
  have hsu := ConcreteCategory.congr_hom hs u
  by_cases hσ : ClosedExcisionSmallSimplex.AvoidsSet U A σ
  · rw [dif_pos hσ]
    symm
    obtain ⟨a, ha⟩ := hσ
    exact closedNbhdSimplex_projection_zero_of_ambient_eq U A u a (hsu.symm.trans ha.symm)
  · rw [dif_neg hσ]
    congr 1
    apply congrArg (fun z ↦ (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex z)
    apply closedNbhdInclusion_singular_injective U
    exact (ClosedExcisionSmallSimplex.closedNbhdPreimage_map U A σ hσ).trans hsu

/-- The two explicit maps between closedNbhd-relative and small-relative chains are inverse
in the small-to-closedNbhd order. -/
lemma closedExcisionSmallRelativeToClosedNbhd_comp_closedNbhdToSmall
    (U : Set X) (A : Set X) :
    closedExcisionSmallRelativeToClosedNbhdRelativeChainMap U A ≫
        closedNbhdRelativeToClosedExcisionSmallRelativeChainMap U A =
      𝟙 (ClosedExcisionSmallRelativeChainComplex U A) := by
  let : Epi (closedExcisionSmallRelativeProjection U A) := by
    change Epi (colimit.ι
      (parallelPair (closedComplementToExcisionSmallChains U A) 0)
      WalkingParallelPair.one)
    infer_instance
  apply (cancel_epi (closedExcisionSmallRelativeProjection U A)).1
  rw [← Category.assoc, closedExcisionSmallRelativeProjection_comp_toClosedNbhd,
    closedExcisionSmallToClosedNbhd_comp_toSmallRelative, Category.comp_id]

lemma closedNbhdToSmallProjection_comp_toClosedNbhd
    (U : Set X) (A : Set X) :
    (closedNbhdToClosedExcisionSmallChains U A ≫
      closedExcisionSmallRelativeProjection U A) ≫
        closedExcisionSmallRelativeToClosedNbhdRelativeChainMap U A =
        closedNbhdRelativeProjection U A := by
  rw [Category.assoc, closedExcisionSmallRelativeProjection_comp_toClosedNbhd]
  exact closedNbhdToClosedExcisionSmall_comp_smallToClosedNbhd U A

/-- The two explicit maps between closedNbhd-relative and small-relative chains are inverse
in the closedNbhd-to-small order. -/
lemma closedNbhdToSmall_comp_closedExcisionSmallRelativeToClosedNbhd
    (U : Set X) (A : Set X) :
    closedNbhdRelativeToClosedExcisionSmallRelativeChainMap U A ≫
        closedExcisionSmallRelativeToClosedNbhdRelativeChainMap U A =
      𝟙 ((relativeChainFunctor ℚ).obj (closedNbhdClosedComplementPair U A)) := by
  let : Epi (closedNbhdRelativeProjection U A) := by
    change Epi (colimit.ι
      (parallelPair
        ((chainPairFunctor ℚ).obj (closedNbhdClosedComplementPair U A)).hom 0)
      WalkingParallelPair.one)
    infer_instance
  apply (cancel_epi
    (closedNbhdRelativeProjection U A)).1
  rw [closedNbhdRelativeProjection_comp_toClosedExcisionSmall_assoc,
    ← Category.assoc, closedNbhdToSmallProjection_comp_toClosedNbhd, Category.comp_id]

/-- ClosedNbhd-relative chains are isomorphic to the point-excision-small relative
quotient. -/
private def closedNbhdRelativeClosedExcisionSmallIso (U : Set X) (A : Set X) :
    (relativeChainFunctor ℚ).obj (closedNbhdClosedComplementPair U A) ≅
      ClosedExcisionSmallRelativeChainComplex U A where
  hom := closedNbhdRelativeToClosedExcisionSmallRelativeChainMap U A
  inv := closedExcisionSmallRelativeToClosedNbhdRelativeChainMap U A
  hom_inv_id := closedNbhdToSmall_comp_closedExcisionSmallRelativeToClosedNbhd U A
  inv_hom_id := closedExcisionSmallRelativeToClosedNbhd_comp_closedNbhdToSmall U A

lemma closedComplementAmbientInclusion_eq_pairMap (A : Set X) :
    closedComplementAmbientInclusion A = (closedComplementPair A).map := rfl

/-- The chain inclusion for the ambient point-complement pair, with both singular chain
complexes exposed. -/
private abbrev ambientClosedComplementSubspaceChainMap (A : Set X) :
    (TopCat.toSSet.obj (closedComplementPair A).snd).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℚ ℚ) :=
  ((chainPairFunctor ℚ).obj (closedComplementPair A)).hom

/-- The explicit singular-chain map underlying the ambient point-complement inclusion. -/
private def closedComplementAmbientChainMap (A : Set X) :
    (TopCat.toSSet.obj (closedComplementPair A).snd).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℚ ℚ) :=
  SSet.chainComplexMap (TopCat.toSSet.map (closedComplementAmbientInclusion A))
    (ModuleCat.of ℚ ℚ)

lemma closedComplementAmbientChainMap_eq_subspaceChainMap (A : Set X) :
    closedComplementAmbientChainMap A = ambientClosedComplementSubspaceChainMap A := rfl

instance closedComplementAmbientInclusion_mono (A : Set X) :
    Mono (closedComplementAmbientInclusion A) :=
  (TopCat.mono_iff_injective _).2 fun _ _ h ↦ Subtype.ext h

instance closedComplementAmbientChainMap_mono (A : Set X) :
    Mono (closedComplementAmbientChainMap A) := by
  dsimp [closedComplementAmbientChainMap, SSet.chainComplexMap,
    SSet.chainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono

instance ambientClosedComplementSubspaceChainMap_mono (A : Set X) :
    Mono (ambientClosedComplementSubspaceChainMap A) := by
  rw [← closedComplementAmbientChainMap_eq_subspaceChainMap]
  infer_instance

/-- The ambient relative-chain projection, with its absolute chain source exposed. -/
private abbrev ambientClosedComplementRelativeProjection (A : Set X) :
    (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      (relativeChainFunctor ℚ).obj (closedComplementPair A) :=
  relativeChainProjection ℚ (closedComplementPair A)

/-- The point-complement-to-small map followed by small-chain inclusion is the ordinary
point-complement chain inclusion. -/
lemma closedComplementToExcisionSmallChains_comp_ambientInclusion
    (U : Set X) (A : Set X) :
    closedComplementToExcisionSmallChains U A ≫
        coverSmallRationalSingularChainInclusion
          (TopCat.of X) (closedExcisionCover U A) =
      ambientClosedComplementSubspaceChainMap A := by
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  calc
    closedComplementToExcisionSmallChains U A ≫
        coverSmallRationalSingularChainInclusion
          (TopCat.of X) (closedExcisionCover U A) =
      F.map (closedComplementToExcisionSmallSingularSet U A ≫
        (coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A)).ι) :=
          (F.map_comp _ _).symm
    _ = F.map (TopCat.toSSet.map (closedComplementAmbientInclusion A)) := by
      rw [closedComplementToExcisionSmallSingularSet_comp_inclusion]
    _ = ambientClosedComplementSubspaceChainMap A := by
      rw [closedComplementAmbientInclusion_eq_pairMap]
      rfl

instance closedComplementToExcisionSmallChains_mono (U : Set X) (A : Set X) :
    Mono (closedComplementToExcisionSmallChains U A) :=
  mono_of_mono_fac
    (closedComplementToExcisionSmallChains_comp_ambientInclusion U A)

/-- The identity map on point-complement chains, with the codomain presented as the left
object of the ambient chain-pair arrow. -/
private def closedComplementChainsToAmbientPairLeft (A : Set X) :
    (TopCat.toSSet.obj (closedComplementPair A).snd).chainComplex
        (ModuleCat.of ℚ ℚ) ⟶
      ((chainPairFunctor ℚ).obj (closedComplementPair A)).left :=
  𝟙 _

instance closedComplementChainsToAmbientPairLeft_isIso (A : Set X) :
    IsIso (closedComplementChainsToAmbientPairLeft A) := by
  exact ⟨⟨𝟙 _, Category.comp_id _, Category.comp_id _⟩⟩

lemma closedComplementChainsToAmbientPairLeft_comp
    (U : Set X) (A : Set X) :
    closedComplementChainsToAmbientPairLeft A ≫
        ((chainPairFunctor ℚ).obj (closedComplementPair A)).hom =
      closedComplementToExcisionSmallChains U A ≫
        coverSmallRationalSingularChainInclusion
          (TopCat.of X) (closedExcisionCover U A) := by
  change 𝟙 _ ≫ ambientClosedComplementSubspaceChainMap A = _
  exact (closedComplementToExcisionSmallChains_comp_ambientInclusion U A).symm

/-- The morphism of chain-pair arrows from the point-excision-small pair to the ambient
point-complement pair. -/
private def closedExcisionSmallToAmbientPairArrow (U : Set X) (A : Set X) :
    closedExcisionSmallChainArrow U A ⟶
      (chainPairFunctor ℚ).obj (closedComplementPair A) :=
  Arrow.homMk
    (closedComplementChainsToAmbientPairLeft A)
    (coverSmallRationalSingularChainInclusion
      (TopCat.of X) (closedExcisionCover U A))
    (closedComplementChainsToAmbientPairLeft_comp U A)

/-- The map from the point-excision-small relative quotient to ambient relative chains. -/
private def closedExcisionSmallRelativeToAmbientRelativeChainMap (U : Set X) (A : Set X) :
    ClosedExcisionSmallRelativeChainComplex U A ⟶
      (relativeChainFunctor ℚ).obj (closedComplementPair A) :=
  (Limits.coker (C := ChainCategory ℚ)).map
    (closedExcisionSmallToAmbientPairArrow U A)

@[reassoc]
lemma closedExcisionSmallRelativeProjection_comp_toAmbient
    (U : Set X) (A : Set X) :
    closedExcisionSmallRelativeProjection U A ≫
        closedExcisionSmallRelativeToAmbientRelativeChainMap U A =
      coverSmallRationalSingularChainInclusion
          (TopCat.of X) (closedExcisionCover U A) ≫
        ambientClosedComplementRelativeProjection A :=
  ((coker.π (C := ChainCategory ℚ)).naturality
    (closedExcisionSmallToAmbientPairArrow U A)).symm

/-- The morphism between the two cokernel short complexes used in point excision. -/
private def closedExcisionSmallToAmbientCokernelSequenceHom (U : Set X) (A : Set X) :
    ShortComplex.cokernelSequence (closedComplementToExcisionSmallChains U A) ⟶
      ShortComplex.cokernelSequence
        (ambientClosedComplementSubspaceChainMap A) :=
  ShortComplex.homMk
    (closedComplementChainsToAmbientPairLeft A)
    (coverSmallRationalSingularChainInclusion
      (TopCat.of X) (closedExcisionCover U A))
    (closedExcisionSmallRelativeToAmbientRelativeChainMap U A)
    (closedComplementChainsToAmbientPairLeft_comp U A)
    (closedExcisionSmallRelativeProjection_comp_toAmbient U A).symm

lemma closedExcisionSmallCokernelSequence_shortExact (U : Set X) (A : Set X) :
    (ShortComplex.cokernelSequence
      (closedComplementToExcisionSmallChains U A)).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by
    change Mono (closedComplementToExcisionSmallChains U A)
    infer_instance
  epi_g := by infer_instance

lemma ambientClosedComplementCokernelSequence_shortExact (A : Set X) :
    (ShortComplex.cokernelSequence
      (ambientClosedComplementSubspaceChainMap A)).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by
    change Mono (ambientClosedComplementSubspaceChainMap A)
    infer_instance
  epi_g := by infer_instance

lemma closedComplementChainsToAmbientPairLeft_quasiIso (A : Set X) :
    QuasiIso (closedComplementChainsToAmbientPairLeft A) :=
  inferInstance

/-- The small relative quotient is quasi-isomorphic to ambient relative chains when the
two-set point-excision cover is open and covers the ambient space. -/
private theorem closedExcisionSmallRelativeToAmbient_quasiIso
    (U : Set X) (A : Set X) (hU : IsOpen U) (hA : IsClosed A) (hAU : A ⊆ U) :
    QuasiIso (closedExcisionSmallRelativeToAmbientRelativeChainMap U A) := by
  let e := coverSmallRationalChainHomotopyEquiv_of_openCover
    (TopCat.of X) (closedExcisionCover U A)
      (closedExcisionCover_isOpen U A hU hA) (closedExcisionCover_iUnion U A hAU)
  have hsmall : QuasiIso e.hom := e.quasiIso_hom
  rw [coverSmallRationalChainHomotopyEquiv_of_openCover_hom] at hsmall
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃
    (closedExcisionSmallToAmbientCokernelSequenceHom U A)
    (closedExcisionSmallCokernelSequence_shortExact U A)
    (ambientClosedComplementCokernelSequence_shortExact A)
    (closedComplementChainsToAmbientPairLeft_quasiIso A)
    hsmall

/-- The ordinary chain map induced by inclusion of the closedNbhd into the ambient space. -/
private def closedNbhdAmbientChainMap (U : Set X) :
    (TopCat.toSSet.obj (TopCat.of U)).chainComplex (ModuleCat.of ℚ ℚ) ⟶
      (TopCat.toSSet.obj (TopCat.of X)).chainComplex (ModuleCat.of ℚ ℚ) :=
  SSet.chainComplexMap
    (TopCat.toSSet.map (topologicalSubsetInclusion (TopCat.of X) U))
    (ModuleCat.of ℚ ℚ)

lemma closedNbhdToClosedExcisionSmallChains_comp_ambientInclusion
    (U : Set X) (A : Set X) :
    closedNbhdToClosedExcisionSmallChains U A ≫
        coverSmallRationalSingularChainInclusion
          (TopCat.of X) (closedExcisionCover U A) =
      closedNbhdAmbientChainMap U := by
  let F := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  calc
    closedNbhdToClosedExcisionSmallChains U A ≫
        coverSmallRationalSingularChainInclusion
          (TopCat.of X) (closedExcisionCover U A) =
      F.map (closedNbhdToClosedExcisionSmallSingularSet U A ≫
        (coverSmallSingularSubcomplex (TopCat.of X) (closedExcisionCover U A)).ι) :=
          (F.map_comp _ _).symm
    _ = F.map (TopCat.toSSet.map
        (topologicalSubsetInclusion (TopCat.of X) U)) := by
      rw [closedNbhdToClosedExcisionSmallSingularSet_comp_inclusion]
    _ = closedNbhdAmbientChainMap U := rfl

@[reassoc]
lemma closedNbhdRelativeProjection_comp_ambientRelativeMap
    (U : Set X) (A : Set X) :
    closedNbhdRelativeProjection U A ≫
        (relativeChainFunctor ℚ).map (closedNbhdClosedComplementPairMap U A) =
      closedNbhdAmbientChainMap U ≫
        ambientClosedComplementRelativeProjection A := by
  exact ((coker.π (C := ChainCategory ℚ)).naturality
    ((chainPairFunctor ℚ).map (closedNbhdClosedComplementPairMap U A))).symm

lemma closedNbhdToSmallProjection_comp_toAmbient
    (U : Set X) (A : Set X) :
    (closedNbhdToClosedExcisionSmallChains U A ≫
        closedExcisionSmallRelativeProjection U A) ≫
      closedExcisionSmallRelativeToAmbientRelativeChainMap U A =
        closedNbhdAmbientChainMap U ≫
          ambientClosedComplementRelativeProjection A := by
  rw [Category.assoc, closedExcisionSmallRelativeProjection_comp_toAmbient,
    ← Category.assoc, closedNbhdToClosedExcisionSmallChains_comp_ambientInclusion]

/-- Factoring the closedNbhd pair through point-excision-small relative chains gives the
canonical map of relative chain complexes. -/
lemma closedNbhdToSmallRelative_comp_smallRelativeToAmbient
    (U : Set X) (A : Set X) :
    closedNbhdRelativeToClosedExcisionSmallRelativeChainMap U A ≫
        closedExcisionSmallRelativeToAmbientRelativeChainMap U A =
      (relativeChainFunctor ℚ).map (closedNbhdClosedComplementPairMap U A) := by
  let : Epi (closedNbhdRelativeProjection U A) := by
    change Epi (colimit.ι
      (parallelPair
        ((chainPairFunctor ℚ).obj (closedNbhdClosedComplementPair U A)).hom 0)
      WalkingParallelPair.one)
    infer_instance
  apply (cancel_epi (closedNbhdRelativeProjection U A)).1
  rw [closedNbhdRelativeProjection_comp_toClosedExcisionSmall_assoc,
    ← Category.assoc, closedNbhdToSmallProjection_comp_toAmbient,
    closedNbhdRelativeProjection_comp_ambientRelativeMap]

end Port

/-- Excision of a closed set at chain level: for `U` open, `A` closed and `A ⊆ U`, the inclusion
`(U, U ∖ A) → (X, X ∖ A)` induces a quasi-isomorphism of rational relative chain complexes. -/
theorem relativeChainMap_quasiIso
    {U A : Set X} (hU : IsOpen U) (hA : IsClosed A) (hAU : A ⊆ U) :
    QuasiIso ((relativeChainFunctor ℚ).map
      (TopPair.ofSubsetHom (A := {u : U | u.1 ∉ A}) (B := Aᶜ)
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of U ⟶ TopCat.of X)
        (fun _ ha => ha))) := by
  change QuasiIso ((relativeChainFunctor ℚ).map (closedNbhdClosedComplementPairMap U A))
  let : IsIso (closedNbhdRelativeToClosedExcisionSmallRelativeChainMap U A) :=
    (closedNbhdRelativeClosedExcisionSmallIso U A).isIso_hom
  let : QuasiIso (closedExcisionSmallRelativeToAmbientRelativeChainMap U A) :=
    closedExcisionSmallRelativeToAmbient_quasiIso U A hU hA hAU
  rw [← closedNbhdToSmallRelative_comp_smallRelativeToAmbient]
  infer_instance

/-- A map of pairs inducing a quasi-isomorphism of rational relative chains is bijective on
relative homology. -/
theorem relativeHomologyMap_bijective_of_quasiIso {P Q : TopPair} (f : P ⟶ Q)
    [QuasiIso ((relativeChainFunctor ℚ).map f)] (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n f) := by
  have hIso : IsIso ((relativeHomologyFunctor ℚ n).map f) := by
    change IsIso (HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map f) n)
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mp hIso

end HodgeLean.RealDefs.ClosedExcision
