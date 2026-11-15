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

import HodgeLean.Foundations.ComplexSheafSingularDefs
import HodgeConjecture.Mathlib.Algebra.Homology.HomComplexPrecomp
import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.FlasqueQuasiIso
import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.InjectiveFlasque
import Mathlib.Algebra.Homology.Factorizations.CM5a

/-! Adapted, with modifications (precomposition dualized to postcomposition; the K-injective
resolution argument rewritten for the edge map `globalSectionsToHypercohomology`; the upstream
licence and notice are in this directory's `LICENSE` and `NOTICE`), from upstream's
`HodgeConjecture/Mathlib/Algebra/Homology/HomComplexPrecomp.lean` and
`Other/AlgebraicGeometry/Cohomology/GlobalSections.lean` at `2ead713`. -/

/-! # Naturality of the edge map

Postcomposition with a chain map on the Hom complex, and the naturality of the edge map
`globalSectionsToHypercohomology` in the complex of sheaves. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ComplexPoint TopologicalSpace

namespace CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Abelian C]
  (K : CochainComplex C ℤ) {L L' : CochainComplex C ℤ} (g : L ⟶ L')

/-- Postcomposition with a chain map, on the Hom complex.

Source: the dual of upstream's `CochainComplex.HomComplex.precompMap`
(`HodgeConjecture/Mathlib/Algebra/Homology/HomComplexPrecomp.lean` at `2ead713`). -/
def postcompMap : HomComplex K L ⟶ HomComplex K L' where
  f n := AddCommGrpCat.ofHom
    { toFun z := z.comp (Cochain.ofHom g) (add_zero n)
      map_zero' := by simp
      map_add' _ _ := Cochain.add_comp _ _ _ _ }
  comm' n m _ := by
    ext z
    exact δ_comp_ofHom z g m

example (n : ℤ) (z : Cochain K L n) :
    (postcompMap K g).f n z = z.comp (Cochain.ofHom g) (add_zero n) := rfl

/-- Postcomposition with a chain map, on cohomology classes.

Source: the dual of upstream's `CochainComplex.HomComplex.precompClass`
(`HodgeConjecture/Mathlib/Algebra/Homology/HomComplexPrecomp.lean` at `2ead713`). -/
def postcompClass (n : ℤ) : CohomologyClass K L n →+ CohomologyClass K L' n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom K L' n).comp
      { toFun z := z.postcomp g
        map_zero' := by ext; simp [Cocycle.postcomp]
        map_add' x y := by ext; simp [Cocycle.postcomp, Cochain.add_comp] }) (by
      intro z hz
      obtain ⟨m, hm, a, ha⟩ := hz
      change CohomologyClass.mk (z.postcomp g) = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      refine ⟨m, hm, a.comp (Cochain.ofHom g) (add_zero m), ?_⟩
      rw [δ_comp_ofHom, ha]
      rfl)

@[simp]
lemma postcompClass_mk (n : ℤ) (z : Cocycle K L n) :
    postcompClass K g n (CohomologyClass.mk z) = CohomologyClass.mk (z.postcomp g) := rfl

example (n : ℤ) : postcompClass K (𝟙 L) n 0 = 0 := map_zero _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The cocycle and cohomology-class maps of postcomposition describe its homology map.

Source: the dual of upstream's `CochainComplex.HomComplex.precompLeftHomologyMapData`
(`HodgeConjecture/Mathlib/Algebra/Homology/HomComplexPrecomp.lean` at `2ead713`). -/
def postcompLeftHomologyMapData (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat ℤᵘᵖ n).map (postcompMap K g))
      (leftHomologyData K L n) (leftHomologyData K L' n) where
  φK := AddCommGrpCat.ofHom
    { toFun z := z.postcomp g
      map_zero' := by ext; simp [Cocycle.postcomp]
      map_add' x y := by ext; simp [Cocycle.postcomp, Cochain.add_comp] }
  φH := AddCommGrpCat.ofHom (postcompClass K g n)
  commi := rfl
  commf' := by
    apply (cancel_mono (leftHomologyData K L' n).i).1
    rw [Category.assoc, show
      AddCommGrpCat.ofHom
        { toFun z := z.postcomp g
          map_zero' := by ext; simp [Cocycle.postcomp]
          map_add' x y := by ext; simp [Cocycle.postcomp, Cochain.add_comp] } ≫
          (leftHomologyData K L' n).i =
        (leftHomologyData K L n).i ≫ (postcompMap K g).f n from rfl,
      ← Category.assoc, ShortComplex.LeftHomologyData.f'_i,
      Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((HomologicalComplex.shortComplexFunctor AddCommGrpCat ℤᵘᵖ n).map
      (postcompMap K g)).comm₁₂.symm
  commπ := rfl

example (n : ℤ) : (postcompLeftHomologyMapData K g n).φH = AddCommGrpCat.ofHom (postcompClass K g n) :=
  rfl

lemma homologyAddEquiv_postcompMap (n : ℤ) (x : (HomComplex K L).homology n) :
    homologyAddEquiv K L' n (HomologicalComplex.homologyMap (postcompMap K g) n x) =
      postcompClass K g n (homologyAddEquiv K L n x) :=
  ConcreteCategory.congr_hom (postcompLeftHomologyMapData K g n).homologyMap_comm x

variable [HasZeroObject C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Postcomposition with `g` on `Hom^•(X[0], L)` is postcomposition with `g` on
`n ↦ Hom(X, L^n)`. -/
lemma postcompMap_fromSingleZeroIsoPreadditiveCoyoneda (X : C) :
    postcompMap ((CochainComplex.singleFunctor C 0).obj X) g ≫
        (fromSingleZeroIsoPreadditiveCoyoneda X L').hom =
      (fromSingleZeroIsoPreadditiveCoyoneda X L).hom ≫
        ((preadditiveCoyoneda.obj (.op X)).mapHomologicalComplex ℤᵘᵖ).map g := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  apply AddCommGrpCat.hom_ext
  refine AddMonoidHom.ext (fun z => ?_)
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective z n (zero_add n)
  change Cochain.fromSingleEquiv (zero_add n)
      ((Cochain.fromSingleMk f (zero_add n)).comp (Cochain.ofHom g) (add_zero n)) =
    Cochain.fromSingleEquiv (zero_add n) (Cochain.fromSingleMk f (zero_add n)) ≫ g.f n
  rw [← Cochain.fromSingleMk_postcomp, Cochain.fromSingleEquiv_fromSingleMk,
    Cochain.fromSingleEquiv_fromSingleMk]

end CochainComplex.HomComplex

namespace CochainComplex.HomComplex.CohomologyClass

universe w

variable {C : Type*} [Category* C] [Abelian C]
  {K L L' : CochainComplex C ℤ} (g : L ⟶ L') {n : ℤ}
  [Localization.HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L]
  [Localization.HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L']
  [Localization.HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ L L']
  [Localization.HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ L' L']

/-- The localization map of cohomology classes commutes with postcomposition by a chain map. -/
lemma toSmallShiftedHom_postcompClass (x : CohomologyClass K L n) :
    (postcompClass K g n x).toSmallShiftedHom =
      x.toSmallShiftedHom.comp
        (Localization.SmallShiftedHom.mk₀ _ (0 : ℤ) rfl g) (zero_add n) := by
  obtain ⟨z, rfl⟩ := x.mk_surjective
  let := HasDerivedCategory.standard C
  apply (Localization.SmallShiftedHom.equiv _ DerivedCategory.Q).injective
  rw [postcompClass_mk, Localization.SmallShiftedHom.equiv_comp, equiv_toSmallShiftedHom_mk,
    equiv_toSmallShiftedHom_mk, Localization.SmallShiftedHom.equiv_mk₀,
    Cocycle.equivHomShift_symm_postcomp, ShiftedHom.comp_mk₀]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]
  congr 1
  exact (DerivedCategory.Q.commShiftIso n).hom.naturality g

end CochainComplex.HomComplex.CohomologyClass

namespace HodgeLean.Foundations

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The identification `Hom^•(ℤ[0], S) ≅ Γ(S)` is natural in the complex of sheaves `S`. -/
lemma homComplexSingleIntegerIsoGlobalSections_naturality (Y : TopCat.{0})
    {S T : CochainComplex (TopCat.Sheaf AddCommGrpCat Y) ℤ} (f : S ⟶ T) :
    CochainComplex.HomComplex.postcompMap (TopCat.Sheaf.integerConstantSingleComplex Y) f ≫
        (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y T).hom =
      (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y S).hom ≫
        (show TopCat.Sheaf.globalSectionsComplexInt Y S ⟶ TopCat.Sheaf.globalSectionsComplexInt Y T
          from ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            Y).mapHomologicalComplex ℤᵘᵖ).map f) := by
  dsimp only [TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections,
    TopCat.Sheaf.integerConstantSingleComplex, Iso.trans_hom]
  rw [← Category.assoc, CochainComplex.HomComplex.postcompMap_fromSingleZeroIsoPreadditiveCoyoneda,
    Category.assoc, Category.assoc]
  congr 1

/-- A commutative square of complexes of abelian groups gives a commutative square in homology,
elementwise. -/
lemma homologyMap_apply_of_comm {A B C D : CochainComplex AddCommGrpCat ℤ}
    {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D} (h : a ≫ b = c ≫ d) (n : ℤ)
    (x : A.homology n) :
    HomologicalComplex.homologyMap b n (HomologicalComplex.homologyMap a n x) =
      HomologicalComplex.homologyMap d n (HomologicalComplex.homologyMap c n x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, h]

section

local instance edgeNatHasDerivedCategory (X : Over (Spec ↧ℂ)) :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- The edge map `H^n(Γ(S)) → ℍ^n(S)` is natural in the complex of sheaves `S`. -/
theorem globalSectionsToHypercohomology_naturality (X : Over (Spec ↧ℂ))
    {S T : CochainComplex (AnalyticAdditiveSheaf X) ℤ} (f : S ⟶ T) (n : ℤ)
    (x : (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) S).homology n) :
    globalSectionsToHypercohomology X T n
        (HomologicalComplex.homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map f) n x) =
      hypercohomologyMap X f n (globalSectionsToHypercohomology X S n x) := by
  let Y := TopCat.of (ComplexPoint X)
  have hnat : (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y S).inv ≫
      CochainComplex.HomComplex.postcompMap (TopCat.Sheaf.integerConstantSingleComplex Y) f =
      (show TopCat.Sheaf.globalSectionsComplexInt Y S ⟶ TopCat.Sheaf.globalSectionsComplexInt Y T
          from ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            Y).mapHomologicalComplex ℤᵘᵖ).map f) ≫
        (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y T).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← homComplexSingleIntegerIsoGlobalSections_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h1 : HomologicalComplex.homologyMap
      (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y T).inv n
        (HomologicalComplex.homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            Y).mapHomologicalComplex ℤᵘᵖ).map f) n x) =
      HomologicalComplex.homologyMap
        (CochainComplex.HomComplex.postcompMap (TopCat.Sheaf.integerConstantSingleComplex Y) f) n
        (HomologicalComplex.homologyMap
          (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y S).inv n x) := by
    exact (homologyMap_apply_of_comm hnat n x).symm
  change cohomologyClassToHypercohomology X T n
      (CochainComplex.HomComplex.homologyAddEquiv _ T n
        (HomologicalComplex.homologyMap
          (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y T).inv n _)) =
    hypercohomologyMap X f n (cohomologyClassToHypercohomology X S n
      (CochainComplex.HomComplex.homologyAddEquiv _ S n
        (HomologicalComplex.homologyMap
          (TopCat.Sheaf.homComplexSingleIntegerIsoGlobalSections Y S).inv n x)))
  rw [h1, CochainComplex.HomComplex.homologyAddEquiv_postcompMap]
  generalize CochainComplex.HomComplex.homologyAddEquiv _ S n _ = c
  change (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
      (constantIntegerSheafComplexIntIsoSingle X).hom).comp
        (CochainComplex.HomComplex.postcompClass _ f n c).toSmallShiftedHom (add_zero n) =
    ((Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) (0 : ℤ) rfl
      (constantIntegerSheafComplexIntIsoSingle X).hom).comp c.toSmallShiftedHom
        (add_zero n)).comp
      (Localization.SmallShiftedHom.mk₀ (analyticQuasiIsomorphisms X) 0 rfl f) (zero_add n)
  rw [CochainComplex.HomComplex.CohomologyClass.toSmallShiftedHom_postcompClass,
    Localization.SmallShiftedHom.comp_assoc _ _ _ _ _ _ (by simp)]

example (X : Over (Spec ↧ℂ)) (S : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (n : ℤ)
    (x : (TopCat.Sheaf.globalSectionsComplexInt (TopCat.of (ComplexPoint X)) S).homology n) :
    globalSectionsToHypercohomology X S n
        (HomologicalComplex.homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map (𝟙 S)) n x) =
      hypercohomologyMap X (𝟙 S) n (globalSectionsToHypercohomology X S n x) :=
  globalSectionsToHypercohomology_naturality X (𝟙 S) n x

end

end HodgeLean.Foundations

namespace HodgeLean.Foundations

section

local instance edgeBijHasDerivedCategory (X : Over (Spec ↧ℂ)) :
    HasDerivedCategory (AnalyticAdditiveSheaf X) :=
  HasDerivedCategory.standard (AnalyticAdditiveSheaf X)

/-- The edge map is bijective for a K-injective target complex. -/
lemma globalSectionsToHypercohomology_bijective_of_isKInjective (X : Over (Spec ↧ℂ))
    (I : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [I.IsKInjective] (n : ℤ) :
    Function.Bijective (globalSectionsToHypercohomology X I n) := by
  let e := constantIntegerSheafComplexIntIsoSingle X
  have he : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X) ℤᵘᵖ e.hom := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have h1 : Function.Bijective (cohomologyClassToHypercohomology X I n) :=
    (Localization.SmallShiftedHom.precompEquiv.{1} e.hom he (a := n)).bijective.comp
      (CochainComplex.HomComplex.CohomologyClass.bijective_toSmallShiftedHom_of_isKInjective.{1}
        _ I n)
  exact h1.comp (AddEquiv.bijective _)

/-- The edge map `H^n(Γ(S)) → ℍ^n(S)` is bijective for a bounded-below complex `S` of flasque
sheaves.

Source: Bredon, *Sheaf Theory*, 2nd ed., GTM 170, II.4 (flasque sheaves are acyclic for global
sections); the proof follows upstream's `rationalSingularCochainHypercohomologyAddEquivGlobalSections`
(`Other/AlgebraicGeometry/Cohomology/GlobalSections.lean` at `2ead713`): a K-injective resolution
`i : S → I`, `globalSectionsComplex_map_quasiIso` and the naturality of the edge map. -/
theorem globalSectionsToHypercohomology_bijective_of_flasque (X : Over (Spec ↧ℂ))
    (S : CochainComplex (AnalyticAdditiveSheaf X) ℤ) (m : ℤ) [S.IsStrictlyGE m]
    (hS : ∀ q, (S.X q).IsFlasque) (n : ℤ) :
    Function.Bijective (globalSectionsToHypercohomology X S n) := by
  obtain ⟨I, i, _, _, _⟩ := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective S m
  have : I.IsKInjective := CochainComplex.isKInjective_of_injective I m
  have hI : ∀ q, (I.X q).IsFlasque := fun _ ↦ inferInstance
  have : QuasiIso (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
      (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map i) :=
    TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsComplex_map_quasiIso i m m hS hI
  have hi : HomologicalComplex.quasiIso (AnalyticAdditiveSheaf X) ℤᵘᵖ i := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    infer_instance
  have hpost : Function.Bijective (hypercohomologyMap X i n) :=
    (Localization.SmallShiftedHom.postcompEquiv.{1} i hi (a := n)).bijective
  rw [← Function.Bijective.of_comp_iff' hpost]
  have hcomp : (hypercohomologyMap X i n) ∘ (globalSectionsToHypercohomology X S n) =
      (globalSectionsToHypercohomology X I n) ∘
        (HomologicalComplex.homologyMap
          (((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor
            (TopCat.of (ComplexPoint X))).mapHomologicalComplex ℤᵘᵖ).map i) n) := by
    funext x
    exact (globalSectionsToHypercohomology_naturality X i n x).symm
  rw [hcomp]
  exact (globalSectionsToHypercohomology_bijective_of_isKInjective X I n).comp
    ((ConcreteCategory.bijective_of_isIso _))

example (X : Over (Spec ↧ℂ)) (S : CochainComplex (AnalyticAdditiveSheaf X) ℤ) [S.IsStrictlyGE 0]
    (hS : ∀ q, (S.X q).IsFlasque) :
    Function.Injective (globalSectionsToHypercohomology X S 1) :=
  (globalSectionsToHypercohomology_bijective_of_flasque X S 0 hS 1).injective

end

end HodgeLean.Foundations
