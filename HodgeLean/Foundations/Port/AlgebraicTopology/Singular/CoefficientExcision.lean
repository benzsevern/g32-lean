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

module

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.CoverSmall
public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Excision.OpenCover
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! Ported from upstream HodgeConjecture
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Excision/Field.lean` @ `2ead713`.
Modified: ℚ generalized to a coefficient ring K (names `Rational` → `Coefficient`,
`rationalize` → `coefficientize`); the `module` header and public/expose markers dropped.
Licensed under Apache-2.0; the upstream licence and notice are in this directory's `LICENSE`
and `NOTICE`. -/

/-!
# Small singular chains with coefficients in a commutative ring

This file transports the integral subdivision homotopy to simplicial chains with coefficients in
a commutative ring `K`, directly from the universal bases of the two simplicial chain complexes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace AlgebraicTopology.Singular

variable (K : Type) [CommRing K]

/-- `K`-chains on a simplicial set.

Source: upstream
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Excision/Field.lean` @ `2ead713`,
`RationalSimplicialChainComplex`, with ℚ generalized to a coefficient ring `K`. -/
abbrev CoefficientSimplicialChainComplex (X : SSet.{0}) :
    ChainComplex (ModuleCat K) ℕ :=
  X.chainComplex (ModuleCat.of K K)

example (X : SSet.{0}) :
    CoefficientSimplicialChainComplex K X = X.chainComplex (ModuleCat.of K K) :=
  rfl

@[simp]
lemma moduleCat_toSpanSingleton_apply_one_coeff (M : ModuleCat K) (v : M) :
    (ModuleCat.ofHom (LinearMap.toSpanSingleton K M v)).hom 1 = v := by simp

/-- The coefficient map from integral to `K`-chains in one degree.

Source: upstream
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Excision/Field.lean` @ `2ead713`,
`integralToRationalChainComponent`, with ℚ generalized to a coefficient ring `K`. -/
def integralToCoefficientChainComponent (X : SSet.{0}) (n : ℕ) :
    (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (forget₂ (ModuleCat K) AddCommGrpCat).obj ((CoefficientSimplicialChainComplex K X).X n) :=
  (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) n).desc
    (Cofan.mk _ fun x ↦
      AddCommGrpCat.ofHom (Int.castAddHom K) ≫
        (forget₂ (ModuleCat K) AddCommGrpCat).map (X.ιChainComplex (R := ModuleCat.of K K) x))

@[reassoc]
lemma iota_integralToCoefficientChainComponent (X : SSet.{0}) (n : ℕ)
    (x : X _⦋n⦌) :
    X.ιChainComplex (R := AddCommGrpCat.of ℤ) x ≫
        integralToCoefficientChainComponent K X n =
      AddCommGrpCat.ofHom (Int.castAddHom K) ≫
        (forget₂ (ModuleCat K) AddCommGrpCat).map (X.ιChainComplex (R := ModuleCat.of K K) x) :=
  (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) n).fac _ (Discrete.mk x)

/-- The coefficient map sends the integral basis chain of a simplex to its `K`-basis chain. -/
lemma integralToCoefficientChainComponent_iota_one (X : SSet.{0}) (n : ℕ)
    (x : X _⦋n⦌) :
    (integralToCoefficientChainComponent K X n).hom
        ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1) =
      (X.ιChainComplex (R := ModuleCat.of K K) x).hom 1 := by
  have hx := ConcreteCategory.congr_hom
    (iota_integralToCoefficientChainComponent K X n x) 1
  simp only [ConcreteCategory.comp_apply] at hx
  rw [hx]
  simp

/-- Extend an integral map between free simplicial-chain groups `K`-linearly.

Source: upstream
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Excision/Field.lean` @ `2ead713`,
`rationalizeSimplicialChainComponent`, with ℚ generalized to a coefficient ring `K`. -/
def coefficientizeSimplicialChainComponent (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    (CoefficientSimplicialChainComplex K X).X n ⟶
      (CoefficientSimplicialChainComplex K Y).X m :=
  (X.isColimitChainComplexXCofan (ModuleCat.of K K) n).desc
    (Cofan.mk _ fun x ↦ ModuleCat.ofHom <|
      LinearMap.toSpanSingleton K _ <|
        (show (CoefficientSimplicialChainComplex K Y).X m from
          (integralToCoefficientChainComponent K Y m).hom
            (f.hom ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1))))

@[reassoc]
lemma iota_coefficientizeSimplicialChainComponent
    (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m)
    (x : X _⦋n⦌) :
    X.ιChainComplex (R := ModuleCat.of K K) x ≫
        coefficientizeSimplicialChainComponent K X Y n m f =
      ModuleCat.ofHom (LinearMap.toSpanSingleton K _ <|
        (show (CoefficientSimplicialChainComplex K Y).X m from
          (integralToCoefficientChainComponent K Y m).hom
            (f.hom ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1)))) :=
  (X.isColimitChainComplexXCofan (ModuleCat.of K K) n).fac _ (Discrete.mk x)

lemma integralToCoefficientChainComponent_naturality
    (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    integralToCoefficientChainComponent K X n ≫
        (forget₂ (ModuleCat K) AddCommGrpCat).map
          (coefficientizeSimplicialChainComponent K X Y n m f) =
      f ≫ integralToCoefficientChainComponent K Y m := by
  refine (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) n).hom_ext fun x ↦ ?_
  change X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      (integralToCoefficientChainComponent K X n ≫
        (forget₂ (ModuleCat K) AddCommGrpCat).map
          (coefficientizeSimplicialChainComponent K X Y n m f)) =
    X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      (f ≫ integralToCoefficientChainComponent K Y m)
  apply AddCommGrpCat.int_hom_ext
  have hx := integralToCoefficientChainComponent_iota_one K X n x.as
  have hf := ConcreteCategory.congr_hom
    (iota_coefficientizeSimplicialChainComponent K X Y n m f x.as) 1
  change (coefficientizeSimplicialChainComponent K X Y n m f).hom
      ((integralToCoefficientChainComponent K X n).hom
        ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as).hom 1)) = _
  rw [hx]
  simpa using hf

lemma coefficientizeSimplicialChainComponent_comp
    (X Y Z : SSet.{0}) (n m k : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m)
    (g : (Y.chainComplex (AddCommGrpCat.of ℤ)).X m ⟶
      (Z.chainComplex (AddCommGrpCat.of ℤ)).X k) :
    coefficientizeSimplicialChainComponent K X Z n k (f ≫ g) =
      coefficientizeSimplicialChainComponent K X Y n m f ≫
        coefficientizeSimplicialChainComponent K Y Z m k g := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_coefficientizeSimplicialChainComponent K,
    iota_coefficientizeSimplicialChainComponent_assoc]
  ext
  have h := ConcreteCategory.congr_hom
    (integralToCoefficientChainComponent_naturality K Y Z m k g)
    (f.hom ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1))
  simpa using h.symm

lemma coefficientizeSimplicialChainComponent_id (X : SSet.{0}) (n : ℕ) :
    coefficientizeSimplicialChainComponent K X X n n (𝟙 _) = 𝟙 _ := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_coefficientizeSimplicialChainComponent K]
  ext
  have hx := ConcreteCategory.congr_hom
    (iota_integralToCoefficientChainComponent K X n x) 1
  simpa using hx

lemma coefficientizeSimplicialChainComponent_zero
    (X Y : SSet.{0}) (n m : ℕ) :
    coefficientizeSimplicialChainComponent K X Y n m 0 = 0 := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_coefficientizeSimplicialChainComponent K]
  simp

lemma coefficientizeSimplicialChainComponent_add
    (X Y : SSet.{0}) (n m : ℕ)
    (f g : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    coefficientizeSimplicialChainComponent K X Y n m (f + g) =
      coefficientizeSimplicialChainComponent K X Y n m f +
        coefficientizeSimplicialChainComponent K X Y n m g := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_coefficientizeSimplicialChainComponent K, Preadditive.comp_add,
    iota_coefficientizeSimplicialChainComponent K,
    iota_coefficientizeSimplicialChainComponent K]
  ext
  simp

lemma coefficientizeSimplicialChainComponent_neg
    (X Y : SSet.{0}) (n m : ℕ)
    (f : (X.chainComplex (AddCommGrpCat.of ℤ)).X n ⟶
      (Y.chainComplex (AddCommGrpCat.of ℤ)).X m) :
    coefficientizeSimplicialChainComponent K X Y n m (-f) =
      -coefficientizeSimplicialChainComponent K X Y n m f := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_coefficientizeSimplicialChainComponent K, Preadditive.comp_neg,
    iota_coefficientizeSimplicialChainComponent K]
  ext
  simp

/-- The integral-to-`K` coefficient map commutes with the simplicial differential. -/
lemma integralToCoefficientChainComponent_comm_d (X : SSet.{0}) (n : ℕ) :
    integralToCoefficientChainComponent K X (n + 1) ≫
        (forget₂ (ModuleCat K) AddCommGrpCat).map
          ((CoefficientSimplicialChainComplex K X).d (n + 1) n) =
      (X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        integralToCoefficientChainComponent K X n := by
  refine (X.isColimitChainComplexXCofan (AddCommGrpCat.of ℤ) (n + 1)).hom_ext fun x ↦ ?_
  change X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      (integralToCoefficientChainComponent K X (n + 1) ≫
        (forget₂ (ModuleCat K) AddCommGrpCat).map
          ((CoefficientSimplicialChainComplex K X).d (n + 1) n)) =
    X.ιChainComplex (R := AddCommGrpCat.of ℤ) x.as ≫
      ((X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n ≫
        integralToCoefficientChainComponent K X n)
  rw [← Category.assoc, iota_integralToCoefficientChainComponent K, Category.assoc,
    ← Functor.map_comp, SSet.ιChainComplex_d, ← Category.assoc, SSet.ιChainComplex_d,
    Preadditive.sum_comp]
  simp_rw [Preadditive.zsmul_comp, iota_integralToCoefficientChainComponent K]
  simp only [Functor.map_sum, Functor.map_zsmul]
  rw [Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Preadditive.comp_zsmul]

/-- Extension of coefficients sends the integral simplicial differential to the `K`-differential. -/
lemma coefficientizeSimplicialChainComponent_d (X : SSet.{0}) (n : ℕ) :
    coefficientizeSimplicialChainComponent K X X (n + 1) n
        ((X.chainComplex (AddCommGrpCat.of ℤ)).d (n + 1) n) =
      (CoefficientSimplicialChainComplex K X).d (n + 1) n := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_coefficientizeSimplicialChainComponent K]
  ext
  change (LinearMap.toSpanSingleton K _ _) 1 = _
  rw [LinearMap.toSpanSingleton_apply_one]
  have h := ConcreteCategory.congr_hom
    (integralToCoefficientChainComponent_comm_d K X n)
    ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1)
  have hx := integralToCoefficientChainComponent_iota_one K X (n + 1) x
  simp only [ConcreteCategory.comp_apply] at h ⊢
  rw [hx] at h
  exact h.symm

/-- Extension of coefficients of a chain map between integral simplicial chains.

Source: upstream
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Excision/Field.lean` @ `2ead713`,
`rationalizeSimplicialChainMap`, with ℚ generalized to a coefficient ring `K`. -/
def coefficientizeSimplicialChainMap (X Y : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) :
    CoefficientSimplicialChainComplex K X ⟶ CoefficientSimplicialChainComplex K Y where
  f n := coefficientizeSimplicialChainComponent K X Y n n (f.f n)
  comm' i j hij := by
    simp only [ComplexShape.down_Rel] at hij
    subst i
    rw [← coefficientizeSimplicialChainComponent_d K Y j,
      ← coefficientizeSimplicialChainComponent_comp K, f.comm,
      coefficientizeSimplicialChainComponent_comp K,
      coefficientizeSimplicialChainComponent_d K]

@[simp]
lemma coefficientizeSimplicialChainMap_f (X Y : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)) (n : ℕ) :
    (coefficientizeSimplicialChainMap K X Y f).f n =
      coefficientizeSimplicialChainComponent K X Y n n (f.f n) :=
  rfl

lemma coefficientizeSimplicialChainMap_id (X : SSet.{0}) :
    coefficientizeSimplicialChainMap K X X (𝟙 _) = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun n ↦ coefficientizeSimplicialChainComponent_id K X n

lemma coefficientizeSimplicialChainMap_comp (X Y Z : SSet.{0})
    (f : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ))
    (g : Y.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Z.chainComplex (AddCommGrpCat.of ℤ)) :
    coefficientizeSimplicialChainMap K X Z (f ≫ g) =
      coefficientizeSimplicialChainMap K X Y f ≫
        coefficientizeSimplicialChainMap K Y Z g :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    coefficientizeSimplicialChainComponent_comp K X Y Z n n n (f.f n) (g.f n)

lemma coefficientizeSimplicialChainMap_zero (X Y : SSet.{0}) :
    coefficientizeSimplicialChainMap K X Y 0 = 0 :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    coefficientizeSimplicialChainComponent_zero K X Y n n

/-- Extension of coefficients preserves a chain homotopy between integral simplicial chain maps.

Source: upstream
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Excision/Field.lean` @ `2ead713`,
`rationalizeSimplicialChainHomotopy`, with ℚ generalized to a coefficient ring `K`. -/
def coefficientizeSimplicialChainHomotopy (X Y : SSet.{0})
    {f g : X.chainComplex (AddCommGrpCat.of ℤ) ⟶
      Y.chainComplex (AddCommGrpCat.of ℤ)} (h : Homotopy f g) :
    Homotopy (coefficientizeSimplicialChainMap K X Y f)
      (coefficientizeSimplicialChainMap K X Y g) where
  hom i j := coefficientizeSimplicialChainComponent K X Y i j (h.hom i j)
  zero i j hij := by
    rw [h.zero i j hij, coefficientizeSimplicialChainComponent_zero K]
  comm i := by
    cases i with
    | zero =>
        have hh := congrArg
          (coefficientizeSimplicialChainComponent K X Y 0 0) (h.comm 0)
        rw [Homotopy.dNext_zero_chainComplex,
          Homotopy.prevD_chainComplex] at hh ⊢
        simp only [coefficientizeSimplicialChainComponent_add K,
          coefficientizeSimplicialChainComponent_comp K,
          coefficientizeSimplicialChainComponent_d K, zero_add] at hh
        change coefficientizeSimplicialChainComponent K X Y 0 0 (f.f 0) =
          0 + coefficientizeSimplicialChainComponent K X Y 0 1 (h.hom 0 1) ≫
            (CoefficientSimplicialChainComplex K Y).d 1 0 +
              coefficientizeSimplicialChainComponent K X Y 0 0 (g.f 0)
        simpa only [zero_add] using hh
    | succ n =>
        have hh := congrArg
          (coefficientizeSimplicialChainComponent K X Y (n + 1) (n + 1))
            (h.comm (n + 1))
        rw [Homotopy.dNext_succ_chainComplex,
          Homotopy.prevD_chainComplex] at hh ⊢
        simp only [coefficientizeSimplicialChainComponent_add K,
          coefficientizeSimplicialChainComponent_comp K,
          coefficientizeSimplicialChainComponent_d K] at hh
        exact hh

example (X Y : SSet.{0})
    {f g : X.chainComplex (AddCommGrpCat.of ℤ) ⟶ Y.chainComplex (AddCommGrpCat.of ℤ)}
    (h : Homotopy f g) (i j : ℕ) :
    (coefficientizeSimplicialChainHomotopy K X Y h).hom i j =
      coefficientizeSimplicialChainComponent K X Y i j (h.hom i j) :=
  rfl

/-- Extension of coefficients preserves a chain-homotopy equivalence of simplicial chain complexes.

Source: upstream
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Excision/Field.lean` @ `2ead713`,
`rationalizeSimplicialChainHomotopyEquiv`, with ℚ generalized to a coefficient ring `K`. -/
def coefficientizeSimplicialChainHomotopyEquiv (X Y : SSet.{0})
    (e : HomotopyEquiv (X.chainComplex (AddCommGrpCat.of ℤ))
      (Y.chainComplex (AddCommGrpCat.of ℤ))) :
    HomotopyEquiv (CoefficientSimplicialChainComplex K X)
      (CoefficientSimplicialChainComplex K Y) where
  hom := coefficientizeSimplicialChainMap K X Y e.hom
  inv := coefficientizeSimplicialChainMap K Y X e.inv
  homotopyHomInvId :=
    (Homotopy.ofEq (coefficientizeSimplicialChainMap_comp K X Y X e.hom e.inv).symm).trans
      ((coefficientizeSimplicialChainHomotopy K X X e.homotopyHomInvId).trans
        (Homotopy.ofEq (coefficientizeSimplicialChainMap_id K X)))
  homotopyInvHomId :=
    (Homotopy.ofEq (coefficientizeSimplicialChainMap_comp K Y X Y e.inv e.hom).symm).trans
      ((coefficientizeSimplicialChainHomotopy K Y Y e.homotopyInvHomId).trans
        (Homotopy.ofEq (coefficientizeSimplicialChainMap_id K Y)))

example (X Y : SSet.{0})
    (e : HomotopyEquiv (X.chainComplex (AddCommGrpCat.of ℤ))
      (Y.chainComplex (AddCommGrpCat.of ℤ))) :
    (coefficientizeSimplicialChainHomotopyEquiv K X Y e).hom =
      coefficientizeSimplicialChainMap K X Y e.hom :=
  rfl

/-- Extension of coefficients of an integral chain map induced by a simplicial map is the
corresponding `K`-chain map. -/
lemma coefficientizeSimplicialChainComponent_chainComplexMap
    {X Y : SSet.{0}} (f : X ⟶ Y) (n : ℕ) :
    coefficientizeSimplicialChainComponent K X Y n n
        ((SSet.chainComplexMap f (AddCommGrpCat.of ℤ)).f n) =
      (SSet.chainComplexMap f (ModuleCat.of K K)).f n := by
  refine SSet.chainComplex_hom_ext fun x ↦ ?_
  rw [iota_coefficientizeSimplicialChainComponent K,
    SSet.ι_chainComplexMap_f]
  ext
  change (LinearMap.toSpanSingleton K _ _) 1 = _
  rw [LinearMap.toSpanSingleton_apply_one]
  have hf := ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f X Y f (AddCommGrpCat.of ℤ) x) 1
  have hcoeff := integralToCoefficientChainComponent_iota_one K Y n (f.app _ x)
  simp only [ConcreteCategory.comp_apply] at hf
  rw [hf]
  exact hcoeff

lemma coefficientizeSimplicialChainMap_chainComplexMap
    {X Y : SSet.{0}} (f : X ⟶ Y) :
    coefficientizeSimplicialChainMap K X Y
        (SSet.chainComplexMap f (AddCommGrpCat.of ℤ)) =
      SSet.chainComplexMap f (ModuleCat.of K K) :=
  HomologicalComplex.hom_ext _ _ fun n ↦
    coefficientizeSimplicialChainComponent_chainComplexMap K f n

section CoefficientSmallChains

variable {ι : Type} (X : TopCat.{0}) (U : ι → Set X)

/-- `K`-chains generated by singular simplices subordinate to one member of a cover.

Source: upstream
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Excision/Field.lean` @ `2ead713`,
`CoverSmallRationalSingularChainComplex`, with ℚ generalized to a coefficient ring `K`. -/
abbrev CoverSmallCoefficientSingularChainComplex :
    ChainComplex (ModuleCat K) ℕ :=
  (coverSmallSingularSubcomplex X U : SSet).chainComplex (ModuleCat.of K K)

example :
    CoverSmallCoefficientSingularChainComplex K X U =
      (coverSmallSingularSubcomplex X U : SSet).chainComplex (ModuleCat.of K K) :=
  rfl

/-- Inclusion of cover-small `K`-singular chains into all `K`-singular chains.

Source: upstream
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Excision/Field.lean` @ `2ead713`,
`coverSmallRationalSingularChainInclusion`, with ℚ generalized to a coefficient ring `K`. -/
def coverSmallCoefficientSingularChainInclusion :
    CoverSmallCoefficientSingularChainComplex K X U ⟶
      (TopCat.toSSet.obj X).chainComplex (ModuleCat.of K K) :=
  SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι (ModuleCat.of K K)

example :
    coverSmallCoefficientSingularChainInclusion K X U =
      SSet.chainComplexMap (coverSmallSingularSubcomplex X U).ι (ModuleCat.of K K) :=
  rfl

instance coverSmallCoefficientSingularChainInclusion_mono :
    Mono (coverSmallCoefficientSingularChainInclusion K X U) := by
  dsimp [coverSmallCoefficientSingularChainInclusion, SSet.chainComplexMap,
    SSet.chainComplexFunctor]
  apply +allowSynthFailures Functor.map_mono

/-- The integral subdivision-and-prism homotopy transported to coefficients in `K`: the
all-open-cover small-chain theorem over `K`. -/
theorem coverSmallCoefficientChainApproximation_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomologicalComplex.homotopyEquivalences (ModuleCat K) (ComplexShape.down ℕ)
      (coverSmallCoefficientSingularChainInclusion K X U) := by
  let eZ := coverSmallChainHomotopyEquiv_of_openCover X U hUopen hUcover
  refine ⟨coefficientizeSimplicialChainHomotopyEquiv K
    (coverSmallSingularSubcomplex X U : SSet) (TopCat.toSSet.obj X) eZ, ?_⟩
  change coefficientizeSimplicialChainMap K
      (coverSmallSingularSubcomplex X U : SSet) (TopCat.toSSet.obj X) eZ.hom =
    coverSmallCoefficientSingularChainInclusion K X U
  rw [show eZ.hom = coverSmallIntegralSingularChainInclusion X U from
    coverSmallChainHomotopyEquiv_of_openCover_hom X U hUopen hUcover]
  exact coefficientizeSimplicialChainMap_chainComplexMap K
    (coverSmallSingularSubcomplex X U).ι

/-- A selected `K`-coefficient small-chain homotopy equivalence for an open cover.

Source: upstream
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Excision/Field.lean` @ `2ead713`,
`coverSmallRationalChainHomotopyEquiv_of_openCover`, with ℚ generalized to a coefficient ring
`K`. -/
def coverSmallCoefficientChainHomotopyEquiv_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv (CoverSmallCoefficientSingularChainComplex K X U)
      ((TopCat.toSSet.obj X).chainComplex (ModuleCat.of K K)) :=
  (coverSmallCoefficientChainApproximation_of_openCover K X U hUopen hUcover).choose

lemma coverSmallCoefficientChainHomotopyEquiv_of_openCover_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (coverSmallCoefficientChainHomotopyEquiv_of_openCover K X U hUopen hUcover).hom =
      coverSmallCoefficientSingularChainInclusion K X U :=
  (coverSmallCoefficientChainApproximation_of_openCover K X U hUopen hUcover).choose_spec

example (X : SSet.{0}) (n : ℕ) (x : X _⦋n⦌) :
    (integralToCoefficientChainComponent K X n).hom
        ((X.ιChainComplex (R := AddCommGrpCat.of ℤ) x).hom 1) =
      (X.ιChainComplex (R := ModuleCat.of K K) x).hom 1 :=
  integralToCoefficientChainComponent_iota_one K X n x

example (X : SSet.{0}) (n : ℕ) :
    coefficientizeSimplicialChainComponent K X X n n (𝟙 _) = 𝟙 _ :=
  coefficientizeSimplicialChainComponent_id K X n

example (X : SSet.{0}) :
    coefficientizeSimplicialChainMap K X X (𝟙 _) = 𝟙 _ :=
  coefficientizeSimplicialChainMap_id K X

example (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (coverSmallCoefficientChainHomotopyEquiv_of_openCover K X U hUopen hUcover).hom =
      coverSmallCoefficientSingularChainInclusion K X U :=
  coverSmallCoefficientChainHomotopyEquiv_of_openCover_hom K X U hUopen hUcover

end CoefficientSmallChains

end AlgebraicTopology.Singular
