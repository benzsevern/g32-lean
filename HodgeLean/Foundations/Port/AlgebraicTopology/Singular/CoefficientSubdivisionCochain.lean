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

public import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.SubdivisionCochain
public import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CoefficientExcision
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Ported from upstream HodgeConjecture
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Sheaf/SubdivisionCochain.lean` @ `2ead713`
(both `section RationalCover` blocks and the two `HereditarilyParacompact` theorems at the end).
Modified: ℚ generalized to a coefficient ring K (names `Rational` → `Coefficient`; results whose
upstream name has no `Rational` carry a `_coeff` suffix); the statements that use
`LinearMap.dualMap_surjective_of_injective` take a field `K`; the `module` header and
public/expose markers dropped. Licensed under Apache-2.0; the upstream licence and notice are in
this directory's `LICENSE` and `NOTICE`. -/

/-!
# Singular cochains with coefficients in `K` subordinate to a cover
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped Simplicial

namespace AlgebraicTopology.Singular

section CoefficientCover

variable (K : Type) [CommRing K] {κ : Type} (Y : TopCat.{0}) (U : κ → Set Y)

/-- Restriction of coefficient singular cochains to chains subordinate to a family of subsets.

Source: upstream
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Sheaf/SubdivisionCochain.lean` @ `2ead713`,
`rationalCochainRestrictionToCoverSmall`, with ℚ generalized to a coefficient ring `K`. -/
def coefficientCochainRestrictionToCoverSmall :
    ((TopCat.toSSet.obj Y).chainComplex
        (ModuleCat.of K K)).linearDualCochainComplex ⟶
      (CoverSmallCoefficientSingularChainComplex K Y U).linearDualCochainComplex :=
  HomologicalComplex.linearDualMap (coverSmallCoefficientSingularChainInclusion K Y U)

example :
    coefficientCochainRestrictionToCoverSmall K Y U =
      HomologicalComplex.linearDualMap (coverSmallCoefficientSingularChainInclusion K Y U) :=
  rfl

/-- The chain map from one member of a family into the cover-small coefficient chains.

Source: upstream
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Sheaf/SubdivisionCochain.lean` @ `2ead713`,
`coverMemberToSmallRationalSingularChains`, with ℚ generalized to a coefficient ring `K`. -/
def coverMemberToSmallCoefficientSingularChains (j : κ) :
    (TopCat.toSSet.obj (TopCat.of (U j))).chainComplex (ModuleCat.of K K) ⟶
      CoverSmallCoefficientSingularChainComplex K Y U :=
  SSet.chainComplexMap (coverMemberToSmallSingularSet Y U j) (ModuleCat.of K K)

example (j : κ) :
    coverMemberToSmallCoefficientSingularChains K Y U j =
      SSet.chainComplexMap (coverMemberToSmallSingularSet Y U j) (ModuleCat.of K K) :=
  rfl

/-- An open cover gives a homotopy equivalence from all coefficient cochains to its cover-small
cochains.

Source: upstream
`HodgeConjecture/Lemmas/AlgebraicTopology/Singular/Sheaf/SubdivisionCochain.lean` @ `2ead713`,
`rationalCochainHomotopyEquivCoverSmall`, with ℚ generalized to a coefficient ring `K`. -/
def coefficientCochainHomotopyEquivCoverSmall
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv
      ((TopCat.toSSet.obj Y).chainComplex
        (ModuleCat.of K K)).linearDualCochainComplex
      (CoverSmallCoefficientSingularChainComplex K Y U).linearDualCochainComplex :=
  HomologicalComplex.linearDualHomotopyEquiv
    (coverSmallCoefficientChainHomotopyEquiv_of_openCover K Y U hUopen hUcover)

@[reassoc]
lemma coverMemberToSmallCoefficientSingularChains_comp_inclusion (j : κ) :
    coverMemberToSmallCoefficientSingularChains K Y U j ≫
        coverSmallCoefficientSingularChainInclusion K Y U =
      SSet.chainComplexMap
        (TopCat.toSSet.map (topologicalSubsetInclusion Y (U j)))
        (ModuleCat.of K K) := by
  have h := congrArg
    (fun f : TopCat.toSSet.obj (TopCat.of (U j)) ⟶ TopCat.toSSet.obj Y ↦
      SSet.chainComplexMap f (ModuleCat.of K K))
    (coverMemberToSmallSingularSet_comp_inclusion Y U j)
  simpa only [coverMemberToSmallCoefficientSingularChains,
    coverSmallCoefficientSingularChainInclusion, SSet.chainComplexMap, Functor.map_comp] using h

set_option backward.isDefEq.respectTransparency false in
/-- Vanishing on every member of a covering sieve implies vanishing on all chains subordinate
to the associated family of open subsets. -/
lemma coefficientCochainRestrictionToCoveringSieve_eq_zero
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of K K)).linearDualCochainComplex.X n)
    (hφ : ∀ I : S.Arrow,
      (singularCochainPresheaf K Y n).map I.f.op
        ((singularCochainComplexIsoTopOpen K Y).hom.f n φ) = 0) :
    (coefficientCochainRestrictionToCoverSmall K Y
      (coveringSieveOpenFamily Y S)).f n φ = 0 := by
  change Module.Dual K
    (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of K K)).X n) at φ
  apply_fun ModuleCat.ofHom
  apply SSet.chainComplex_hom_ext
  intro x
  obtain ⟨I, y, hy⟩ :=
    (mem_coverSmallSingularSubcomplex_iff_exists_preimage Y
      (coveringSieveOpenFamily Y S) x.1).mp x.2
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have hI := congrArg
    (fun ψ : OpenCochains K Y (.op I.Y) n ↦ ψ
      (((TopCat.toSSet.obj (TopCat.of (coveringSieveOpenFamily Y S I))).ιChainComplex
        (R := ModuleCat.of K K) y).hom a))
    (hφ I)
  change φ (ModuleCat.Hom.hom
      (((openSingularChainComplexFunctor K Y).map I.f).f n ≫
        (topOpenSingularChainComplexIso K Y).hom.f n)
      (((TopCat.toSSet.obj (TopCat.of (coveringSieveOpenFamily Y S I))).ιChainComplex
        (R := ModuleCat.of K K) y).hom a)) = 0 at hI
  have hchain := HomologicalComplex.congr_hom
    (openSingularChainToTop_comp_topOpenIso K Y I.f) n
  have hchain' :
      ((openSingularChainComplexFunctor K Y).map I.f).f n ≫
          (topOpenSingularChainComplexIso K Y).hom.f n =
        (SSet.chainComplexMap
          (TopCat.toSSet.map (topologicalSubsetInclusion Y I.Y))
          (ModuleCat.of K K)).f n := by
    simpa only [HomologicalComplex.comp_f] using hchain
  rw [hchain'] at hI
  have hiota := ConcreteCategory.congr_hom
    (SSet.ι_chainComplexMap_f
      (TopCat.toSSet.obj (TopCat.of (coveringSieveOpenFamily Y S I)))
      (TopCat.toSSet.obj Y)
      (TopCat.toSSet.map (topologicalSubsetInclusion Y
        (coveringSieveOpenFamily Y S I)))
      (ModuleCat.of K K) y) a
  have hI' : φ
      (((TopCat.toSSet.obj Y).ιChainComplex
        (R := ModuleCat.of K K)
        ((TopCat.toSSet.map (topologicalSubsetInclusion Y
          (coveringSieveOpenFamily Y S I))).app _ y)).hom a) = 0 := by
    calc
      _ = φ ((SSet.chainComplexMap
          (TopCat.toSSet.map (topologicalSubsetInclusion Y
            (coveringSieveOpenFamily Y S I)))
          (ModuleCat.of K K)).f n
          (((TopCat.toSSet.obj
            (TopCat.of (coveringSieveOpenFamily Y S I))).ιChainComplex
              (R := ModuleCat.of K K) y).hom a)) := congrArg φ hiota.symm
      _ = 0 := hI
  change φ (ModuleCat.Hom.hom
    (((coverSmallSingularSubcomplex Y
      (coveringSieveOpenFamily Y S) : SSet).ιChainComplex
        (R := ModuleCat.of K K) x) ≫
      (coverSmallCoefficientSingularChainInclusion K Y
        (coveringSieveOpenFamily Y S)).f n) a) = 0
  dsimp only [coverSmallCoefficientSingularChainInclusion] at ⊢
  simpa [hy] using hI'
  · intro f g h
    exact congrArg ModuleCat.Hom.hom h

set_option backward.isDefEq.respectTransparency false in
/-- Conversely, vanishing on the cover-small chains associated to a covering sieve implies
vanishing after restriction along every arrow of that sieve. -/
lemma coefficientCochainRestrictionToCoveringSieve_local_zero
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of K K)).linearDualCochainComplex.X n)
    (hφ : (coefficientCochainRestrictionToCoverSmall K Y
      (coveringSieveOpenFamily Y S)).f n φ = 0) :
    ∀ I : S.Arrow,
      (singularCochainPresheaf K Y n).map I.f.op
        ((singularCochainComplexIsoTopOpen K Y).hom.f n φ) = 0 := by
  intro I
  change Module.Dual K
    (((TopCat.toSSet.obj Y).chainComplex (ModuleCat.of K K)).X n) at φ
  apply LinearMap.ext
  intro c
  have hc := LinearMap.congr_fun hφ
    (((coverMemberToSmallCoefficientSingularChains K Y
      (coveringSieveOpenFamily Y S) I).f n).hom c)
  have htop := HomologicalComplex.congr_hom
    (openSingularChainToTop_comp_topOpenIso K Y I.f) n
  have hmember := HomologicalComplex.congr_hom
    (coverMemberToSmallCoefficientSingularChains_comp_inclusion K Y
      (coveringSieveOpenFamily Y S) I) n
  calc
    φ ((topOpenSingularChainComplexIso K Y).hom.f n
        (((openSingularChainComplexFunctor K Y).map I.f).f n c)) =
      φ ((SSet.chainComplexMap
        (TopCat.toSSet.map (topologicalSubsetInclusion Y I.Y))
        (ModuleCat.of K K)).f n c) :=
          congrArg φ (ConcreteCategory.congr_hom htop c)
    _ = φ ((coverSmallCoefficientSingularChainInclusion K Y
          (coveringSieveOpenFamily Y S)).f n
        ((coverMemberToSmallCoefficientSingularChains K Y
          (coveringSieveOpenFamily Y S) I).f n c)) :=
            congrArg φ (ConcreteCategory.congr_hom hmember c).symm
    _ = 0 := hc

lemma coefficientCochainHomotopyEquivCoverSmall_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (coefficientCochainHomotopyEquivCoverSmall K Y U hUopen hUcover).hom =
      coefficientCochainRestrictionToCoverSmall K Y U := by
  dsimp [coefficientCochainHomotopyEquivCoverSmall,
    coefficientCochainRestrictionToCoverSmall]
  change HomologicalComplex.linearDualMap
      (coverSmallCoefficientChainHomotopyEquiv_of_openCover K
        Y U hUopen hUcover).hom = _
  rw [coverSmallCoefficientChainHomotopyEquiv_of_openCover_hom K]

/-- Restriction from all coefficient cochains to cover-small cochains is a quasi-isomorphism for an
open cover. -/
theorem coefficientCochainRestrictionToCoverSmall_quasiIso
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    QuasiIso (coefficientCochainRestrictionToCoverSmall K Y U) := by
  rw [← coefficientCochainHomotopyEquivCoverSmall_hom K Y U hUopen hUcover]
  infer_instance

example (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (coefficientCochainHomotopyEquivCoverSmall K Y U hUopen hUcover).hom =
      coefficientCochainRestrictionToCoverSmall K Y U :=
  coefficientCochainHomotopyEquivCoverSmall_hom K Y U hUopen hUcover

end CoefficientCover

section FieldCover

variable (K : Type) [Field K] {κ : Type} (Y : TopCat.{0}) (U : κ → Set Y)

/-- Restriction to cover-small coefficient chains is surjective in every cochain degree. -/
lemma coefficientCochainRestrictionToCoverSmall_surjective (n : ℕ) :
    Function.Surjective ((coefficientCochainRestrictionToCoverSmall K Y U).f n) := by
  apply LinearMap.dualMap_surjective_of_injective
  rw [← ModuleCat.mono_iff_injective]
  exact Functor.map_mono
    (HomologicalComplex.eval (ModuleCat K) (ComplexShape.down ℕ) n)
    (coverSmallCoefficientSingularChainInclusion K Y U)

/-- Restriction to cover-small coefficient chains is an epimorphism of cochain complexes. -/
instance coefficientCochainRestrictionToCoverSmall_epi :
    Epi (coefficientCochainRestrictionToCoverSmall K Y U) :=
  HomologicalComplex.epi_of_epi_f _ fun n ↦ by
    rw [ModuleCat.epi_iff_surjective]
    exact coefficientCochainRestrictionToCoverSmall_surjective K Y U n

/-- The complex of coefficient cochains vanishing on every chain subordinate to an open cover is
acyclic. -/
theorem coefficientCoverSmallCochainKernel_acyclic
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (kernel (coefficientCochainRestrictionToCoverSmall K Y U)).Acyclic := by
  let := coefficientCochainRestrictionToCoverSmall_quasiIso K Y U hUopen hUcover
  exact HomologicalComplex.kernel_acyclic_of_epi_of_quasiIso
    (coefficientCochainRestrictionToCoverSmall K Y U)

set_option backward.isDefEq.respectTransparency false in
/-- A closed coefficient cochain which vanishes on all cover-small chains has a primitive which
also vanishes on all cover-small chains. -/
theorem exists_coverSmallKernel_primitive_coeff
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) (n : ℕ)
    (φ : ((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of K K)).linearDualCochainComplex.X n)
    (hφsmall : (coefficientCochainRestrictionToCoverSmall K Y U).f n φ = 0)
    (hφclosed : (((TopCat.toSSet.obj Y).chainComplex
      (ModuleCat.of K K)).linearDualCochainComplex.d n (n + 1)) φ = 0) :
    ∃ ψ : ((TopCat.toSSet.obj Y).chainComplex
        (ModuleCat.of K K)).linearDualCochainComplex.X
          ((ComplexShape.up ℕ).prev n),
      (((TopCat.toSSet.obj Y).chainComplex
          (ModuleCat.of K K)).linearDualCochainComplex.sc n).f ψ = φ ∧
        (coefficientCochainRestrictionToCoverSmall K Y U).f
          ((ComplexShape.up ℕ).prev n) ψ = 0 := by
  let F := ((TopCat.toSSet.obj Y).chainComplex
    (ModuleCat.of K K)).linearDualCochainComplex
  let q := coefficientCochainRestrictionToCoverSmall K Y U
  let Kc := kernel q
  let E : (kernel q).X n ≅ ModuleCat.of K (q.f n).hom.ker :=
    asIso (kernelComparison q (HomologicalComplex.eval (ModuleCat K)
      (ComplexShape.up ℕ) n)) ≪≫ ModuleCat.kernelIsoKer (q.f n)
  let z : (kernel q).X n := E.inv ⟨φ, hφsmall⟩
  have hzmap : (kernel.ι q).f n z = φ := by
    let ev := HomologicalComplex.eval (ModuleCat K) (ComplexShape.up ℕ) n
    have hc := ConcreteCategory.congr_hom (kernelComparison_comp_ι q ev) z
    have hk := ModuleCat.kernelIsoKer_hom_ker_subtype_apply
      (q.f n) ((kernelComparison q ev) z)
    have hE : E.hom z = (⟨φ, hφsmall⟩ : (q.f n).hom.ker) := by
      simp [z]
    calc
      (kernel.ι q).f n z = kernel.ι (ev.map q) ((kernelComparison q ev) z) := hc.symm
      _ = ((ModuleCat.kernelIsoKer (q.f n)).hom
          ((kernelComparison q ev) z)).1 := hk.symm
      _ = φ := congrArg Subtype.val hE
  have hzclosed : (Kc.sc n).g z = 0 := by
    change Kc.d n ((ComplexShape.up ℕ).next n) z = 0
    rw [show (ComplexShape.up ℕ).next n = n + 1 by simp]
    apply (ModuleCat.mono_iff_injective ((kernel.ι q).f (n + 1))).mp inferInstance
    rw [map_zero]
    change (Kc.d n (n + 1) ≫ (kernel.ι q).f (n + 1)) z = 0
    rw [← (kernel.ι q).comm n (n + 1)]
    change F.d n (n + 1) ((kernel.ι q).f n z) = 0
    rw [hzmap]
    exact hφclosed
  have hacyclic := coefficientCoverSmallCochainKernel_acyclic K Y U hUopen hUcover
  obtain ⟨p, hp⟩ := (ShortComplex.moduleCat_exact_iff (Kc.sc n)).mp
    (hacyclic n) z hzclosed
  change Kc.d ((ComplexShape.up ℕ).prev n) n p = z at hp
  refine ⟨(kernel.ι q).f ((ComplexShape.up ℕ).prev n) p, ?_, ?_⟩
  · change F.d ((ComplexShape.up ℕ).prev n) n
      ((kernel.ι q).f ((ComplexShape.up ℕ).prev n) p) = φ
    calc
      _ = (kernel.ι q).f n
          (Kc.d ((ComplexShape.up ℕ).prev n) n p) :=
        by
          simpa only [ConcreteCategory.comp_apply, F, Kc] using
            (ConcreteCategory.congr_hom
              ((kernel.ι q).comm ((ComplexShape.up ℕ).prev n) n) p)
      _ = φ := by rw [hp, hzmap]
  · have hcondition := HomologicalComplex.congr_hom (kernel.condition q)
      ((ComplexShape.up ℕ).prev n)
    exact ConcreteCategory.congr_hom hcondition p

set_option backward.isDefEq.respectTransparency false in
/-- A closed cochain on the top open which vanishes along a covering sieve has a primitive that
still vanishes along the same sieve. -/
theorem exists_topOpenLocallyZero_primitive_coeff
    (S : (Opens.grothendieckTopology Y).Cover (⊤ : Opens Y)) (n : ℕ)
    (φ : (TopOpenSingularChainComplex K Y).linearDualCochainComplex.X n)
    (hφlocal : ∀ I : S.Arrow,
      (singularCochainPresheaf K Y n).map I.f.op φ = 0)
    (hφclosed : ((TopOpenSingularChainComplex K Y).linearDualCochainComplex.d
      n (n + 1)) φ = 0) :
    ∃ ψ : (TopOpenSingularChainComplex K Y).linearDualCochainComplex.X
        ((ComplexShape.up ℕ).prev n),
      ((TopOpenSingularChainComplex K Y).linearDualCochainComplex.sc n).f ψ = φ ∧
        ∀ I : S.Arrow,
          (singularCochainPresheaf K Y ((ComplexShape.up ℕ).prev n)).map I.f.op ψ = 0 := by
  let A := (SingularChainComplex K Y).linearDualCochainComplex
  let B := (TopOpenSingularChainComplex K Y).linearDualCochainComplex
  let e := singularCochainComplexIsoTopOpen K Y
  let φ' : A.X n := e.inv.f n φ
  have heφ : e.hom.f n φ' = φ := by
    have hc := ConcreteCategory.congr_hom
      (HomologicalComplex.congr_hom e.inv_hom_id n) φ
    simpa only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply,
      HomologicalComplex.id_f, ConcreteCategory.id_apply, φ'] using hc
  have hlocal' : ∀ I : S.Arrow,
      (singularCochainPresheaf K Y n).map I.f.op (e.hom.f n φ') = 0 := by
    intro I
    rw [heφ]
    exact hφlocal I
  have hsmall : (coefficientCochainRestrictionToCoverSmall K Y
      (coveringSieveOpenFamily Y S)).f n φ' = 0 :=
    coefficientCochainRestrictionToCoveringSieve_eq_zero K Y S n φ' hlocal'
  have hclosed' : A.d n (n + 1) φ' = 0 := by
    change A.d n (n + 1) (e.inv.f n φ) = 0
    have hc := ConcreteCategory.congr_hom (e.inv.comm n (n + 1)) φ
    calc
      _ = e.inv.f (n + 1) (B.d n (n + 1) φ) := by
        simpa only [ConcreteCategory.comp_apply, A, B] using hc
      _ = 0 := by rw [hφclosed, map_zero]
  obtain ⟨ψ, hψ, hψsmall⟩ := exists_coverSmallKernel_primitive_coeff K Y
    (coveringSieveOpenFamily Y S)
    (coveringSieveOpenFamily_isOpen Y S)
    (coveringSieveOpenFamily_iUnion Y S) n φ' hsmall hclosed'
  refine ⟨e.hom.f ((ComplexShape.up ℕ).prev n) ψ, ?_, ?_⟩
  · change B.d ((ComplexShape.up ℕ).prev n) n
      (e.hom.f ((ComplexShape.up ℕ).prev n) ψ) = φ
    have hc := ConcreteCategory.congr_hom
      (e.hom.comm ((ComplexShape.up ℕ).prev n) n) ψ
    calc
      _ = e.hom.f n (A.d ((ComplexShape.up ℕ).prev n) n ψ) := by
        simpa only [ConcreteCategory.comp_apply, A, B] using hc
      _ = e.hom.f n φ' := congrArg (e.hom.f n) hψ
      _ = φ := heφ
  · simpa only [e] using
      (coefficientCochainRestrictionToCoveringSieve_local_zero K
        Y S ((ComplexShape.up ℕ).prev n) ψ hψsmall)

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the map from top-open coefficient cochains to global first-plus cochains is
acyclic. -/
theorem topOpenToGlobalSingularCochainPlusComplex_kernel_acyclic_coeff :
    (kernel (topOpenToGlobalSingularCochainPlusComplex K Y)).Acyclic := by
  let C := globalRawSingularCochainComplex K Y
  let B := topOpenForgottenSingularCochainComplex K Y
  let e := globalRawSingularCochainComplexIso K Y
  let f := topOpenToGlobalSingularCochainPlusComplex K Y
  let Kc := kernel f
  intro n
  rw [Kc.exactAt_iff, ShortComplex.ab_exact_iff]
  intro z hzclosed
  let φ : OpenCochains K Y (.op ⊤) n := (kernel.ι f).f n z
  have hφplus : f.f n φ = 0 := by
    have hcondition := HomologicalComplex.congr_hom (kernel.condition f) n
    exact ConcreteCategory.congr_hom hcondition z
  obtain ⟨S, hφlocal⟩ :=
    (singularCochain_toPlus_eq_zero_iff K Y ⊤ n φ).mp hφplus
  have hφclosed : ((TopOpenSingularChainComplex K Y).linearDualCochainComplex.d
      n (n + 1)) φ = 0 := by
    change Kc.d n ((ComplexShape.up ℕ).next n) z = 0 at hzclosed
    rw [show (ComplexShape.up ℕ).next n = n + 1 by simp] at hzclosed
    apply_fun (kernel.ι f).f (n + 1) at hzclosed
    rw [map_zero] at hzclosed
    have hc := ConcreteCategory.congr_hom ((kernel.ι f).comm n (n + 1)) z
    have hC : C.d n (n + 1) φ = 0 := by
      calc
        _ = (kernel.ι f).f (n + 1) (Kc.d n (n + 1) z) := by
          simpa only [ConcreteCategory.comp_apply, C, Kc] using hc
        _ = 0 := hzclosed
    change B.d n (n + 1) φ = 0
    have hc := ConcreteCategory.congr_hom (e.hom.comm n (n + 1)) φ
    have hc' : B.d n (n + 1) φ = C.d n (n + 1) φ := by
      simp only [ConcreteCategory.comp_apply] at hc
      simpa only [e, B, C,
        globalRawSingularCochainComplexIso_hom_f_apply] using hc
    rw [hc', hC]
  obtain ⟨ψ, hψ, hψlocal⟩ :=
    exists_topOpenLocallyZero_primitive_coeff K Y S n φ hφlocal hφclosed
  have hψplus : f.f ((ComplexShape.up ℕ).prev n) ψ = 0 := by
    change ((Opens.grothendieckTopology Y).toPlus
      (singularCochainPresheaf K Y ((ComplexShape.up ℕ).prev n))).app
        (.op ⊤) ψ = 0
    exact (singularCochain_toPlus_eq_zero_iff K Y ⊤
      ((ComplexShape.up ℕ).prev n) ψ).mpr ⟨S, hψlocal⟩
  let ev := HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℕ)
    ((ComplexShape.up ℕ).prev n)
  let E : Kc.X ((ComplexShape.up ℕ).prev n) ≅
      AddCommGrpCat.of (f.f ((ComplexShape.up ℕ).prev n)).hom.ker :=
    asIso (kernelComparison f ev) ≪≫
      AddCommGrpCat.kernelIsoKer (f.f ((ComplexShape.up ℕ).prev n))
  let p : Kc.X ((ComplexShape.up ℕ).prev n) := E.inv ⟨ψ, hψplus⟩
  have hpmap : (kernel.ι f).f ((ComplexShape.up ℕ).prev n) p = ψ := by
    have hc := ConcreteCategory.congr_hom (kernelComparison_comp_ι f ev) p
    have hk := ConcreteCategory.congr_hom
      (AddCommGrpCat.kernelIsoKer_hom_comp_subtype
        (f.f ((ComplexShape.up ℕ).prev n))) ((kernelComparison f ev) p)
    have hE : E.hom p =
        (⟨ψ, hψplus⟩ : (f.f ((ComplexShape.up ℕ).prev n)).hom.ker) := by
      simp [p]
    calc
      (kernel.ι f).f ((ComplexShape.up ℕ).prev n) p =
          kernel.ι (ev.map f) ((kernelComparison f ev) p) := hc.symm
      _ = ((AddCommGrpCat.kernelIsoKer
          (f.f ((ComplexShape.up ℕ).prev n))).hom
            ((kernelComparison f ev) p)).1 := hk.symm
      _ = ψ := congrArg Subtype.val hE
  refine ⟨p, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective ((kernel.ι f).f n)).mp inferInstance
  have hc := ConcreteCategory.congr_hom
    ((kernel.ι f).comm ((ComplexShape.up ℕ).prev n) n) p
  have hψC : C.d ((ComplexShape.up ℕ).prev n) n ψ = φ := by
    change B.d ((ComplexShape.up ℕ).prev n) n ψ = φ at hψ
    have hc := ConcreteCategory.congr_hom
      (e.hom.comm ((ComplexShape.up ℕ).prev n) n) ψ
    have hc' : B.d ((ComplexShape.up ℕ).prev n) n ψ =
        C.d ((ComplexShape.up ℕ).prev n) n ψ := by
      simp only [ConcreteCategory.comp_apply] at hc
      simpa only [e, B, C,
        globalRawSingularCochainComplexIso_hom_f_apply] using hc
    exact hc'.symm.trans hψ
  calc
    (kernel.ι f).f n (Kc.d ((ComplexShape.up ℕ).prev n) n p) =
        C.d ((ComplexShape.up ℕ).prev n) n
          ((kernel.ι f).f ((ComplexShape.up ℕ).prev n) p) := by
      simpa only [ConcreteCategory.comp_apply, C, Kc] using hc.symm
    _ = C.d ((ComplexShape.up ℕ).prev n) n ψ := by rw [hpmap]
    _ = φ := hψC
    _ = (kernel.ι f).f n z := rfl

/-- The map from top-open coefficient cochains to global first-plus cochains is a
quasi-isomorphism. -/
theorem topOpenToGlobalSingularCochainPlusComplex_quasiIso_coeff :
    QuasiIso (topOpenToGlobalSingularCochainPlusComplex K Y) :=
  HomologicalComplex.quasiIso_of_epi_of_kernel_acyclic
    (topOpenToGlobalSingularCochainPlusComplex K Y)
    (topOpenToGlobalSingularCochainPlusComplex_kernel_acyclic_coeff K Y)

/-- On a paracompact Hausdorff space, ordinary cochains map quasi-isomorphically to global
sections of the double-plus singular-cochain complex. -/
theorem topOpenToGlobalSingularCochainPlusPlusComplex_quasiIso_coeff
    [ParacompactSpace Y] [T2Space Y] :
    QuasiIso (topOpenToGlobalSingularCochainPlusPlusComplex K Y) := by
  change QuasiIso
    (topOpenToGlobalSingularCochainPlusComplex K Y ≫
      globalSingularCochainPlusToPlusPlusComplex K Y)
  let := topOpenToGlobalSingularCochainPlusComplex_quasiIso_coeff K Y
  infer_instance

/-- On a paracompact Hausdorff space, ordinary singular cochains with coefficients in `K` compute
the global section complex of the chosen singular-cochain sheaf resolution. -/
theorem topOpenToGlobalSingularCochainSheafComplex_quasiIso_coeff
    [ParacompactSpace Y] [T2Space Y] :
    QuasiIso (topOpenToGlobalSingularCochainSheafComplex K Y) := by
  change QuasiIso
    (topOpenToGlobalSingularCochainPlusPlusComplex K Y ≫
      (globalSingularCochainPlusPlusComplexIsoSheafComplex K Y).hom)
  let := topOpenToGlobalSingularCochainPlusPlusComplex_quasiIso_coeff K Y
  infer_instance

end FieldCover

end AlgebraicTopology.Singular
