import HodgeLean.Foundations.Curves.CurveDivisorsDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates
import HodgeConjecture.Mathlib.RingTheory.SmoothKrullDimension
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # The function field of a smooth complex curve

The function field `K` of an integral smooth complex curve is a `ℂ`-algebra of transcendence degree
at most one and essentially of finite type. Hence `K` is finite over `ℂ⟮t⟯` for every transcendental
`t`, and every algebraic element of `K` is a constant.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry IntermediateField

attribute [local instance] overSpecAlgebra

namespace HodgeLean.Foundations.Curves

section Algebra

/-- Chains of primes lift along an injective integral extension, so their lengths are bounded by
the dimension of the extension.
Source: Atiyah–Macdonald, Theorem 5.11; Mathlib `Ideal.exists_ltSeries_of_hasGoingUp`. -/
theorem length_le_ringKrullDim_of_isIntegral {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S))
    (l : LTSeries (PrimeSpectrum R)) : (l.length : WithBot ℕ∞) ≤ ringKrullDim S := by
  obtain ⟨Q, -, hQ, hQo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal
    (⊥ : Ideal S) (by
      rw [Ideal.under, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le)
  have : Q.LiesOver l.head.asIdeal := ⟨hQo.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

/-- A Noether normalization of a ring of dimension at most one has at most one variable.
Source: Atiyah–Macdonald, Theorem 5.11 and Chapter 11. -/
theorem le_one_of_noether {S : Type*} [CommRing S] [Algebra ℂ S] (s : ℕ)
    (g : MvPolynomial (Fin s) ℂ →ₐ[ℂ] S) (hinj : Function.Injective g) (hint : g.IsIntegral)
    (hdim : ringKrullDim S ≤ 1) : s ≤ 1 := by
  let := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral (MvPolynomial (Fin s) ℂ) S := ⟨hint⟩
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (MvPolynomial (Fin s) ℂ)
  have hh := MvPolynomial.height_eq_fin_of_isMaximal ℂ s M
  let m : PrimeSpectrum (MvPolynomial (Fin s) ℂ) := ⟨M, hM.isPrime⟩
  rw [show M = m.asIdeal from rfl, PrimeSpectrum.height_eq_orderHeight] at hh
  obtain ⟨l, -, hl⟩ := Order.exists_series_of_le_height m (n := s) hh.ge
  have := length_le_ringKrullDim_of_isIntegral hinj l
  rw [hl] at this
  exact_mod_cast this.trans hdim

/-- The fraction field of a finitely generated complex domain of dimension at most one has
transcendence degree at most one.
Source: Mathlib `exists_integral_inj_algHom_of_fg` (Noether normalization). -/
theorem trdeg_le_one_of_isFractionRing {S L : Type} [CommRing S] [IsDomain S] [Field L]
    [Algebra ℂ S] [Algebra ℂ L] [Algebra S L] [IsScalarTower ℂ S L] [IsFractionRing S L]
    [Algebra.FiniteType ℂ S] (hdim : ringKrullDim S ≤ 1) : Algebra.trdeg ℂ L ≤ 1 := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℂ S
  have hs := le_one_of_noether s g hinj hint hdim
  let R := MvPolynomial (Fin s) ℂ
  let x : Fin s → L := fun i ↦ algebraMap S L (g (MvPolynomial.X i))
  let := g.toRingHom.toAlgebra
  let : Algebra R L := ((algebraMap S L).comp g.toRingHom).toAlgebra
  have : IsScalarTower R S L := .of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsIntegral R S := ⟨hint⟩
  have hRL : Function.Injective (algebraMap R L) :=
    (IsFractionRing.injective S L).comp hinj
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr hRL
  let := FractionRing.liftAlgebra R L
  have := FractionRing.isScalarTower_liftAlgebra R L
  have : Algebra.IsAlgebraic (FractionRing R) L :=
    isAlgebraic_of_isFractionRing R S (FractionRing R) L
  have hx : ∀ p : R, MvPolynomial.aeval x p = algebraMap R L p := by
    intro p
    have : (MvPolynomial.aeval x : R →ₐ[ℂ] L) =
        (IsScalarTower.toAlgHom ℂ S L).comp g := by
      ext i; simp [x]
    rw [this]; rfl
  let f : R →+* Algebra.adjoin ℂ (Set.range x) :=
    (MvPolynomial.aeval x).toRingHom.codRestrict _ fun p ↦ by
      rw [← MvPolynomial.aeval_range]; exact ⟨p, rfl⟩
  have hf : Function.Injective f := fun p q h ↦ hRL (by
    rw [← hx, ← hx]; exact congrArg Subtype.val h)
  have : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range x)) L := ⟨fun y ↦ by
    have hy : IsAlgebraic R y :=
      (IsFractionRing.isAlgebraic_iff R (FractionRing R) L).mpr
        (Algebra.IsAlgebraic.isAlgebraic y)
    exact hy.ringHom_of_comp_eq f (RingHom.id L) hf (RingHom.ext fun p ↦ hx p)⟩
  calc Algebra.trdeg ℂ L ≤ Cardinal.mk (Set.range x) := Algebra.IsAlgebraic.trdeg_le_cardinalMk ℂ _
    _ ≤ Cardinal.mk (Fin s) := Cardinal.mk_range_le
    _ ≤ 1 := by simpa using hs

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- A field of transcendence degree at most one that is essentially of finite type over `ℂ` is
finite over `ℂ⟮t⟯` for every transcendental `t`.
Source: Mathlib `AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite`. -/
theorem finiteDimensional_adjoin_of_transcendental {L : Type} [Field L] [Algebra ℂ L]
    [Algebra.EssFiniteType ℂ L] (htr : Algebra.trdeg ℂ L ≤ 1) (t : L)
    (ht : Transcendental ℂ t) : FiniteDimensional ℂ⟮t⟯ L := by
  have hx : AlgebraicIndependent ℂ (fun _ : Unit ↦ t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have hb : IsTranscendenceBasis ℂ (fun _ : Unit ↦ t) :=
    hx.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htr)
  have halg := hb.isAlgebraic
  rw [Set.range_const] at halg
  have : Algebra.IsAlgebraic ℂ⟮t⟯ L := ⟨fun y ↦
    (halg.isAlgebraic y).extendScalars (FaithfulSMul.algebraMap_injective _ _)⟩
  have : Algebra.EssFiniteType ℂ⟮t⟯ L := .of_comp ℂ _ _
  obtain ⟨s, hs⟩ := (IntermediateField.fg_top (F := ℂ⟮t⟯) (E := L))
  have : FiniteDimensional ℂ⟮t⟯ (IntermediateField.adjoin ℂ⟮t⟯ (s : Set L)) :=
    IntermediateField.finiteDimensional_adjoin fun y _ ↦
      (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  rw [hs] at this
  exact (IntermediateField.topEquiv).toLinearEquiv.finiteDimensional

/-- An algebraic element of a field over `ℂ` is a constant.
Source: Mathlib `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic`. -/
theorem exists_algebraMap_eq_of_isAlgebraic {L : Type*} [Field L] [Algebra ℂ L] {f : L}
    (hf : IsAlgebraic ℂ f) : ∃ c : ℂ, algebraMap ℂ L c = f := by
  have := IntermediateField.isAlgebraic_adjoin_simple hf.isIntegral
  have h := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic ℂ⟮f⟯
  have hf' : f ∈ (⊥ : IntermediateField ℂ L) := h ▸ IntermediateField.mem_adjoin_simple_self ℂ f
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hf'
  exact ⟨c, hc⟩

end Algebra

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left]

/-- The whole space of an integral scheme is a nonempty open. -/
instance nonempty_top_opens : Nonempty (⊤ : X.left.Opens) := ⟨⟨genericPoint X.left, trivial⟩⟩

/-- The function field of a complex scheme as a `ℂ`-algebra, through global sections.
Source: HodgeConjecture `overSpecAlgebra`. -/
@[instance_reducible]
def functionFieldAlgebra : Algebra ℂ X.left.functionField :=
  ((X.left.germToFunctionField ⊤).hom.comp (algebraMap ℂ Γ(X.left, ⊤))).toAlgebra

attribute [local instance] functionFieldAlgebra

variable {X}

/-- Constants in the function field come from every nonempty open. -/
theorem algebraMap_functionField (U : X.left.Opens) [Nonempty U] (c : ℂ) :
    algebraMap ℂ X.left.functionField c =
      X.left.germToFunctionField U (algebraMap ℂ Γ(X.left, U) c) := by
  change X.left.germToFunctionField ⊤ (X.hom.appLE ⊤ ⊤ _ _) =
    X.left.germToFunctionField U (X.hom.appLE ⊤ U _ _)
  rw [← X.hom.appLE_map (U := ⊤) (V := ⊤) (V' := U) (by simp) (homOfLE le_top).op]
  simp only [CommRingCat.comp_apply]
  exact (TopCat.Presheaf.germ_res_apply X.left.presheaf (homOfLE le_top) _ _ _).symm

/-- Sections over a nonempty open form a tower between `ℂ` and the function field. -/
instance (U : X.left.Opens) [Nonempty U] :
    IsScalarTower ℂ Γ(X.left, U) X.left.functionField :=
  .of_algebraMap_eq fun c ↦ algebraMap_functionField U c

variable [SmoothOfRelativeDimension 1 X.hom]

/-- The function field of an integral smooth complex curve has transcendence degree at most one.
Source: Hartshorne, *Algebraic Geometry*, I.1.8A. -/
theorem trdeg_functionField_le_one : Algebra.trdeg ℂ X.left.functionField ≤ 1 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty X.left)
  obtain ⟨U, hU, hPU, hsm⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension (d := 1) X.hom P
  have : Nonempty U := ⟨⟨P, hPU⟩⟩
  have hst := algebraMap_isStandardSmoothOfRelativeDimension X hsm
  have hdim := hst.ringKrullDim_eq_complex
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 ℂ Γ(X.left, U) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hst
  have := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1 (R := ℂ)
    (S := Γ(X.left, U))
  have := functionField_isFractionRing_of_isAffineOpen X.left U hU
  exact trdeg_le_one_of_isFractionRing (hdim.trans (by norm_num)).le

/-- The function field of a smooth complex curve is essentially of finite type over `ℂ`. -/
instance essFiniteType_functionField : Algebra.EssFiniteType ℂ X.left.functionField := by
  obtain ⟨P⟩ := (inferInstance : Nonempty X.left)
  obtain ⟨U, hU, hPU, hsm⟩ :=
    SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension (d := 1) X.hom P
  have : Nonempty U := ⟨⟨P, hPU⟩⟩
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 ℂ Γ(X.left, U) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp
      (algebraMap_isStandardSmoothOfRelativeDimension X hsm)
  have := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1 (R := ℂ)
    (S := Γ(X.left, U))
  have := functionField_isFractionRing_of_isAffineOpen X.left U hU
  have : Algebra.EssFiniteType Γ(X.left, U) X.left.functionField :=
    Algebra.EssFiniteType.of_isLocalization (R := Γ(X.left, U)) (S := X.left.functionField)
      (nonZeroDivisors Γ(X.left, U))
  exact .comp ℂ Γ(X.left, U) _

/-- The function field of a smooth complex curve is finite over `ℂ⟮t⟯` for transcendental `t`.
Source: Hartshorne, *Algebraic Geometry*, I.6. -/
theorem finiteDimensional_functionField (t : X.left.functionField) (ht : Transcendental ℂ t) :
    FiniteDimensional ℂ⟮t⟯ X.left.functionField :=
  finiteDimensional_adjoin_of_transcendental trdeg_functionField_le_one t ht

end HodgeLean.Foundations.Curves
