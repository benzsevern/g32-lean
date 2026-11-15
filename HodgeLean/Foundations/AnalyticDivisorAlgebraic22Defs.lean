import HodgeLean.Foundations.AnalyticDivisorAlgebraic21
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Translation of certified divisor occurrences

An occurrence is translated by pulling back all its factors and changing only its unit
when choosing a chart at the new anchor. HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic22
open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic21

private theorem gaga22_irreducible_translate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : E → ℂ} {p : E} (l : E) (h : IsIrreducibleAt f p) :
    IsIrreducibleAt (fun z ↦ f (z - l)) (p + l) := by
  refine ⟨by simpa only [add_sub_cancel_right] using h.1, ?_⟩
  intro a b ha hb he
  have ht : Tendsto (fun z : E ↦ z + l) (𝓝 p) (𝓝 (p + l)) :=
    (continuous_id.add continuous_const).tendsto p
  have han : AnalyticAt ℂ (fun z : E ↦ z + l) p := analyticAt_id.add analyticAt_const
  have he' : f =ᶠ[𝓝 p] fun z ↦ a (z + l) * b (z + l) := by
    simpa only [Function.comp_def, add_sub_cancel_right] using he.comp_tendsto ht
  exact h.2 _ _ (ha.comp_of_eq han rfl) (hb.comp_of_eq han rfl) he'

private theorem gaga22_coprime_translate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f g : E → ℂ} {p : E} (l : E) (h : IsCoprimeAt f g p) :
    IsCoprimeAt (fun z ↦ f (z - l)) (fun z ↦ g (z - l)) (p + l) := by
  rintro ⟨a, b, c, ha, hb, hc, hz, he, hf⟩
  have ht : Tendsto (fun z : E ↦ z + l) (𝓝 p) (𝓝 (p + l)) :=
    (continuous_id.add continuous_const).tendsto p
  have han : AnalyticAt ℂ (fun z : E ↦ z + l) p := analyticAt_id.add analyticAt_const
  apply h
  refine ⟨fun z ↦ a (z + l), fun z ↦ b (z + l), fun z ↦ c (z + l),
    ha.comp_of_eq han rfl, hb.comp_of_eq han rfl, hc.comp_of_eq han rfl, hz, ?_, ?_⟩
  · simpa only [Function.comp_def, add_sub_cancel_right] using he.comp_tendsto ht
  · simpa only [Function.comp_def, add_sub_cancel_right] using hf.comp_tendsto ht

/-- Translate every factor, retain every exponent and the selected index, and absorb the
chart transition unit into the translated unit. The choice is only a covering chart and
its association unit, never a component or a factorization.
Source: Griffiths--Harris, Chapter 1 §1, change of local equations of a divisor. -/
def gaga22_translateOccurrence {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) (a : gaga21_LocalFactorOccurrence V f) : gaga21_LocalFactorOccurrence V f := by
  classical
  have hcover : ∃ j, a.point + (l : Fin g → ℂ) ∈ V j := by
    apply mem_iUnion.mp
    rw [hD.2.1]
    exact mem_univ _
  let j := hcover.choose
  have hj : a.point + (l : Fin g → ℂ) ∈ V j := hcover.choose_spec
  have hass := hper (-l) j a.chart (a.point + l) hj (by simpa using a.mem_chart)
  let u := hass.choose
  have hu := hass.choose_spec
  have han : AnalyticAt ℂ (fun z : Fin g → ℂ ↦ z - l) (a.point + l) :=
    analyticAt_id.sub analyticAt_const
  have ht : Tendsto (fun z : Fin g → ℂ ↦ z - l) (𝓝 (a.point + l)) (𝓝 a.point) := by
    simpa only [ContinuousAt, add_sub_cancel_right] using han.continuousAt
  exact {
    chart := j
    point := a.point + l
    mem_chart := hj
    count := a.count
    unit := fun z ↦ u z * a.unit (z - l)
    factors := fun k z ↦ a.factors k (z - l)
    exponents := a.exponents
    selected := a.selected
    unit_analytic := hu.1.mul (a.unit_analytic.comp_of_eq han (add_sub_cancel_right _ _))
    unit_ne := mul_ne_zero hu.2.1 (by simpa only [add_sub_cancel_right] using a.unit_ne)
    factor_data := fun k ↦ ⟨(a.factor_data k).1.comp_of_eq han (add_sub_cancel_right _ _),
      gaga22_irreducible_translate (l : Fin g → ℂ) (a.factor_data k).2.1, (a.factor_data k).2.2⟩
    coprime := fun k m hkm ↦ gaga22_coprime_translate (l : Fin g → ℂ) (a.coprime hkm)
    factorization := by
      filter_upwards [hu.2.2, a.factorization.comp_tendsto ht] with z hz hfz
      change f a.chart (z - l) = _ at hfz
      simpa only [AddSubgroup.coe_neg, ← sub_eq_add_neg, hfz, Function.comp_def, mul_assoc] using hz
    selected_zero := by simpa only [add_sub_cancel_right] using a.selected_zero }

example {g : ℕ} {ι : Type} {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) (a : gaga21_LocalFactorOccurrence V f) :
    (gaga22_translateOccurrence Λ hD hper l a).point = a.point + l := rfl

/-- Translate the chosen representative and take its component class. Independence of the
representative is a separate theorem, not part of this construction.
Source: Chirka, *Complex Analytic Sets*, §5.1 (continuation of branches). -/
def gaga22_translateComponent {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) (C : gaga21_GlobalComponent V f) : gaga21_GlobalComponent V f :=
  Quotient.mk _ (gaga22_translateOccurrence Λ hD hper l (Quotient.out C))

example {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) (C : gaga21_GlobalComponent V f) :
    gaga22_translateComponent Λ hD hper l C =
      Quotient.mk _ (gaga22_translateOccurrence Λ hD hper l (Quotient.out C)) := rfl

end HodgeLean.Foundations.AnalyticDivisorAlgebraic22
