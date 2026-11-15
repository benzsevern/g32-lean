import HodgeLean.Foundations.AnalyticDivisorAlgebraic22Proofs

/-! # Lattice descent of analytic divisor components

These are implications from local divisor data and association under period translation.
The occurrence construction retains all factors and multiplicities; the quotient action,
carrier translation and weight invariance are separate proof obligations.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic22
open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic21

/-- Translation carries the connected regular germ witnesses to their translates.
Source: Chirka §5.1; invariance of regular support under analytic translations. -/
theorem gaga22_continuation_translate {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) (a b : gaga21_LocalFactorOccurrence V f)
    (hab : gaga21_continuation a b) :
    gaga21_continuation (gaga22_translateOccurrence Λ hD hper l a)
      (gaga22_translateOccurrence Λ hD hper l b) :=
  gaga22_continuation_translate_aux Λ hD hper l a b hab

/-- The component map agrees with translation at every certified representative.
Source: Chirka §5.1; induction on the equivalence closure of continuation. -/
theorem gaga22_translateComponent_mk {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) (a : gaga21_LocalFactorOccurrence V f) :
    gaga22_translateComponent Λ hD hper l (Quotient.mk _ a) =
      Quotient.mk _ (gaga22_translateOccurrence Λ hD hper l a) :=
  gaga22_translateComponent_mk_aux Λ hD hper l a

/-- Translation on global components satisfies the additive action laws.
Source: Griffiths--Harris Ch. 1 §1; association of factors under chart changes. -/
theorem gaga22_translation_laws {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    :
    (∀ C, gaga22_translateComponent Λ hD hper 0 C = C) ∧
    (∀ (l m : Λ) C, gaga22_translateComponent Λ hD hper (l + m) C =
      gaga22_translateComponent Λ hD hper l (gaga22_translateComponent Λ hD hper m C)) :=
  gaga22_translation_laws_aux Λ hD hper

/-- The carrier of the translated component is exactly the translated carrier.
Source: Chirka §5.1; translation and its inverse on certified anchors. -/
theorem gaga22_carrier_translate {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) (C : gaga21_GlobalComponent V f) :
    gaga21_componentCarrier (gaga22_translateComponent Λ hD hper l C) =
      (fun z ↦ z + (l : Fin g → ℂ)) '' gaga21_componentCarrier C :=
  gaga22_carrier_translate_aux Λ hD hper l C

/-- Component weights are invariant under period translation.
Source: Griffiths--Harris Ch. 1 §1; gaga21_glued_multiplicity. -/
theorem gaga22_weight_translate {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (l : Λ) (C : gaga21_GlobalComponent V f) :
    (gaga21_gluedDivisor V f).multiplicity (gaga22_translateComponent Λ hD hper l C) =
      (gaga21_gluedDivisor V f).multiplicity C :=
  gaga22_weight_translate_aux Λ hD hper l C

/-- The period action on global components, obtained from the explicit translation map.
Source: the two identities in `gaga22_translation_laws`. -/
def gaga22_componentAction {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p) : AddAction Λ (gaga21_GlobalComponent V f) where
  vadd := gaga22_translateComponent Λ hD hper
  zero_vadd := (gaga22_translation_laws Λ hD hper).1
  add_vadd := (gaga22_translation_laws Λ hD hper).2

end HodgeLean.Foundations.AnalyticDivisorAlgebraic22
