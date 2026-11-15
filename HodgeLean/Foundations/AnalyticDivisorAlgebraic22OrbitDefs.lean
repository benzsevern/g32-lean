import HodgeLean.Foundations.AnalyticDivisorAlgebraic22

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic22
open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic21

/-- The orbit relation for the constructed additive period action.
Source: `AddAction.orbitRel`, applied to `gaga22_componentAction`. -/
def gaga22_orbitSetoid {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p) : Setoid (gaga21_GlobalComponent V f) := by
  letI := gaga22_componentAction Λ hD hper
  exact AddAction.orbitRel Λ (gaga21_GlobalComponent V f)

/-- Components of the descended divisor are period orbits, rather than individual branches.
Source: Griffiths--Harris, Chapter 1 §1, descent of divisors. -/
abbrev gaga22_ComponentOrbit {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p) := Quotient (gaga22_orbitSetoid Λ hD hper)

/-- Take the image of a representative carrier in the torus, with its original weight.
Representative independence and finiteness are separate statements.
Source: Griffiths--Harris, Chapter 1 §1, descent of divisors. -/
def gaga22_descendedDivisor {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p) : gaga21_WeightedCarrierFamily ((Fin g → ℂ) ⧸ Λ) where
  Component := gaga22_ComponentOrbit Λ hD hper
  carrier O := (QuotientAddGroup.mk : (Fin g → ℂ) → (Fin g → ℂ) ⧸ Λ) ''
    gaga21_componentCarrier (Quotient.out O)
  multiplicity O := (gaga21_gluedDivisor V f).multiplicity (Quotient.out O)

example {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p) (C : gaga21_GlobalComponent V f) :
    (gaga22_orbitSetoid Λ hD hper).r C C := (gaga22_orbitSetoid Λ hD hper).refl C
example {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p) (C : gaga21_GlobalComponent V f) :
    gaga22_ComponentOrbit Λ hD hper := Quotient.mk _ C
example {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p) : gaga21_WeightedCarrierFamily ((Fin g → ℂ) ⧸ Λ) :=
  gaga22_descendedDivisor Λ hD hper

end HodgeLean.Foundations.AnalyticDivisorAlgebraic22
