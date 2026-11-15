import HodgeLean.Foundations.AnalyticDivisorAlgebraic22OrbitProofs

/-! # Finite weighted descent to a compact quotient

Finiteness is an implication from compactness of the quotient, not an input about components.
No discreteness is needed for this set-level finiteness statement.
HC no distance; AV milestone no distance.
-/

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic22
open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic21

/-- Only finitely many carriers meet any compact subset of the cover.
Source: gaga21_component_locallyFinite and compactness via a finite subcover. -/
theorem gaga22_compact_incidence {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (K : Set (Fin g → ℂ)) (hK : IsCompact K) :
    {C : gaga21_GlobalComponent V f | (gaga21_componentCarrier C ∩ K).Nonempty}.Finite :=
  gaga22_compact_incidence_aux Λ hD hper K hK

/-- A compact torus quotient has only finitely many component orbits.
Source: Chirka §5.1; compact fundamental set and gaga22_compact_incidence. -/
theorem gaga22_finite_orbits {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    [CompactSpace ((Fin g → ℂ) ⧸ Λ)] :
    Finite (gaga22_ComponentOrbit Λ hD hper) :=
  gaga22_finite_orbits_aux Λ hD hper

/-- Both carrier image and weight agree at every representative of an orbit.
Source: gaga22_carrier_translate and gaga22_weight_translate. -/
theorem gaga22_descended_representative {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    (C : gaga21_GlobalComponent V f) :
    (gaga22_descendedDivisor Λ hD hper).carrier (Quotient.mk _ C) =
      (QuotientAddGroup.mk : (Fin g → ℂ) → (Fin g → ℂ) ⧸ Λ) '' gaga21_componentCarrier C ∧
    (gaga22_descendedDivisor Λ hD hper).multiplicity (Quotient.mk _ C) =
      (gaga21_gluedDivisor V f).multiplicity C :=
  gaga22_descended_representative_aux Λ hD hper C

/-- The finite orbit family has positive weights and exactly the descended divisor support.
Source: Chirka §5.1; gaga21 carrier nonemptiness and local factorization. -/
theorem gaga22_descended_support {g : ℕ} {ι : Type}
    {V : ι → Set (Fin g → ℂ)} {f : ι → (Fin g → ℂ) → ℂ}
    (Λ : AddSubgroup (Fin g → ℂ)) (hD : IsLocalDivisorData univ V f)
    (hper : ∀ (l : Λ) i j p, p ∈ V i → p + l ∈ V j →
      AreAssociatedAt (f i) (fun z ↦ f j (z + l)) p)
    :
    (∀ O, 0 < (gaga22_descendedDivisor Λ hD hper).multiplicity O) ∧
    (⋃ O, (gaga22_descendedDivisor Λ hD hper).carrier O) =
      (QuotientAddGroup.mk : (Fin g → ℂ) → (Fin g → ℂ) ⧸ Λ) '' localDivisorSupport V f ∧
    Function.Injective (gaga22_descendedDivisor Λ hD hper).carrier :=
  gaga22_descended_support_aux Λ hD hper

end HodgeLean.Foundations.AnalyticDivisorAlgebraic22
