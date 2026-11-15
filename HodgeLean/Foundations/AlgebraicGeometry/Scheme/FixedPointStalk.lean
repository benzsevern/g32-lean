import HodgeLean.Foundations.AlgebraicGeometry.Scheme.FixedPointStalkProofs

/-! # Fixed-point stalk and finite jet transport

Implication from explicit point equalities and section representatives.
No field, properness, invertibility, or group order input is required.
Cover evaluation and averaging are outside this interface.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.FixedPointStalk

/-- Germ transport and section pullback use the specified point equality.
Source: Hartshorne, Algebraic Geometry, II.1–2 and II.5. -/
theorem germ_transport (X : Scheme) :
    (∀ (U : X.Opens) (x y : X) (hx : x ∈ U) (hy : y ∈ U) (h : x = y),
      X.presheaf.germ U x hx ≫ (X.presheaf.stalkCongr (.of_eq h)).hom =
        X.presheaf.germ U y hy) ∧
    (∀ (f : X ⟶ X) (p : X) (hp : f p = p) (U : X.Opens)
      (hU : U ≤ f ⁻¹ᵁ U) (hmem : p ∈ U),
      X.presheaf.germ U p hmem ≫
          (X.presheaf.stalkCongr (.of_eq hp)).inv ≫ f.stalkMap p =
        f.appLE U U hU ≫ X.presheaf.germ U p hmem) :=
  germ_transport_aux X

example (X : Scheme) :
    (∀ (U : X.Opens) (x y : X) (hx : x ∈ U) (hy : y ∈ U) (h : x = y),
      X.presheaf.germ U x hx ≫ (X.presheaf.stalkCongr (.of_eq h)).hom =
        X.presheaf.germ U y hy) ∧
    (∀ (f : X ⟶ X) (p : X) (hp : f p = p) (U : X.Opens)
      (hU : U ≤ f ⁻¹ᵁ U) (hmem : p ∈ U),
      X.presheaf.germ U p hmem ≫
          (X.presheaf.stalkCongr (.of_eq hp)).inv ≫ f.stalkMap p =
        f.appLE U U hU ≫ X.presheaf.germ U p hmem) := germ_transport X

/-- Identity and literal contravariant composition at a fixed point.
Source: Hartshorne, Algebraic Geometry, II.1–2 and II.5. -/
theorem pullback_laws (X : Scheme) (p : X) :
    pullback X (𝟙 X) p (by simp) = RingHom.id _ ∧
    (∀ (u v : X ⟶ X) (hu : u p = p) (hv : v p = p),
      pullback X (u ≫ v) p (by change v (u p) = p; rw [hu, hv]) =
        (pullback X u p hu).comp (pullback X v p hv)) :=
  pullback_laws_aux X p

example (X : Scheme) (p : X) :
    pullback X (𝟙 X) p (by simp) = RingHom.id _ ∧
    (∀ (u v : X ⟶ X) (hu : u p = p) (hv : v p = p),
      pullback X (u ≫ v) p (by change v (u p) = p; rw [hu, hv]) =
        (pullback X u p hu).comp (pullback X v p hv)) := pullback_laws X p

/-- Local stalk pullback preserves every maximal-ideal power.
Source: Hartshorne, Algebraic Geometry, II.1–2 and II.5. -/
theorem pullback_power (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p)
    (n : ℕ) (r : X.presheaf.stalk p)
    (hr : r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n) :
    pullback X f p hp r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n :=
  pullback_power_aux X f p hp n r hr

example (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p)
    (n : ℕ) (r : X.presheaf.stalk p)
    (hr : r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n) :
    pullback X f p hp r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n := pullback_power X f p hp n r hr

/-- The induced finite jet maps agree on representatives and commute with projections.
Source: Hartshorne, Algebraic Geometry, II.1–2 and II.5. -/
theorem jet_pullback_naturality (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p) :
    (∀ (n : ℕ) (r : X.presheaf.stalk p),
      jetPullback X f p hp n (Ideal.Quotient.mk _ r) =
        Ideal.Quotient.mk _ (pullback X f p hp r)) ∧
    (∀ (m n : ℕ) (h : m ≤ n),
      (projection X p h).comp (jetPullback X f p hp n) =
        (jetPullback X f p hp m).comp (projection X p h)) :=
  jet_pullback_naturality_aux X f p hp

example (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p) :
    (∀ (n : ℕ) (r : X.presheaf.stalk p),
      jetPullback X f p hp n (Ideal.Quotient.mk _ r) =
        Ideal.Quotient.mk _ (pullback X f p hp r)) ∧
    (∀ (m n : ℕ) (h : m ≤ n),
      (projection X p h).comp (jetPullback X f p hp n) =
        (jetPullback X f p hp m).comp (projection X p h)) := jet_pullback_naturality X f p hp

/-- A representative of an invariant stalk jet is invariant under section pullback to the same order.
Source: Hartshorne, Algebraic Geometry, II.1–2 and II.5. -/
theorem section_jet_invariant (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p)
    (U : X.Opens) (hU : U ≤ f ⁻¹ᵁ U) (hmem : p ∈ U) (n : ℕ)
    (r : X.presheaf.stalk p)
    (hr : pullback X f p hp r - r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n)
    (b : Γ(X, U))
    (hb : (X.presheaf.germ U p hmem).hom b - r ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n) :
    (X.presheaf.germ U p hmem).hom ((f.appLE U U hU).hom b - b) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n :=
  section_jet_invariant_aux X f p hp U hU hmem n r hr b hb

example (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p)
    (U : X.Opens) (hU : U ≤ f ⁻¹ᵁ U) (hmem : p ∈ U) (n : ℕ)
    (r : X.presheaf.stalk p)
    (hr : pullback X f p hp r - r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n)
    (b : Γ(X, U))
    (hb : (X.presheaf.germ U p hmem).hom b - r ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n) :
    (X.presheaf.germ U p hmem).hom ((f.appLE U U hU).hom b - b) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n := section_jet_invariant X f p hp U hU hmem n r hr b hb

end AlgebraicGeometry.Scheme.FixedPointStalk
