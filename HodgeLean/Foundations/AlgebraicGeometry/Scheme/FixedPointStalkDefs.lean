import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-! # Transported pullback and finite jets at a fixed scheme point

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.FixedPointStalk

/-- Pullback transported along the specified equality of points.
Source: Hartshorne, Algebraic Geometry, II.1–2. -/
def pullback (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p) :
    X.presheaf.stalk p →+* X.presheaf.stalk p :=
  ((X.presheaf.stalkCongr (.of_eq hp)).inv ≫ f.stalkMap p).hom

example (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p) :
    pullback X f p hp =
      ((X.presheaf.stalkCongr (.of_eq hp)).inv ≫ f.stalkMap p).hom := rfl

/-- The existing maximal-ideal power quotient, with order zero included.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5. -/
abbrev Jet (X : Scheme) (p : X) (n : ℕ) :=
  X.presheaf.stalk p ⧸ IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n

example (X : Scheme) (p : X) (n : ℕ) :
    Jet X p n = (X.presheaf.stalk p ⧸
      IsLocalRing.maximalIdeal (X.presheaf.stalk p) ^ n) := rfl

/-- The quotient ring map induced by the actual local stalk map.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5. -/
def jetPullback (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p) (n : ℕ) :
    Jet X p n →+* Jet X p n :=
  Ideal.quotientMap _ (pullback X f p hp) (by
    letI : IsLocalHom (X.presheaf.stalkCongr (.of_eq hp)).inv.hom :=
      isLocalHom_of_iso (X.presheaf.stalkCongr (.of_eq hp)).symm
    letI : IsLocalHom (pullback X f p hp) := inferInstanceAs
      (IsLocalHom ((X.presheaf.stalkCongr (.of_eq hp)).inv ≫ f.stalkMap p).hom)
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le (pullback X f p hp)) n)

example (X : Scheme) (f : X ⟶ X) (p : X) (hp : f p = p) (n : ℕ)
    (r : X.presheaf.stalk p) :
    jetPullback X f p hp n (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (pullback X f p hp r) := rfl

/-- Projection from a higher order jet to a lower order jet.
Source: Hartshorne, Algebraic Geometry, II.2 and II.5. -/
def projection (X : Scheme) (p : X) {m n : ℕ} (h : m ≤ n) :
    Jet X p n →+* Jet X p m :=
  Ideal.Quotient.factorPow _ h

example (X : Scheme) (p : X) {m n : ℕ} (h : m ≤ n) (r : X.presheaf.stalk p) :
    projection X p h (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r := rfl
end AlgebraicGeometry.Scheme.FixedPointStalk
