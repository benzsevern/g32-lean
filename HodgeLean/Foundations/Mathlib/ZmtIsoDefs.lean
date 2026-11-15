module

public import Mathlib

/-! # Definitions for finite birational isomorphism specifications -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A scheme is normal when every local ring is an integrally closed domain.
Source: Stacks Project, Tag 033H; Hartshorne, *Algebraic Geometry*, II.3. -/
def zmtiso_IsNormal (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

example (X : Scheme.{u}) : Prop := zmtiso_IsNormal X

/-- A morphism between integral schemes is birational when it takes the generic point to the
generic point and induces an isomorphism on their local rings there.
Source: Stacks Project, Tag 01RN; Hartshorne, *Algebraic Geometry*, I.4. -/
def zmtiso_IsBirational {Z X : Scheme.{u}} [IsIntegral Z] [IsIntegral X]
    (f : Z ⟶ X) : Prop :=
  f (genericPoint Z) = genericPoint X ∧ IsIso (f.stalkMap (genericPoint Z))

example {Z X : Scheme.{u}} [IsIntegral Z] [IsIntegral X] (f : Z ⟶ X) : Prop :=
  zmtiso_IsBirational f

end AlgebraicGeometry
