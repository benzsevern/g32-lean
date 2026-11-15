module

public import HodgeLean.Foundations.Mathlib.ZmtIsoProofs

/-!
# Proper bijective morphisms and normal targets (FROZEN SPEC)

This specification isolates the implication from finiteness and birationality to an isomorphism,
the characteristic-zero implication from pointwise data to birationality, and normality of schemes
smooth over a field. The proper statement includes surjectivity and trivial residue-field extensions
at closed points. It claims no algebraization theorem for analytic maps and no comparison theorem
between analytic and algebraic spaces. HC no distance; AV milestone no distance.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A finite birational morphism from an integral scheme to an integral normal scheme is an
isomorphism.
Source: Hartshorne, *Algebraic Geometry*, II, Exercise 3.8; Stacks Project, Tag 0AB1. -/
theorem zmtiso_isIso_of_finite_birational_normal
    {Z X : Scheme.{u}} (f : Z ⟶ X) [IsIntegral Z] [IsIntegral X] [IsFinite f]
    (hX : zmtiso_IsNormal X) (hf : zmtiso_IsBirational f) : IsIso f :=
  zmtiso_isIso_of_finite_birational_normal_aux f hX hf

example {Z X : Scheme.{u}} (f : Z ⟶ X) [IsIntegral Z] [IsIntegral X] [IsFinite f]
    (hX : zmtiso_IsNormal X) (hf : zmtiso_IsBirational f) : IsIso f :=
  zmtiso_isIso_of_finite_birational_normal f hX hf

/-- A bijective finite-type morphism of integral schemes over an algebraically closed
characteristic-zero field is birational when its closed-point residue extensions are trivial.
Source: EGA IV, 17.9.1 and 18.10.1; Stacks Project, Tags 02GU and 04DF. -/
theorem zmtiso_birational_of_injective_char0
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {Z X : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    (f : Z ⟶ X) [IsIntegral Z] [IsIntegral X]
    [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX]
    (hover : f ≫ sX = sZ)
    (hinj : ∀ ⦃z₁ z₂ : Z⦄,
      IsClosed ({z₁} : Set Z) → IsClosed ({z₂} : Set Z) →
      f z₁ = f z₂ → z₁ = z₂)
    (hsurj : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ z : Z, IsClosed ({z} : Set Z) ∧ f z = x)
    (hres : ∀ z : Z, IsClosed ({z} : Set Z) → IsIso (f.residueFieldMap z)) :
    zmtiso_IsBirational f :=
  zmtiso_birational_of_injective_char0_aux sZ sX f hover hinj hsurj hres

example {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {Z X : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    (f : Z ⟶ X) [IsIntegral Z] [IsIntegral X]
    [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX]
    (hover : f ≫ sX = sZ)
    (hinj : ∀ ⦃z₁ z₂ : Z⦄,
      IsClosed ({z₁} : Set Z) → IsClosed ({z₂} : Set Z) →
      f z₁ = f z₂ → z₁ = z₂)
    (hsurj : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ z : Z, IsClosed ({z} : Set Z) ∧ f z = x)
    (hres : ∀ z : Z, IsClosed ({z} : Set Z) → IsIso (f.residueFieldMap z)) :
    zmtiso_IsBirational f :=
  zmtiso_birational_of_injective_char0 sZ sX f hover hinj hsurj hres

/-- A scheme smooth over a field is normal.
Source: EGA IV, 17.5.1; Stacks Project, Tags 056S, 00NN, and 031O. -/
theorem zmtiso_normal_of_smooth
    {k : Type u} [Field k] (X : Scheme.{u}) (sX : X ⟶ Spec (.of k)) [Smooth sX] :
    zmtiso_IsNormal X :=
  zmtiso_normal_of_smooth_aux X sX

example {k : Type u} [Field k] (X : Scheme.{u}) (sX : X ⟶ Spec (.of k)) [Smooth sX] :
    zmtiso_IsNormal X := zmtiso_normal_of_smooth X sX

/-- A proper bijective morphism of integral finite-type schemes over an algebraically closed
characteristic-zero field is an isomorphism when the target is normal and closed-point residue
extensions are trivial.
Source: EGA IV, 18.12.13; Hartshorne, *Algebraic Geometry*, II, Exercise 3.8; Stacks Project,
Tags 02LS and 0AB1. -/
theorem zmtiso_isIso_of_proper_injective_normal
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {Z X : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    (f : Z ⟶ X) [IsIntegral Z] [IsIntegral X] [IsProper f]
    [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX]
    (hX : zmtiso_IsNormal X) (hover : f ≫ sX = sZ)
    (hinj : ∀ ⦃z₁ z₂ : Z⦄,
      IsClosed ({z₁} : Set Z) → IsClosed ({z₂} : Set Z) →
      f z₁ = f z₂ → z₁ = z₂)
    (hsurj : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ z : Z, IsClosed ({z} : Set Z) ∧ f z = x)
    (hres : ∀ z : Z, IsClosed ({z} : Set Z) → IsIso (f.residueFieldMap z)) : IsIso f :=
  zmtiso_isIso_of_proper_injective_normal_aux sZ sX f hX hover hinj hsurj hres

example {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {Z X : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    (f : Z ⟶ X) [IsIntegral Z] [IsIntegral X] [IsProper f]
    [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX]
    (hX : zmtiso_IsNormal X) (hover : f ≫ sX = sZ)
    (hinj : ∀ ⦃z₁ z₂ : Z⦄,
      IsClosed ({z₁} : Set Z) → IsClosed ({z₂} : Set Z) →
      f z₁ = f z₂ → z₁ = z₂)
    (hsurj : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ z : Z, IsClosed ({z} : Set Z) ∧ f z = x)
    (hres : ∀ z : Z, IsClosed ({z} : Set Z) → IsIso (f.residueFieldMap z)) : IsIso f :=
  zmtiso_isIso_of_proper_injective_normal sZ sX f hX hover hinj hsurj hres

end AlgebraicGeometry
