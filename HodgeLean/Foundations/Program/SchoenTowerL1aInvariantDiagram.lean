import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.Algebra.Ring.Subring.Order

/-! # Invariant section rings on saturated opens

The actual section endomorphisms and invariant subrings for a scheme map with
specified endomorphisms over its target. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The section endomorphism induced on the inverse image of a target open.
Source: Hartshorne, Algebraic Geometry, II.2, restriction of a morphism to invariant opens. -/
def s2v_l1a_saturatedSectionEnd
    {X Y : Scheme} {T : Type*} (f : X ⟶ Y) (a : T → (X ⟶ X))
    (ha : ∀ t, a t ≫ f = f) (U : Y.Opens) (t : T) :
    Γ(X, f ⁻¹ᵁ U) ⟶ Γ(X, f ⁻¹ᵁ U) :=
  (a t).appLE (f ⁻¹ᵁ U) (f ⁻¹ᵁ U) (by rw [← Scheme.Hom.comp_preimage, ha t])

example {X Y : Scheme} {T : Type*} (f : X ⟶ Y) (a : T → (X ⟶ X))
    (ha : ∀ t, a t ≫ f = f) (U : Y.Opens) (t : T) :
    s2v_l1a_saturatedSectionEnd f a ha U t =
      (a t).appLE (f ⁻¹ᵁ U) (f ⁻¹ᵁ U)
        (by rw [← Scheme.Hom.comp_preimage, ha t]) := rfl

/-- The invariant subring of sections on the actual inverse image of a target open.
Source: Stacks Project, tag 04A9, invariant functions on a quotient. -/
def s2v_l1a_fixedSectionSubring
    {X Y : Scheme} {T : Type*} (f : X ⟶ Y) (a : T → (X ⟶ X))
    (ha : ∀ t, a t ≫ f = f) (U : Y.Opens) : Subring Γ(X, f ⁻¹ᵁ U) :=
  ⨅ t : T, (s2v_l1a_saturatedSectionEnd f a ha U t).hom.eqLocus (RingHom.id _)

example {X Y : Scheme} {T : Type*} (f : X ⟶ Y) (a : T → (X ⟶ X))
    (ha : ∀ t, a t ≫ f = f) (U : Y.Opens) :
    s2v_l1a_fixedSectionSubring f a ha U =
      ⨅ t : T, (s2v_l1a_saturatedSectionEnd f a ha U t).hom.eqLocus (RingHom.id _) := rfl

/-- Membership in the invariant section ring is fixedness under every retained section endomorphism.
Source: Stacks Project, tag 04A9, invariant functions on a quotient. -/
theorem s2v_l1a_mem_fixedSectionSubring
    {X Y : Scheme} {T : Type*} (f : X ⟶ Y) (a : T → (X ⟶ X))
    (ha : ∀ t, a t ≫ f = f) (U : Y.Opens) (s : Γ(X, f ⁻¹ᵁ U)) :
    s ∈ s2v_l1a_fixedSectionSubring f a ha U ↔
      ∀ t, (s2v_l1a_saturatedSectionEnd f a ha U t).hom s = s := by
  simp only [s2v_l1a_fixedSectionSubring, Subring.mem_iInf,
    RingHom.mem_eqLocus, RingHom.id_apply]

/-- Section endomorphisms on saturated opens commute with restriction.
Source: Hartshorne, Algebraic Geometry, II.2, naturality of morphisms of structure sheaves. -/
theorem s2v_l1a_saturatedSectionEnd_naturality
    {X Y : Scheme} {T : Type*} (f : X ⟶ Y) (a : T → (X ⟶ X))
    (ha : ∀ t, a t ≫ f = f) (U V : Y.Opens) (h : V ≤ U) (t : T) :
    s2v_l1a_saturatedSectionEnd f a ha U t ≫
        X.presheaf.map (homOfLE (f.preimage_mono h)).op =
      X.presheaf.map (homOfLE (f.preimage_mono h)).op ≫
        s2v_l1a_saturatedSectionEnd f a ha V t := by
  dsimp only [s2v_l1a_saturatedSectionEnd]
  rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

/-- Restriction of regular functions gives the actual ring map between invariant section rings.
Source: Stacks Project, tag 04A9, the subalgebra of invariant functions; Hartshorne, Algebraic Geometry, II.2. -/
def s2v_l1a_fixedSectionRestriction
    {X Y : Scheme} {T : Type*} (f : X ⟶ Y) (a : T → (X ⟶ X))
    (ha : ∀ t, a t ≫ f = f) (U V : Y.Opens) (h : V ≤ U) :
    s2v_l1a_fixedSectionSubring f a ha U →+* s2v_l1a_fixedSectionSubring f a ha V :=
  (X.presheaf.map (homOfLE (f.preimage_mono h)).op).hom.restrict _ _ (by
    intro s hs
    rw [s2v_l1a_mem_fixedSectionSubring] at hs ⊢
    intro t
    have heq := congrArg (fun g : Γ(X, f ⁻¹ᵁ U) ⟶ Γ(X, f ⁻¹ᵁ V) => g.hom s)
      (s2v_l1a_saturatedSectionEnd_naturality f a ha U V h t)
    change (X.presheaf.map (homOfLE (f.preimage_mono h)).op).hom
        ((s2v_l1a_saturatedSectionEnd f a ha U t).hom s) =
      (s2v_l1a_saturatedSectionEnd f a ha V t).hom
        ((X.presheaf.map (homOfLE (f.preimage_mono h)).op).hom s) at heq
    rw [hs t] at heq
    exact heq.symm)

example {X Y : Scheme} {T : Type*} (f : X ⟶ Y) (a : T → (X ⟶ X))
    (ha : ∀ t, a t ≫ f = f) (U V : Y.Opens) (h : V ≤ U)
    (s : s2v_l1a_fixedSectionSubring f a ha U) :
    (s2v_l1a_fixedSectionRestriction f a ha U V h s : Γ(X, f ⁻¹ᵁ V)) =
      (X.presheaf.map (homOfLE (f.preimage_mono h)).op).hom s := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Pullback of base sections lands in the actual invariant section subring.
Source: Stacks Project, tag 04A9, the structure map to invariant functions. -/
def s2v_l1a_baseToFixedSections
    {X Y : Scheme} {T : Type*} (f : X ⟶ Y) (a : T → (X ⟶ X))
    (ha : ∀ t, a t ≫ f = f) (U : Y.Opens) :
    Γ(Y, U) →+* s2v_l1a_fixedSectionSubring f a ha U :=
  (f.app U).hom.codRestrict _ (by
    intro s
    rw [s2v_l1a_mem_fixedSectionSubring]
    intro t
    have heq : f.app U ≫ s2v_l1a_saturatedSectionEnd f a ha U t = f.app U := by
      dsimp only [s2v_l1a_saturatedSectionEnd]
      simpa only [ha t, Scheme.Hom.appLE_eq_app] using
        (Scheme.Hom.appLE_comp_appLE (a t) f U (f ⁻¹ᵁ U) (f ⁻¹ᵁ U) le_rfl
          (by rw [← Scheme.Hom.comp_preimage, ha t]))
    exact congrArg (fun g => g.hom s) heq)

example {X Y : Scheme} {T : Type*} (f : X ⟶ Y) (a : T → (X ⟶ X))
    (ha : ∀ t, a t ≫ f = f) (U : Y.Opens) (s : Γ(Y, U)) :
    (s2v_l1a_baseToFixedSections f a ha U s : Γ(X, f ⁻¹ᵁ U)) = (f.app U).hom s := rfl

end HodgeLean.Foundations.Program
