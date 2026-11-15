import HodgeLean.Foundations.Program.SchoenTowerL1bChartAlgebra
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Polynomial.Monomial

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

namespace HodgeLean.Foundations.Program
open Polynomial

/-- The parameter-invertible part of a binomial chart. -/
abbrev s2v_L1bOverlap {R : Type*} [CommRing R] (u v : R) :=
  Localization.Away (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) X)

example {R : Type*} [CommRing R] (u v : R) :
    s2v_L1bOverlap u v =
      Localization.Away (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) X) := rfl

/-- An invertible solution of the binomial equation gives a unique map from the overlap ring. -/
theorem s2v_l1b_overlap_lift {R A : Type*} [CommRing R] [CommRing A]
    (u v : R) (f : R →+* A) (s : A) (hs : f u = s * f v) (hsunit : IsUnit s) :
    let q := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
    let l := algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v)
    ∃! φ : s2v_L1bOverlap u v →+* A, (φ.comp l).comp q = eval₂RingHom f s := by
  dsimp only
  let q := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
  obtain ⟨g, hg, _⟩ := s2v_l1b_chart_lift u v f s hs
  have hgs : g (q X) = s := by
    have h := DFunLike.congr_fun hg X
    exact h.trans (eval₂_X f s)
  let φ : s2v_L1bOverlap u v →+* A :=
    IsLocalization.Away.lift (q X) (show IsUnit (g (q X)) by rw [hgs]; exact hsunit)
  have hφ : φ.comp (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v)) = g :=
    IsLocalization.Away.lift_comp _ _
  refine ⟨φ, ?_, ?_⟩
  · change (φ.comp (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v))).comp q = _
    rw [hφ, hg]
  · intro ψ hψ
    apply IsLocalization.ringHom_ext (Submonoid.powers (q X))
    apply Ideal.Quotient.ringHom_ext
    rw [hψ, hφ, hg]

/-- Maps from an overlap ring are determined by the base sections and the chart parameter. -/
theorem s2v_l1b_overlap_hom_ext {R A : Type*} [CommRing R] [CommRing A]
    (u v : R) (f g : s2v_L1bOverlap u v →+* A)
    (hC : ∀ a : R,
      f (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v)
        (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) (C a))) =
      g (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v)
        (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) (C a))))
    (hX : f (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v)
        (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) X)) =
      g (algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v)
        (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) X))) : f = g := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) X))
  apply Ideal.Quotient.ringHom_ext
  exact Polynomial.ringHom_ext hC hX

/-- The reciprocal parameter gives a transition map between the two overlap rings. -/
theorem s2v_l1b_overlap_transition {R : Type*} [CommRing R] (u v : R) :
    let q₁ := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
    let q₂ := Ideal.Quotient.mk (Ideal.span {C v - X * C u})
    let l₁ := algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v)
    let l₂ := algebraMap (s2v_L1bChart v u) (s2v_L1bOverlap v u)
    ∃ φ : s2v_L1bOverlap u v →+* s2v_L1bOverlap v u,
      (∀ a, φ (l₁ (q₁ (C a))) = l₂ (q₂ (C a))) ∧
      φ (l₁ (q₁ X)) * l₂ (q₂ X) = 1 := by
  dsimp only
  let q₁ := Ideal.Quotient.mk (Ideal.span {C u - X * C v})
  let q₂ := Ideal.Quotient.mk (Ideal.span {C v - X * C u})
  let l₁ := algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v)
  let l₂ := algebraMap (s2v_L1bChart v u) (s2v_L1bOverlap v u)
  let f : R →+* s2v_L1bOverlap v u := (l₂.comp q₂).comp C
  obtain ⟨w, hw⟩ := IsLocalization.Away.algebraMap_isUnit (q₂ X)
    (S := s2v_L1bOverlap v u)
  have hrel : f v = (w : s2v_L1bOverlap v u) * f u := by
    change l₂ (q₂ (C v)) = (w : s2v_L1bOverlap v u) * l₂ (q₂ (C u))
    rw [hw, ← map_mul]
    exact congrArg l₂ (s2v_l1b_chart_relation v u)
  have hs : f u = (↑w⁻¹ : s2v_L1bOverlap v u) * f v := by
    rw [hrel, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨φ, hφ, _⟩ := s2v_l1b_overlap_lift u v f ↑w⁻¹ hs (Units.isUnit _)
  refine ⟨φ, ?_, ?_⟩
  · intro a
    have h := DFunLike.congr_fun hφ (C a)
    exact h.trans (eval₂_C f _)
  · have h := DFunLike.congr_fun hφ X
    have hX : φ (l₁ (q₁ X)) = ↑w⁻¹ := h.trans (eval₂_X f _)
    change φ (l₁ (q₁ X)) * l₂ (q₂ X) = 1
    rw [hX, ← hw, Units.inv_mul]

/-- Reciprocal transition maps compose to the identity on an overlap ring. -/
theorem s2v_l1b_overlap_transition_inverse {R : Type*} [CommRing R] (u v : R)
    (φ : s2v_L1bOverlap u v →+* s2v_L1bOverlap v u)
    (ψ : s2v_L1bOverlap v u →+* s2v_L1bOverlap u v)
    (hφC : ∀ a, φ (algebraMap _ _
        (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) (C a))) =
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {C v - X * C u}) (C a)))
    (hψC : ∀ a, ψ (algebraMap _ _
        (Ideal.Quotient.mk (Ideal.span {C v - X * C u}) (C a))) =
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) (C a)))
    (hφX : φ (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) X)) *
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {C v - X * C u}) X) = 1)
    (hψX : ψ (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {C v - X * C u}) X)) *
      algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) X) = 1) :
    ψ.comp φ = RingHom.id (s2v_L1bOverlap u v) := by
  apply s2v_l1b_overlap_hom_ext u v
  · intro a
    change ψ (φ _) = _
    rw [hφC, hψC]
    rfl
  · let s₁ := algebraMap (s2v_L1bChart u v) (s2v_L1bOverlap u v)
      (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) X)
    let s₂ := algebraMap (s2v_L1bChart v u) (s2v_L1bOverlap v u)
      (Ideal.Quotient.mk (Ideal.span {C v - X * C u}) X)
    have hunit : IsUnit (ψ s₂) := (IsLocalization.Away.algebraMap_isUnit
      (Ideal.Quotient.mk (Ideal.span {C v - X * C u}) X)).map ψ
    change ψ (φ s₁) = s₁
    apply hunit.mul_right_cancel
    have h := congrArg ψ hφX
    rw [map_mul, map_one] at h
    exact h.trans ((mul_comm _ _).trans hψX).symm

/-- The two parameter-invertible charts are isomorphic over their common coefficient ring. -/
theorem s2v_l1b_overlap_equiv {R : Type*} [CommRing R] (u v : R) :
    ∃ e : s2v_L1bOverlap u v ≃+* s2v_L1bOverlap v u,
      (∀ a, e (algebraMap _ _
        (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) (C a))) =
        algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {C v - X * C u}) (C a))) ∧
      e (algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {C u - X * C v}) X)) *
        algebraMap _ _ (Ideal.Quotient.mk (Ideal.span {C v - X * C u}) X) = 1 := by
  obtain ⟨φ, hφC, hφX⟩ := s2v_l1b_overlap_transition u v
  obtain ⟨ψ, hψC, hψX⟩ := s2v_l1b_overlap_transition v u
  have hleft := s2v_l1b_overlap_transition_inverse u v φ ψ hφC hψC hφX hψX
  have hright := s2v_l1b_overlap_transition_inverse v u ψ φ hψC hφC hψX hφX
  let e : s2v_L1bOverlap u v ≃+* s2v_L1bOverlap v u :=
    { φ with
      invFun := ψ
      left_inv := fun a => DFunLike.congr_fun hleft a
      right_inv := fun a => DFunLike.congr_fun hright a }
  exact ⟨e, hφC, hφX⟩

end HodgeLean.Foundations.Program
