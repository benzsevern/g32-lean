import Mathlib.Topology.Homotopy.Basic

/-! Actual cutoff extensions of local deformations. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- Run the local deformation for the specified cutoff time and use the identity elsewhere. -/
def persistenceCutoffDeformation
    {X : Type*} [TopologicalSpace X] (U : Set X) (β : C(X, unitInterval))
    (H : C(unitInterval × U, X)) : unitInterval × X → X := by
  classical
  exact fun p => if hx : p.2 ∈ U then H (p.1 * β p.2, ⟨p.2, hx⟩) else p.2

lemma persistence_cutoff_deformation_of_zero
    {X : Type*} [TopologicalSpace X] (U : Set X) (β : C(X, unitInterval))
    (H : C(unitInterval × U, X)) (hzero : ∀ u : U, H (0, u) = u.val)
    (t : unitInterval) (x : X) (hx : β x = 0) :
    persistenceCutoffDeformation U β H (t, x) = x := by
  by_cases hU : x ∈ U
  · simp only [persistenceCutoffDeformation, dif_pos hU, hx, mul_zero, hzero]
  · simp only [persistenceCutoffDeformation, dif_neg hU]

lemma persistence_cutoff_deformation_continuous
    {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (β : C(X, unitInterval)) (H : C(unitInterval × U, X))
    (hzero : ∀ u : U, H (0, u) = u.val)
    (S : Set X) (hS : IsClosed S) (hSU : S ⊆ U)
    (hβ : ∀ x, x ∉ S → β x = 0) :
    Continuous (persistenceCutoffDeformation U β H) := by
  let P : Set (unitInterval × X) := Prod.snd ⁻¹' U
  let Q : Set (unitInterval × X) := Prod.snd ⁻¹' Sᶜ
  have hP : ContinuousOn (persistenceCutoffDeformation U β H) P := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have htime : Continuous (fun p : P => p.val.1 * β p.val.2) := by
      apply Continuous.subtype_mk
      exact (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).mul
        (continuous_subtype_val.comp (β.continuous.comp
          (continuous_snd.comp continuous_subtype_val)))
    have hc : Continuous (fun p : P =>
        (p.val.1 * β p.val.2, (⟨p.val.2, p.property⟩ : U))) :=
      htime.prodMk ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
    convert H.continuous.comp hc using 1
    funext p
    exact dif_pos p.property
  have hQ : ContinuousOn (persistenceCutoffDeformation U β H) Q := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : (fun p : Q => persistenceCutoffDeformation U β H p.val) =
        (fun p : Q => p.val.2) := by
      funext p
      exact persistence_cutoff_deformation_of_zero U β H hzero p.val.1 p.val.2
        (hβ p.val.2 p.property)
    change Continuous (fun p : Q => persistenceCutoffDeformation U β H p.val)
    rw [heq]
    exact continuous_snd.comp continuous_subtype_val
  have hcover : P ∪ Q = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    by_cases hp : p.2 ∈ U
    · exact Or.inl hp
    · exact Or.inr (fun hs => hp (hSU hs))
  have h := hP.union_of_isOpen hQ (hU.preimage continuous_snd)
    (hS.isOpen_compl.preimage continuous_snd)
  rw [hcover] at h
  exact continuousOn_univ.mp h

lemma persistence_cutoff_deformation_zero_time
    {X : Type*} [TopologicalSpace X] (U : Set X) (β : C(X, unitInterval))
    (H : C(unitInterval × U, X)) (hzero : ∀ u : U, H (0, u) = u.val) (x : X) :
    persistenceCutoffDeformation U β H (0, x) = x := by
  by_cases hx : x ∈ U
  · simp only [persistenceCutoffDeformation, dif_pos hx, zero_mul, hzero]
  · simp only [persistenceCutoffDeformation, dif_neg hx]

lemma persistence_cutoff_deformation_fixed
    {X : Type*} [TopologicalSpace X] (U A : Set X) (β : C(X, unitInterval))
    (H : C(unitInterval × U, X))
    (hfixed : ∀ (t : unitInterval) (u : U), u.val ∈ A → H (t, u) = u.val)
    (t : unitInterval) (x : X) (hx : x ∈ A) :
    persistenceCutoffDeformation U β H (t, x) = x := by
  classical
  by_cases hu : x ∈ U
  · change (if h : x ∈ U then H (t * β x, ⟨x, h⟩) else x) = x
    rw [dif_pos hu]
    exact hfixed (t * β x) ⟨x, hu⟩ hx
  · simp only [persistenceCutoffDeformation, dif_neg hu]

lemma persistence_cutoff_deformation_full_time
    {X : Type*} [TopologicalSpace X] (U : Set X) (β : C(X, unitInterval))
    (H : C(unitInterval × U, X)) (x : X) (hx : x ∈ U) (hβ : β x = 1) :
    persistenceCutoffDeformation U β H (1, x) = H (1, ⟨x, hx⟩) := by
  simp only [persistenceCutoffDeformation, dif_pos hx, hβ, one_mul]

end HodgeLean.Foundations.QuotientDuality
