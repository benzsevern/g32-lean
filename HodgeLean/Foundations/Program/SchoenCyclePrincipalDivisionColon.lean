import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Localization.Ideal

/-! # Local principal division and invariant denominator ideals -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Principal divisibility after localization makes its denominator ideal the unit ideal after that same localization.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 3. -/
theorem s2e_localized_principal_division_colon_top
    {A T : Type*} [CommRing A] [CommRing T] [Algebra A T]
    (M : Submonoid A) [IsLocalization M T] (c s : A)
    (hd : algebraMap A T c ∣ algebraMap A T s) :
    Ideal.map (algebraMap A T) ((Ideal.span {c}).colon ({s} : Set A)) = ⊤ := by
  have hm : algebraMap A T s ∈ (Ideal.span {c}).map (algebraMap A T) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact Ideal.mem_span_singleton.mpr hd
  obtain ⟨m, hmM, hms⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M T (Ideal.span {c}) s).mp hm
  have hmK : m ∈ (Ideal.span {c}).colon ({s} : Set A) := by
    exact Submodule.mem_colon_singleton.mpr hms
  exact Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem (algebraMap A T) hmK)
    (IsLocalization.map_units T (⟨m, hmM⟩ : M))

/-- The denominator ideal for division of two invariant elements is stable under the same group action.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, Chapter 1, §1. -/
theorem s2e_invariant_principal_division_colon_stable
    {A G : Type*} [CommRing A] [Algebra ℂ A] [Group G]
    (a : G →* (A ≃ₐ[ℂ] A)) (c s : A)
    (hc : ∀ g, a g c = c) (hs : ∀ g, a g s = s)
    (g : G) (z : A) (hz : z ∈ (Ideal.span {c}).colon ({s} : Set A)) :
    a g z ∈ (Ideal.span {c}).colon ({s} : Set A) := by
  apply Submodule.mem_colon_singleton.mpr
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp (Submodule.mem_colon_singleton.mp hz)
  apply Ideal.mem_span_singleton.mpr
  refine ⟨a g w, ?_⟩
  have h := congrArg (a g) hw
  simpa only [smul_eq_mul, map_mul, hc g, hs g] using h

end HodgeLean.Foundations.Program
