import Mathlib.RingTheory.Regular.RegularSequence
import HodgeLean.Foundations.Program.G32Native.PairedLastBlowupChartIdeals

/-! # Regular equations in the last paired blowup charts

The transverse equations are ordered first. In the first chart the final
pulled-back equation is the product `s*v`; in the second it is `t`.
-/

open RingTheory.Sequence
namespace HodgeLean.Foundations.Program.G32Native

/-- In the first Rees chart, the transverse equations followed by `s*v`
are weakly regular if both coordinates are regular modulo the transverse
equations. This applies in every transverse rank.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8, local equations
of the blowup and regular sequences for a regular immersion. -/
theorem paired_last_first_chart_weaklyRegular
    {A : Type*} [CommRing A] (ts : List A) (s v : A)
    (hts : IsWeaklyRegular A ts)
    (hs : IsSMulRegular (A ⧸ (Ideal.ofList ts • ⊤ : Submodule A A)) s)
    (hv : IsSMulRegular (A ⧸ (Ideal.ofList ts • ⊤ : Submodule A A)) v) :
    IsWeaklyRegular A (ts ++ [s * v]) := by
  apply (isWeaklyRegular_append_iff A ts [s * v]).mpr
  refine ⟨hts, (isWeaklyRegular_singleton_iff _ _).mpr ?_⟩
  intro x y h
  apply hv
  apply hs
  simpa only [mul_smul] using h

/-- Properness of the pulled-back ideal upgrades the first-chart equations
to a regular sequence of the same length as the original equations.
Source: Hartshorne, Algebraic Geometry, II.8, regular sequences. -/
theorem paired_last_first_chart_regular
    {A : Type*} [CommRing A] (ts : List A) (s v : A)
    (hts : IsWeaklyRegular A ts)
    (hs : IsSMulRegular (A ⧸ (Ideal.ofList ts • ⊤ : Submodule A A)) s)
    (hv : IsSMulRegular (A ⧸ (Ideal.ofList ts • ⊤ : Submodule A A)) v)
    (hproper : (⊤ : Submodule A A) ≠ Ideal.ofList (ts ++ [s * v]) • ⊤) :
    IsRegular A (ts ++ [s * v]) :=
  ⟨paired_last_first_chart_weaklyRegular ts s v hts hs hv, hproper⟩

/-- The second Rees chart retains a single regular final coordinate
alongside all transverse equations.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_last_second_chart_regular
    {A : Type*} [CommRing A] (ts : List A) (t : A)
    (hts : IsWeaklyRegular A ts)
    (ht : IsSMulRegular (A ⧸ (Ideal.ofList ts • ⊤ : Submodule A A)) t)
    (hproper : (⊤ : Submodule A A) ≠ Ideal.ofList (ts ++ [t]) • ⊤) :
    IsRegular A (ts ++ [t]) := by
  refine ⟨?_, hproper⟩
  exact (isWeaklyRegular_append_iff A ts [t]).mpr
    ⟨hts, (isWeaklyRegular_singleton_iff _ _).mpr ht⟩

/-- Regularity of the exceptional coordinate on the strict component
supplies the cancellation used in the first-chart union identity.
Source: Hartshorne, Algebraic Geometry, II.7.13. -/
theorem paired_last_union_of_quotient_regular
    {A : Type*} [CommRing A] (K : Ideal A) (s v : A)
    (hs : IsSMulRegular (A ⧸ (K ⊔ Ideal.span {v})) s) :
    (K ⊔ Ideal.span {v}) ⊓ (K ⊔ Ideal.span {s}) =
      K ⊔ Ideal.span {s * v} := by
  apply paired_last_chart_union K s v
  intro x hx
  exact mem_of_isSMulRegular_quotient_of_smul_mem hs hx

#print axioms paired_last_first_chart_weaklyRegular
#print axioms paired_last_first_chart_regular
#print axioms paired_last_second_chart_regular
#print axioms paired_last_union_of_quotient_regular
end HodgeLean.Foundations.Program.G32Native
