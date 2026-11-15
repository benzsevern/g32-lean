import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Regular.Free
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.Quotient

noncomputable section
namespace HodgeLean.Adapters

/-- A finite module over a Noetherian local ring is free when a regular
sequence generating the maximal ideal acts regularly on it. -/
theorem a3b4a_gysin_finite_free_of_regular_parameters
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (xs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular M xs)
    (hspan : Ideal.ofList xs = IsLocalRing.maximalIdeal R) : Module.Free R M := by
  classical
  generalize hlen : xs.length = n
  induction n using Nat.strong_induction_on generalizing R M xs with
  | h n ih =>
    cases xs with
    | nil =>
      have hbot : (⊥ : Ideal R).IsMaximal := by
        have heq : (⊥ : Ideal R) = IsLocalRing.maximalIdeal R := by
          simpa only [Ideal.ofList_nil] using hspan
        rw [heq]
        infer_instance
      letI : Field R := (Ring.isField_iff_maximal_bot.mpr hbot).toField
      infer_instance
    | cons x xs =>
      obtain ⟨hxreg, hxsreg⟩ := (RingTheory.Sequence.isWeaklyRegular_cons_iff' M x xs).mp hreg
      have hx : x ∈ IsLocalRing.maximalIdeal R := by
        rw [← hspan, Ideal.ofList_cons]
        exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton x))
      let I := Ideal.span ({x} : Set R)
      have hIle : I ≤ IsLocalRing.maximalIdeal R := Ideal.span_le.mpr
        (fun y hy => (Set.mem_singleton_iff.mp hy) ▸ hx)
      have hI : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hIle
      letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
      letI : IsLocalRing (R ⧸ I) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      letI : IsNoetherianRing (R ⧸ I) := isNoetherianRing_of_surjective R (R ⧸ I)
        (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      have hmap : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I) =
          IsLocalRing.maximalIdeal (R ⧸ I) :=
        IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
      have hspanq : Ideal.ofList (xs.map (Ideal.Quotient.mk I)) =
          IsLocalRing.maximalIdeal (R ⧸ I) := by
        rw [← hmap, ← hspan, Ideal.ofList_cons, Ideal.map_sup, Ideal.map_ofList]
        have hzero : (Ideal.span ({x} : Set R)).map (Ideal.Quotient.mk I) = ⊥ := by
          exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker])
        rw [hzero, bot_sup_eq]
      have hfin : Module.Finite (R ⧸ I) (QuotSMulTop x M) :=
        Module.Finite.of_restrictScalars_finite R _ _
      letI := hfin
      have hfree : Module.Free (R ⧸ I) (QuotSMulTop x M) :=
        ih xs.length (by simp only [List.length_cons] at hlen; omega)
          (xs.map (Ideal.Quotient.mk I)) hxsreg hspanq (List.length_map _)
      have hpres : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
      letI := hpres
      exact (Module.free_quotSMulTop_iff_free R M
        ((IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).symm ▸ hx) hxreg).mp hfree

end HodgeLean.Adapters
