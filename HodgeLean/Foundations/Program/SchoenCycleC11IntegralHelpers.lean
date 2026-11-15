import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- One localization denominator annihilates a finitely generated localization kernel.
Source: Mathlib, IsLocalization.map_eq_zero_iff and finite generation of an ideal. -/
theorem s2e_c11_fg_localization_kernel_annihilator
    {R S : Type*} [CommRing R] [CommRing S] (M : Submonoid R)
    [Algebra R S] [IsLocalization M S] (hfg : (RingHom.ker (algebraMap R S)).FG) :
    ∃ s : M, ∀ a ∈ RingHom.ker (algebraMap R S), (s : R) * a = 0 := by
  classical
  have hfin : ∀ t : Finset R, (∀ a ∈ t, algebraMap R S a = 0) →
      ∃ s : M, ∀ a ∈ t, (s : R) * a = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact fun _ => ⟨1, by simp⟩
    | @insert a t hat ih =>
      intro h
      obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff M S a).mp (h a (by simp))
      obtain ⟨v, hv⟩ := ih (fun b hb => h b (Finset.mem_insert_of_mem hb))
      refine ⟨u * v, ?_⟩
      intro b hb
      obtain rfl | hb := Finset.mem_insert.mp hb
      · rw [Submonoid.coe_mul, mul_comm (u : R) (v : R), mul_assoc, hu, mul_zero]
      · rw [Submonoid.coe_mul, mul_assoc, hv b hb, mul_zero]
  obtain ⟨t, ht⟩ := hfg
  obtain ⟨s, hs⟩ := hfin t (fun a ha => by
    apply RingHom.mem_ker.mp
    rw [← ht]
    exact Submodule.subset_span ha)
  refine ⟨s, ?_⟩
  intro a ha
  rw [← ht] at ha
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
  · intro b hb
    exact hs b hb
  · simp
  · intro x y _ _ hx hy
    rw [mul_add, hx, hy, add_zero]
  · intro c x _ hx
    change (s : R) * (c * x) = 0
    rw [mul_left_comm, hx, mul_zero]

/-- A domain localization of a noetherian ring extends to a domain principal neighbourhood.
Source: Atiyah–Macdonald, Chapter 3; finite generation of the localization kernel. -/
theorem s2e_c11_domain_principal_neighbourhood
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R]
    [Algebra R S] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime S p] [IsDomain S] :
    ∃ s : R, s ∉ p ∧ IsDomain (Localization.Away s) := by
  obtain ⟨s, hs⟩ := s2e_c11_fg_localization_kernel_annihilator (S := S) p.primeCompl
    (RingHom.ker (algebraMap R S)).fg_of_isNoetherianRing
  let L := Localization.Away (s : R)
  let u : IsUnit (algebraMap R S (s : R)) := IsLocalization.map_units S s
  let φ : L →+* S := IsLocalization.Away.lift (s : R) u
  have hφ : Function.Injective φ := by
    apply (injective_iff_map_eq_zero φ).mpr
    intro z hz
    obtain ⟨⟨a, t⟩, hfrac⟩ := IsLocalization.surj (Submonoid.powers (s : R)) z
    have ha : algebraMap R S a = 0 := by
      have h := congrArg φ hfrac
      rw [map_mul, hz, zero_mul] at h
      change 0 = IsLocalization.Away.lift (s : R) u (algebraMap R L a) at h
      rw [IsLocalization.Away.lift_eq] at h
      exact h.symm
    have hsa : (s : R) * a = 0 := hs a ha
    have hLa : algebraMap R L a = 0 :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (s : R)) L a).mpr
        ⟨⟨s, ⟨1, by simp⟩⟩, hsa⟩
    apply (IsLocalization.map_units L t).mul_left_eq_zero.mp
    exact hfrac.trans hLa
  exact ⟨s, s.2, hφ.isDomain φ⟩

end HodgeLean.Foundations.Program
