import HodgeLean.Foundations.Program.SchoenCycleInvariantJets
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Tactic.Ring

/-! # Extending stabilizer-invariant infinitesimal classes -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Averaging an orbit-supported representative extends a stabilizer-invariant
class to a full-group invariant element.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1,
finite quotient local invariants and the averaging operator. -/
theorem s2e_orbit_supported_jet_average
    (G A : Type*) [Group G] [Fintype G] [CommRing A] [Algebra ℂ A]
    (a : G →* (A ≃ₐ[ℂ] A)) (H : Subgroup G) (I : Ideal A) (x z : A)
    (hin : ∀ g ∈ H, a g z - x ∈ I)
    (hout : ∀ g ∉ H, a g z ∈ I) :
    ∃ y : A, (∀ g, a g y = y) ∧ y - x ∈ I := by
  classical
  let S : Finset G := Finset.univ.filter (fun g => g ∈ H)
  have hS : S.Nonempty := ⟨1, by simp only [S, Finset.mem_filter, Finset.mem_univ,
    H.one_mem, and_self]⟩
  have hn : (S.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hS)
  let v : A := algebraMap ℂ A ((S.card : ℂ)⁻¹)
  let y : A := v * ∑ g : G, a g z
  have hv : v * (S.card : A) = 1 := by
    dsimp only [v]
    rw [← map_natCast (algebraMap ℂ A), ← map_mul, inv_mul_cancel₀ hn, map_one]
  have hcount : (∑ g : G, if g ∈ H then x else 0) = (S.card : A) * x := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rfl
  refine ⟨y, ?_, ?_⟩
  · intro g
    dsimp only [y, v]
    rw [map_mul, (a g).commutes, map_sum]
    congr 1
    simp only [← AlgEquiv.mul_apply, ← map_mul]
    rw [Function.Bijective.sum_comp (Group.mulLeft_bijective g) (fun h => a h z)]
  · have hsum : (∑ g : G, (a g z - if g ∈ H then x else 0)) ∈ I := by
      apply I.sum_mem
      intro g _
      by_cases hg : g ∈ H
      · simpa only [if_pos hg] using hin g hg
      · simpa only [if_neg hg, sub_zero] using hout g hg
    have he : y - x = v * ∑ g : G, (a g z - if g ∈ H then x else 0) := by
      rw [Finset.sum_sub_distrib, hcount, mul_sub, ← mul_assoc, hv, one_mul]
    rw [he]
    exact I.mul_mem_left v hsum

/-- Comaximal orbit ideals give a section equal to one at the retained ideal and
zero at every translate outside its stabilizer.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1. -/
theorem s2e_orbit_ideal_separator
    (G A : Type*) [Group G] [Fintype G] [CommRing A] [Algebra ℂ A]
    (a : G →* (A ≃ₐ[ℂ] A)) (H : Subgroup G) (I : Ideal A)
    (hcoprime : ∀ g ∉ H, I ⊔ I.comap (a g).toRingHom = ⊤) :
    ∃ e : A, e - 1 ∈ I ∧ ∀ g ∉ H, a g e ∈ I := by
  classical
  let S : Finset G := Finset.univ.filter (fun g => g ∉ H)
  have hv (g : {g : G // g ∈ S}) : ∃ v : A, v - 1 ∈ I ∧ a g.val v ∈ I := by
    have hg : g.val ∉ H := (Finset.mem_filter.mp g.property).2
    have hsum : I + I.comap (a g.val).toRingHom = 1 := by
      rw [Ideal.add_eq_sup, hcoprime g.val hg, Ideal.one_eq_top]
    obtain ⟨u, hu, v, hv, h1⟩ := Ideal.add_eq_one_iff.mp hsum
    refine ⟨v, ?_, hv⟩
    have he : v - 1 = -u := by rw [← h1]; ring
    rw [he]
    exact I.neg_mem hu
  choose v hv1 hv0 using hv
  let e : A := ∏ g : {g : G // g ∈ S}, v g
  refine ⟨e, ?_, ?_⟩
  · have hmk (g : {g : G // g ∈ S}) : Ideal.Quotient.mk I (v g) = 1 := by
      have h := Ideal.Quotient.eq.mpr (hv1 g)
      simpa only [map_one] using h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_one, sub_eq_zero]
    change Ideal.Quotient.mk I (∏ g : {g : G // g ∈ S}, v g) = 1
    rw [map_prod]
    simp only [hmk, Finset.prod_const_one]
  · intro g hg
    let j : {g : G // g ∈ S} := ⟨g, by simp only [S, Finset.mem_filter,
      Finset.mem_univ, hg, not_false_eq_true, and_self]⟩
    have hfac : v j ∣ e := Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    obtain ⟨r, hr⟩ := hfac
    rw [hr, map_mul]
    exact I.mul_mem_right _ (hv0 j)

/-- A stabilizer-invariant infinitesimal class extends to an invariant element
when its other orbit ideals are comaximal with the retained ideal.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1,
local invariants of a finite quotient. -/
theorem s2e_stabilizer_jet_extension
    (G A : Type*) [Group G] [Fintype G] [CommRing A] [Algebra ℂ A]
    (a : G →* (A ≃ₐ[ℂ] A)) (H : Subgroup G) (I : Ideal A) (x : A)
    (hstable : ∀ g ∈ H, ∀ r ∈ I, a g r ∈ I)
    (hx : ∀ g ∈ H, a g x - x ∈ I)
    (hcoprime : ∀ g ∉ H, I ⊔ I.comap (a g).toRingHom = ⊤) :
    ∃ y : A, (∀ g, a g y = y) ∧ y - x ∈ I := by
  obtain ⟨e, he, he0⟩ := s2e_orbit_ideal_separator G A a H I hcoprime
  apply s2e_orbit_supported_jet_average G A a H I x (e * x)
  · intro g hg
    have he1 : a g e - 1 ∈ I := by
      simpa only [map_sub, map_one] using hstable g hg (e - 1) he
    have hmul : a g (e * x) - x =
        a g e * (a g x - x) + (a g e - 1) * x := by
      rw [map_mul]
      ring
    rw [hmul]
    exact I.add_mem (I.mul_mem_left _ (hx g hg)) (I.mul_mem_right _ he1)
  · intro g hg
    rw [map_mul]
    exact I.mul_mem_right _ (he0 g hg)

/-- A jet at a maximal ideal invariant under that ideal's stabilizer extends to
an invariant element, to every finite order.
Source: Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1,
finite quotient local invariants; Atiyah–Macdonald, Proposition 1.10. -/
theorem s2e_maximal_stabilizer_jet_extension
    (G A : Type*) [Group G] [Fintype G] [CommRing A] [Algebra ℂ A]
    (a : G →* (A ≃ₐ[ℂ] A)) (H : Subgroup G) (I : Ideal A) [I.IsMaximal]
    (hstab : ∀ g, I.comap (a g).toRingHom = I ↔ g ∈ H)
    (N : ℕ) (x : A) (hx : ∀ g ∈ H, a g x - x ∈ I ^ N) :
    ∃ y : A, (∀ g, a g y = y) ∧ y - x ∈ I ^ N := by
  have hpow (g : G) : (I ^ N).comap (a g).toRingHom =
      (I.comap (a g).toRingHom) ^ N := by
    apply (Ideal.relIsoOfBijective (a g).toRingHom (a g).bijective).symm.injective
    change ((I ^ N).comap (a g).toRingHom).map (a g).toRingHom =
      ((I.comap (a g).toRingHom) ^ N).map (a g).toRingHom
    rw [Ideal.map_comap_of_surjective (f := (a g).toRingHom) (a g).surjective,
      Ideal.map_pow,
      Ideal.map_comap_of_surjective (f := (a g).toRingHom) (a g).surjective]
  apply s2e_stabilizer_jet_extension G A a H (I ^ N) x ?_ hx ?_
  · intro g hg r hr
    change r ∈ (I ^ N).comap (a g).toRingHom
    rwa [hpow, (hstab g).mpr hg]
  · intro g hg
    rw [hpow]
    apply Ideal.pow_sup_pow_eq_top
    have hm : (I.comap (a g).toRingHom).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective (a g).toRingHom (a g).surjective
    apply Ideal.IsMaximal.coprime_of_ne (inferInstance) hm
    intro he
    exact hg ((hstab g).mp he.symm)

end HodgeLean.Foundations.Program
