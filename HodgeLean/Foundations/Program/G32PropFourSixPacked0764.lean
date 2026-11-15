import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow22
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0186
import HodgeLean.Foundations.Program.G32PropFourSixPacked0761
import HodgeLean.Foundations.Program.G32PropFourSixPacked0762
import HodgeLean.Foundations.Program.G32PropFourSixPacked0763
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixCharacters

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row22_squareBlock34 : ∀ r : Fin 16,
    HurwitzPrymRex_mmul
      (g32p_row22_groupNodes (g32p_finBlockIndex 576 34 r))
      (g32p_row22_groupNodes (g32p_finBlockIndex 576 34 r)) = HurwitzPrymRex_mone →
    g32p_row22_characterValues (g32p_finBlockIndex 576 34 r) = 1 := by
  decide +kernel

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row22_squareBlock35 : ∀ r : Fin 16,
    HurwitzPrymRex_mmul
      (g32p_row22_groupNodes (g32p_finBlockIndex 576 35 r))
      (g32p_row22_groupNodes (g32p_finBlockIndex 576 35 r)) = HurwitzPrymRex_mone →
    g32p_row22_characterValues (g32p_finBlockIndex 576 35 r) = 1 := by
  decide +kernel

end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 200000

theorem g32p_exps_of_coprime_order {G : Type*} [Group G] [Finite G]
    {m p : ℕ} [NeZero m] (H : Subgroup G)
    (χ : H →* Multiplicative (ZMod m)) (g : G) (hg : g ^ p = 1)
    (hcop : Nat.Coprime p m) : papersExps H χ g = 0 := by
  have hχ (h : H) (hh : h ^ p = 1) : χ h = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    have hp : orderOf (χ h) ∣ p := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hh, map_one])
    have hm : orderOf (χ h) ∣ m := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] using
        orderOf_dvd_natCard (χ h)
    simpa only [hcop.gcd_eq_one] using Nat.dvd_gcd hp hm
  have hlocal (q : Quotient (orbitRel (Subgroup.zpowers g) (G ⧸ H))) :
      χ (papersLocalMonodromy H g q) = 1 := by
    apply hχ
    apply Subtype.ext
    change (q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out) ^ p = 1
    have hc := conj_pow (a := q.out.out⁻¹)
      (b := g ^ Function.minimalPeriod (g • ·) q.out) (i := p)
    rw [inv_inv] at hc
    rw [hc, ← pow_mul, Nat.mul_comm, pow_mul, hg, one_pow, mul_one, inv_mul_cancel]
  simp only [papersExps, hlocal, toAdd_one, Multiset.map_const', Multiset.filter_eq_nil]
  intro a ha
  have ha0 : a = 0 := (Multiset.mem_replicate.mp ha).2
  exact not_ne_iff.mpr ha0

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 200000

theorem g32p_exps_of_power_kernel {G : Type*} [Group G] [Finite G]
    {m p : ℕ} (H : Subgroup G) (χ : H →* Multiplicative (ZMod m))
    (g : G) (hg : g ^ p = 1) (hχ : ∀ h : H, h ^ p = 1 → χ h = 1) :
    papersExps H χ g = 0 := by
  have hlocal (q : Quotient (orbitRel (Subgroup.zpowers g) (G ⧸ H))) :
      χ (papersLocalMonodromy H g q) = 1 := by
    apply hχ
    apply Subtype.ext
    change (q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out) ^ p = 1
    have hc := conj_pow (a := q.out.out⁻¹)
      (b := g ^ Function.minimalPeriod (g • ·) q.out) (i := p)
    rw [inv_inv] at hc
    rw [hc, ← pow_mul, Nat.mul_comm, pow_mul, hg, one_pow, mul_one, inv_mul_cancel]
  simp only [papersExps, hlocal, toAdd_one, Multiset.map_const', Multiset.filter_eq_nil]
  intro a ha
  have ha0 : a = 0 := (Multiset.mem_replicate.mp ha).2
  exact not_ne_iff.mpr ha0

theorem g32p_supplier_square_kernel (S : g32p_Supplier) {n : ℕ}
    (e : Fin n ≃ S.H) (nodes : Fin n → HurwitzPrymRex_Mat)
    (values : Fin n → Multiplicative (ZMod S.m))
    (hvalues : ∀ i, S.χ (e i) = values i)
    (hmap : ∀ i, b4b_toMatrix (e i : g32p_G) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (nodes i)))
    (hcheck : ∀ i, HurwitzPrymRex_mmul (nodes i) (nodes i) = HurwitzPrymRex_mone →
      values i = 1) : ∀ h : S.H, h ^ 2 = 1 → S.χ h = 1 := by
  intro h hh
  let i := e.symm h
  have he : e i = h := e.apply_symm_apply h
  have hp : (e i : g32p_G) ^ 2 = 1 := by
    have hh' : e i ^ 2 = 1 := by rw [he, hh]
    exact congrArg (fun x : S.H => (x : g32p_G)) hh'
  rw [← he, hvalues]
  apply hcheck
  apply HurwitzPrymRex_evM_injective g32h_omega_sq_add
  apply HurwitzPrymRex_g32conj_injective
  rw [HurwitzPrymRex_evM_mmul g32h_omega_sq_add, map_mul]
  simp only [← hmap]
  rw [← pow_two, ← map_pow, hp, map_one, HurwitzPrymRex_evM_mone, map_one]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_row22_traces : Fin 576 → HurwitzPrymRex_Zw :=
  ![⟨4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, -4⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 4⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨4, 4⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-4, -4⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨-2, -2⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨2, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]

theorem g32p_row22_traceCertificate (i : Fin 576) :
    (⟨∑ j : Fin 4, (g32p_row22_groupNodes i j j).re,
      ∑ j : Fin 4, (g32p_row22_groupNodes i j j).om⟩ : HurwitzPrymRex_Zw) =
      g32p_row22_traces i := by
  revert i
  decide +kernel

theorem g32p_row22_character (i : Fin 576) :
    g32p_rho.character (g32p_row22_groupEquiv i : g32p_G) =
      HurwitzPrymRex_ev g32h_omega (g32p_row22_traces i) := by
  rw [g32p_rho_character, g32p_row22_groupEquiv_map, g32p_archive_trace,
    g32p_integral_trace, g32p_row22_traceCertificate]

theorem g32p_row22_trace_avoid : ∀ i : Fin 576, ∀ j : Fin 12,
    g32p_row22_traces i ≠ g32p_branchTrace ⟨j.val, by omega⟩ := by
  decide +kernel

theorem g32p_row22_squareCheck : ∀ i : Fin 576,
    HurwitzPrymRex_mmul (g32p_row22_groupNodes i) (g32p_row22_groupNodes i) =
      HurwitzPrymRex_mone → g32p_row22_characterValues i = 1 := by
  apply g32p_forall_fin_blocks
  intro q
  fin_cases q
  · exact g32p_row22_squareBlock00
  · exact g32p_row22_squareBlock01
  · exact g32p_row22_squareBlock02
  · exact g32p_row22_squareBlock03
  · exact g32p_row22_squareBlock04
  · exact g32p_row22_squareBlock05
  · exact g32p_row22_squareBlock06
  · exact g32p_row22_squareBlock07
  · exact g32p_row22_squareBlock08
  · exact g32p_row22_squareBlock09
  · exact g32p_row22_squareBlock10
  · exact g32p_row22_squareBlock11
  · exact g32p_row22_squareBlock12
  · exact g32p_row22_squareBlock13
  · exact g32p_row22_squareBlock14
  · exact g32p_row22_squareBlock15
  · exact g32p_row22_squareBlock16
  · exact g32p_row22_squareBlock17
  · exact g32p_row22_squareBlock18
  · exact g32p_row22_squareBlock19
  · exact g32p_row22_squareBlock20
  · exact g32p_row22_squareBlock21
  · exact g32p_row22_squareBlock22
  · exact g32p_row22_squareBlock23
  · exact g32p_row22_squareBlock24
  · exact g32p_row22_squareBlock25
  · exact g32p_row22_squareBlock26
  · exact g32p_row22_squareBlock27
  · exact g32p_row22_squareBlock28
  · exact g32p_row22_squareBlock29
  · exact g32p_row22_squareBlock30
  · exact g32p_row22_squareBlock31
  · exact g32p_row22_squareBlock32
  · exact g32p_row22_squareBlock33
  · exact g32p_row22_squareBlock34
  · exact g32p_row22_squareBlock35

theorem g32p_row22_squareKernel : ∀ h : g32p_row22_finiteSupplier.H,
    h ^ 2 = 1 → g32p_row22_finiteSupplier.χ h = 1 :=
  g32p_supplier_square_kernel g32p_row22_finiteSupplier
    g32p_row22_groupEquiv g32p_row22_groupNodes g32p_row22_characterValues
    g32p_row22_finiteSupplier_value g32p_row22_groupEquiv_map g32p_row22_squareCheck

theorem g32p_row22_branch_exps (j : Fin 13) :
    papersExps g32p_row22_finiteSupplier.H g32p_row22_finiteSupplier.χ
      (g32p_classDatum j) = 0 := by
  by_cases hj : j.val < 12
  · apply g32p_exps_of_character_avoid (p := 3) (by decide) _ _ _
      (by simpa only [if_pos hj] using g32p_branch_power j) g32p_rho
    intro h he
    let i := g32p_row22_groupEquiv.symm h
    have hi : g32p_row22_groupEquiv i = h := g32p_row22_groupEquiv.apply_symm_apply h
    rw [← hi, g32p_row22_character, g32p_branch_character] at he
    exact g32p_row22_trace_avoid i ⟨j.val, hj⟩
      (HurwitzPrymRex_ev_injective g32h_omega_sq_add he)
  · have he : j = 12 := Fin.ext (by omega)
    subst j
    exact g32p_exps_of_power_kernel _ _ _ (g32p_branch_power 12) g32p_row22_squareKernel

theorem g32p_row22_exponents : g32p_exponents g32p_row22_finiteSupplier = [] := by
  have hs : papersExpsTuple g32p_row22_finiteSupplier.H
      g32p_row22_finiteSupplier.χ g32p_classList = 0 := by
    unfold papersExpsTuple g32p_classList
    rw [List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_eq_zero (fun j _ => g32p_row22_branch_exps j)
  change ((papersExpsTuple _ _ _).map ZMod.val).toList = []
  rw [hs, Multiset.map_zero, Multiset.toList_zero]

theorem g32p_row22_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 22 ∧ r.m = g32p_row22_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row22_finiteSupplier.H ∧
      (g32p_exponents g32p_row22_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨22, (-1), 576, 6, 871, 0, 1740, none, [], .U⟩,
    ?_, rfl, rfl, g32p_row22_finiteSupplier_order.symm, ?_⟩
  · decide
  · rw [g32p_row22_exponents]
    exact List.Perm.refl _


def g32p_row22_complexWitness : g32p_row22_finiteSupplier.H →* ℂˣ :=
  g32p_complexCharacter g32p_row22_finiteSupplier

theorem g32p_row22_supplierWitness :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 22 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) := by
  exact ⟨g32p_row22_finiteSupplier, g32p_row22_complexWitness,
    g32p_complexCharacter_apply _, g32p_row22_finiteSupplier_table⟩

end HodgeLean.Foundations.Program

end
end
