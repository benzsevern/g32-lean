import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness13BranchVanish
import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness13CosetOrbits
import HodgeLean.Foundations.Program.G32PropFourSixCharacters
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow14
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Foundations.Program.G32PropFourSixPacked0494
import HodgeLean.Foundations.Program.G32PropFourSixPacked0634
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRow15

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_row13_exponents :
    (g32p_exponents g32p_row13_finiteSupplier).Perm (expandExps [(6, 72)]) := by
  have h0 : papersExps g32p_row13_finiteSupplier.H g32p_row13_finiteSupplier.χ (g32p_classDatum 0) = (([] : List (ZMod 12)) : Multiset (ZMod 12)) := by
    exact g32p_row13_reflectionExponents 0
  have h1 : papersExps g32p_row13_finiteSupplier.H g32p_row13_finiteSupplier.χ (g32p_classDatum 6) = (([] : List (ZMod 12)) : Multiset (ZMod 12)) := by
    exact g32p_row13_reflectionExponents 6
  have h2 : papersExps g32p_row13_finiteSupplier.H g32p_row13_finiteSupplier.χ (g32p_classDatum 12) = (([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List (ZMod 12)) : Multiset (ZMod 12)) := by
    change papersExps g32p_row13_finiteSupplier.H g32p_row13_finiteSupplier.χ (g32p_cosetBranches 2) = _
    rw [g32p_row13_cosetBranchExponents2]
    change ((Finset.univ : Finset (Fin 3312)).val.map
      (fun j => Multiplicative.toAdd (g32p_row13_cosetExponents2 j))).filter (· ≠ 0) = (([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List (ZMod 12)) : Multiset (ZMod 12))
    decide +kernel
  have hs : papersExpsTuple g32p_row13_finiteSupplier.H g32p_row13_finiteSupplier.χ g32p_classList =
      6 • (([] : List (ZMod 12)) : Multiset (ZMod 12)) + 6 • (([] : List (ZMod 12)) : Multiset (ZMod 12)) + (([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List (ZMod 12)) : Multiset (ZMod 12)) := by
    have hc : g32p_classList = List.replicate 6 (g32p_classDatum 0) ++
        List.replicate 6 (g32p_classDatum 6) ++ [g32p_classDatum 12] := rfl
    simp only [papersExpsTuple, hc, List.map_append, List.map_replicate,
      List.map_cons, List.map_nil, List.sum_append, List.sum_replicate,
      List.sum_cons, List.sum_nil, List.sum_singleton, h0, h1, h2, add_zero]
    rfl
  apply Multiset.coe_eq_coe.mp
  change (((papersExpsTuple _ _ _).map ZMod.val).toList : Multiset ℕ) = _
  rw [Multiset.coe_toList, hs]
  change (6 • (([] : List (ZMod 12)) : Multiset (ZMod 12)) + 6 • (([] : List (ZMod 12)) : Multiset (ZMod 12)) + (([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List (ZMod 12)) : Multiset (ZMod 12))).map ZMod.val = ↑(expandExps [(6, 72)])
  decide +kernel

theorem g32p_row13_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 13 ∧ r.m = g32p_row13_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row13_finiteSupplier.H ∧
      (g32p_exponents g32p_row13_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨13, (-1), 24, 12, 21025, 72, 42120, some 6, [(6, 72)], .Sstar⟩, ?_, rfl, rfl, g32p_row13_finiteSupplier_order.symm, g32p_row13_exponents⟩
  decide

def g32p_row13_complexWitness : g32p_row13_finiteSupplier.H →* ℂˣ := g32p_complexCharacter g32p_row13_finiteSupplier

theorem g32p_row13_supplierWitness :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 13 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) := by
  exact ⟨g32p_row13_finiteSupplier, g32p_row13_complexWitness, g32p_complexCharacter_apply _,
    g32p_row13_finiteSupplier_table⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row14_branchTraces : Fin 24 → HurwitzPrymRex_Zw :=
  ![⟨4, 0⟩, ⟨2, 0⟩, ⟨-3, -2⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 2⟩, ⟨3, 2⟩, ⟨2, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨1, -2⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩]

theorem g32p_row14_branchTraceCheck (i : Fin 24) :
    (⟨∑ j : Fin 4, (g32p_row14_groupNodes i j j).re,
      ∑ j : Fin 4, (g32p_row14_groupNodes i j j).om⟩ : HurwitzPrymRex_Zw) =
      g32p_row14_branchTraces i := by
  revert i
  decide +kernel

theorem g32p_row14_branchCharacter (i : Fin 24) :
    g32p_rho.character (g32p_row14_groupEquiv i : g32p_G) =
      HurwitzPrymRex_ev g32h_omega (g32p_row14_branchTraces i) := by
  rw [g32p_rho_character, g32p_row14_groupEquiv_map, g32p_archive_trace,
    g32p_integral_trace, g32p_row14_branchTraceCheck]

theorem g32p_row14_branchTraceAvoid : ∀ i : Fin 24, ∀ j : Fin 12,
    g32p_row14_branchTraces i ≠ g32p_branchTrace ⟨j.val, by omega⟩ := by
  decide +kernel

theorem g32p_row14_reflectionExponents (j : Fin 12) :
    papersExps g32p_row14_finiteSupplier.H g32p_row14_finiteSupplier.χ
      (g32p_classDatum ⟨j.val, by omega⟩) = 0 := by
  apply g32p_exps_of_character_avoid (p := 3) (by decide) _ _ _
    (by simpa only [if_pos j.isLt] using
      g32p_branch_power ⟨j.val, by omega⟩) g32p_rho
  intro h he
  let i := g32p_row14_groupEquiv.symm h
  have hi : g32p_row14_groupEquiv i = h := g32p_row14_groupEquiv.apply_symm_apply h
  rw [← hi, g32p_row14_branchCharacter, g32p_branch_character] at he
  exact g32p_row14_branchTraceAvoid i j
    (HurwitzPrymRex_ev_injective g32h_omega_sq_add he)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

theorem g32p_square_iff_integral (g : g32p_G) (a : HurwitzPrymRex_Mat)
    (ha : b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega a)) :
    g ^ 2 = 1 ↔ HurwitzPrymRex_mmul a a = HurwitzPrymRex_mone := by
  have hi := HurwitzPrymRex_g32conj_injective.comp
    (HurwitzPrymRex_evM_injective g32h_omega_sq_add)
  constructor
  · intro h
    apply hi
    dsimp only [Function.comp_apply]
    rw [HurwitzPrymRex_evM_mmul g32h_omega_sq_add, map_mul,
      ← ha, ← map_mul, ← pow_two, h, map_one, HurwitzPrymRex_evM_mone, map_one]
  · intro h
    apply Subtype.val_injective
    change b4b_toMatrix (g ^ 2) = b4b_toMatrix 1
    rw [map_pow, pow_two, ha, ← map_mul,
      ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add, h,
      HurwitzPrymRex_evM_mone, map_one, map_one]

theorem g32p_row14_nontrivial_involutions (i : Fin 24) :
    (g32p_row14_groupEquiv i : g32p_G) ^ 2 = 1 ∧
      g32p_row14_finiteSupplier.χ (g32p_row14_groupEquiv i) ≠ 1 ↔
    i = 3 ∨ i = 4 := by
  rw [g32p_square_iff_integral _ _ (g32p_row14_groupEquiv_map i),
    g32p_row14_finiteSupplier_value]
  change HurwitzPrymRex_mmul (g32p_row14_groupNodes i) (g32p_row14_groupNodes i) = HurwitzPrymRex_mone ∧
    Multiplicative.toAdd (g32p_row14_characterValues i) ≠ (0 : ZMod 12) ↔ i = 3 ∨ i = 4
  revert i
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000

theorem g32p_row13_nontrivial_involutions (i : Fin 24) :
    (g32p_row13_groupEquiv i : g32p_G) ^ 2 = 1 ∧
      g32p_row13_finiteSupplier.χ (g32p_row13_groupEquiv i) ≠ 1 ↔
    i = 3 ∨ i = 4 := by
  rw [g32p_square_iff_integral _ _ (g32p_row13_groupEquiv_map i),
    g32p_row13_finiteSupplier_value]
  change HurwitzPrymRex_mmul (g32p_row13_groupNodes i) (g32p_row13_groupNodes i) = HurwitzPrymRex_mone ∧
    Multiplicative.toAdd (g32p_row13_characterValues i) ≠ (0 : ZMod 12) ↔ i = 3 ∨ i = 4
  revert i
  decide +kernel

theorem g32p_row14_involution_eq_row13 (i : Fin 24) (hi : i = 3 ∨ i = 4) :
    (g32p_row14_groupEquiv i : g32p_G) = (g32p_row13_groupEquiv i : g32p_G) := by
  apply Subtype.val_injective
  change b4b_toMatrix _ = b4b_toMatrix _
  rw [g32p_row14_groupEquiv_map, g32p_row13_groupEquiv_map]
  congr 2
  rcases hi with rfl | rfl <;> decide +kernel

theorem g32p_row14_involution_support (y : g32p_G) (hy : y ^ 2 = 1) :
    (∃ h : g32p_row14_finiteSupplier.H, (h : g32p_G) = y ∧
      g32p_row14_finiteSupplier.χ h ≠ 1) ↔
    (∃ h : g32p_row13_finiteSupplier.H, (h : g32p_G) = y ∧
      g32p_row13_finiteSupplier.χ h ≠ 1) := by
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨i, rfl⟩ := g32p_row14_groupEquiv.surjective h
    have hi := (g32p_row14_nontrivial_involutions i).mp ⟨hh.symm ▸ hy, hc⟩
    refine ⟨g32p_row13_groupEquiv i, (g32p_row14_involution_eq_row13 i hi).symm.trans hh, ?_⟩
    exact ((g32p_row13_nontrivial_involutions i).mpr hi).2
  · rintro ⟨h, hh, hc⟩
    obtain ⟨i, rfl⟩ := g32p_row13_groupEquiv.surjective h
    have hi := (g32p_row13_nontrivial_involutions i).mp ⟨hh.symm ▸ hy, hc⟩
    refine ⟨g32p_row14_groupEquiv i, (g32p_row14_involution_eq_row13 i hi).trans hh, ?_⟩
    exact ((g32p_row14_nontrivial_involutions i).mpr hi).2

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 200000

theorem g32p_involution_nonzero_fixed {G : Type*} [Group G] [Finite G]
    {m : ℕ} (H : Subgroup G) (χ : H →* Multiplicative (ZMod m))
    (g : G) (hg : g ^ 2 = 1)
    (q : Quotient (orbitRel (Subgroup.zpowers g) (G ⧸ H)))
    (hq : χ (papersLocalMonodromy H g q) ≠ 1) : g • q.out = q.out := by
  have hp : Function.IsPeriodicPt (g • ·) 2 q.out := by
    rw [isPeriodicPt_smul_iff, hg, one_smul]
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hp.minimalPeriod_dvd with h | h
  · exact Function.minimalPeriod_eq_one_iff_isFixedPt.mp h
  · have he : papersLocalMonodromy H g q = 1 := by
      apply Subtype.ext
      change q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out = 1
      rw [h, hg, mul_one, inv_mul_cancel]
    exact (hq (by rw [he, map_one])).elim

theorem g32p_orbit_out_eq_of_fixed {G X : Type*} [Group G] [MulAction G X]
    (g : G) (x : X) (hx : g • x = x) :
    (Quotient.mk'' x : Quotient (orbitRel (Subgroup.zpowers g) X)).out = x := by
  have hrel : orbitRel (Subgroup.zpowers g) X
      (Quotient.mk'' x : Quotient (orbitRel (Subgroup.zpowers g) X)).out x :=
    Quotient.exact' (Quotient.out_eq' _)
  rw [orbitRel_apply, mem_orbit_iff] at hrel
  obtain ⟨a, ha⟩ := hrel
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.property
  rw [Subgroup.mk_smul, ← hk] at ha
  exact ha.symm.trans (mem_fixedBy_zpow hx k)

theorem g32p_exps_card_nonzero_orbits {G : Type*} [Group G] [Finite G]
    {m : ℕ} (H : Subgroup G) (χ : H →* Multiplicative (ZMod m)) (g : G) :
    (papersExps H χ g).card = Nat.card
      {q : Quotient (orbitRel (Subgroup.zpowers g) (G ⧸ H)) //
        χ (papersLocalMonodromy H g q) ≠ 1} := by
  classical
  letI := Fintype.ofFinite (Quotient (orbitRel (Subgroup.zpowers g) (G ⧸ H)))
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp only [papersExps, Multiset.filter_map, Multiset.card_map,
    ← Finset.filter_val, Multiset.coe_card, Function.comp_def]
  congr 1


theorem g32p_involution_exps_card_cosets {G : Type*} [Group G] [Finite G]
    {m : ℕ} (H : Subgroup G) (χ : H →* Multiplicative (ZMod m))
    (g : G) (hg : g ^ 2 = 1) :
    (papersExps H χ g).card = Nat.card
      {c : G ⧸ H // g • c = c ∧
        χ (papersLocalMonodromy H g (Quotient.mk'' c)) ≠ 1} := by
  rw [g32p_exps_card_nonzero_orbits]
  apply Nat.card_congr
  refine { toFun := fun q => ⟨q.val.out, g32p_involution_nonzero_fixed H χ g hg q.val q.property, ?_⟩
           invFun := fun c => ⟨Quotient.mk'' c.val, c.property.2⟩
           left_inv := ?_
           right_inv := ?_ }
  · simpa only [Quotient.out_eq'] using q.property
  · intro q
    exact Subtype.ext (Quotient.out_eq' q.val)
  · intro c
    exact Subtype.ext (g32p_orbit_out_eq_of_fixed g c.val c.property.1)

theorem g32p_fixed_coset_iff {G : Type*} [Group G]
    (H : Subgroup G) (g x : G) :
    g • (x : G ⧸ H) = (x : G ⧸ H) ↔ x⁻¹ * g * x ∈ H := by
  constructor
  · intro h
    simpa only [smul_eq_mul, mul_assoc] using (QuotientGroup.eq.mp h.symm)
  · intro h
    apply Eq.symm
    exact QuotientGroup.eq.mpr (by simpa only [smul_eq_mul, mul_assoc] using h)

theorem g32p_fixed_localCharacter {G : Type*} [Group G]
    {m : ℕ} (H : Subgroup G) (χ : H →* Multiplicative (ZMod m))
    (g x : G) (h : H) (hh : (h : G) = x⁻¹ * g * x) :
    χ (papersLocalMonodromy H g (Quotient.mk'' (x : G ⧸ H))) = χ h := by
  have hf : g • (x : G ⧸ H) = (x : G ⧸ H) :=
    (g32p_fixed_coset_iff H g x).mpr (hh ▸ h.property)
  have hp : Function.minimalPeriod (g • ·) (x : G ⧸ H) = 1 :=
    Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hf
  apply Multiplicative.toAdd.injective
  rw [papersExpVal_eq H χ g _ x rfl]
  unfold papersExpVal
  congr 2
  apply Subtype.ext
  change x⁻¹ * g ^ Function.minimalPeriod (g • ·) (x : G ⧸ H) * x = (h : G)
  rw [hp, pow_one, hh]

theorem g32p_involution_transporters_card {G : Type*} [Group G] [Finite G]
    {m : ℕ} (H : Subgroup G) (χ : H →* Multiplicative (ZMod m))
    (g : G) (hg : g ^ 2 = 1) :
    Nat.card {x : G // ∃ h : H, (h : G) = x⁻¹ * g * x ∧ χ h ≠ 1} =
      Nat.card H * (papersExps H χ g).card := by
  classical
  calc
    _ = Nat.card (QuotientGroup.mk ⁻¹'
        {c : G ⧸ H | g • c = c ∧
          χ (papersLocalMonodromy H g (Quotient.mk'' c)) ≠ 1}) := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro x
      constructor
      · rintro ⟨h, hh, hχ⟩
        refine ⟨(g32p_fixed_coset_iff H g x).mpr (hh ▸ h.property), ?_⟩
        rwa [g32p_fixed_localCharacter H χ g x h hh]
      · rintro ⟨hf, hχ⟩
        let h : H := ⟨x⁻¹ * g * x, (g32p_fixed_coset_iff H g x).mp hf⟩
        refine ⟨h, rfl, ?_⟩
        rwa [g32p_fixed_localCharacter H χ g x h rfl] at hχ
    _ = Nat.card H * Nat.card
        {c : G ⧸ H // g • c = c ∧
          χ (papersLocalMonodromy H g (Quotient.mk'' c)) ≠ 1} := by
      rw [← Nat.card_prod]
      exact Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet H _)
    _ = _ := by rw [← g32p_involution_exps_card_cosets H χ g hg]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 200000

theorem g32p_row14_involution_exps_card :
    (papersExps g32p_row14_finiteSupplier.H g32p_row14_finiteSupplier.χ
      (g32p_classDatum 12)).card =
    (papersExps g32p_row13_finiteSupplier.H g32p_row13_finiteSupplier.χ
      (g32p_classDatum 12)).card := by
  have hg : g32p_classDatum 12 ^ 2 = 1 := g32p_branch_power 12
  have ht := g32p_involution_transporters_card g32p_row14_finiteSupplier.H
    g32p_row14_finiteSupplier.χ (g32p_classDatum 12) hg
  have hs := g32p_involution_transporters_card g32p_row13_finiteSupplier.H
    g32p_row13_finiteSupplier.χ (g32p_classDatum 12) hg
  have he : Nat.card {x : g32p_G // ∃ h : g32p_row14_finiteSupplier.H,
      (h : g32p_G) = x⁻¹ * g32p_classDatum 12 * x ∧
        g32p_row14_finiteSupplier.χ h ≠ 1} =
      Nat.card {x : g32p_G // ∃ h : g32p_row13_finiteSupplier.H,
      (h : g32p_G) = x⁻¹ * g32p_classDatum 12 * x ∧
        g32p_row13_finiteSupplier.χ h ≠ 1} := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x
    apply g32p_row14_involution_support
    calc
      _ = x⁻¹ * g32p_classDatum 12 ^ 2 * x := by simp only [pow_two, mul_assoc, mul_inv_cancel_left]
      _ = 1 := by rw [hg, mul_one, inv_mul_cancel]
  rw [ht, hs, g32p_row14_finiteSupplier_order,
    show Nat.card g32p_row13_finiteSupplier.H = 24 from g32p_row13_finiteSupplier_order] at he
  omega

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers MulAction
set_option maxHeartbeats 200000

theorem g32p_involution_exps_replicate {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (χ : H →* Multiplicative (ZMod 12))
    (g : G) (hg : g ^ 2 = 1) :
    papersExps H χ g = Multiset.replicate (papersExps H χ g).card 6 := by
  classical
  apply Multiset.eq_replicate_card.mpr
  intro a ha
  simp only [papersExps, Multiset.mem_filter, Multiset.mem_map] at ha
  obtain ⟨⟨q, _, rfl⟩, hn⟩ := ha
  have hn' : χ (papersLocalMonodromy H g q) ≠ 1 := hn
  have hf := g32p_involution_nonzero_fixed H χ g hg q hn'
  have hp := Function.minimalPeriod_eq_one_iff_isFixedPt.mpr hf
  have hm : papersLocalMonodromy H g q ^ 2 = 1 := by
    apply Subtype.ext
    change (q.out.out⁻¹ * g ^ Function.minimalPeriod (g • ·) q.out * q.out.out) ^ 2 = 1
    rw [hp, pow_one]
    calc
      _ = q.out.out⁻¹ * g ^ 2 * q.out.out := by simp only [pow_two, mul_assoc, mul_inv_cancel_left]
      _ = 1 := by rw [hg, mul_one, inv_mul_cancel]
  have hc : χ (papersLocalMonodromy H g q) ^ 2 = 1 := by
    rw [← map_pow, hm, map_one]
  have hz : ∀ a : Multiplicative (ZMod 12), a ≠ 1 → a ^ 2 = 1 →
      Multiplicative.toAdd a = 6 := by decide +kernel
  exact hz _ hn' hc

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 200000

theorem g32p_row14_involution_exps_eq :
    papersExps (m := 12) g32p_row14_finiteSupplier.H g32p_row14_finiteSupplier.χ (g32p_classDatum 12) =
    papersExps (m := 12) g32p_row13_finiteSupplier.H g32p_row13_finiteSupplier.χ (g32p_classDatum 12) := by
  calc
    _ = Multiset.replicate _ 6 := g32p_involution_exps_replicate _ _ _ (g32p_branch_power 12)
    _ = Multiset.replicate _ 6 := congrArg (fun n => Multiset.replicate n (6 : ZMod 12))
      g32p_row14_involution_exps_card
    _ = _ := (g32p_involution_exps_replicate _ _ _ (g32p_branch_power 12)).symm

theorem g32p_row14_exponents_eq_row13 :
    g32p_exponents g32p_row14_finiteSupplier = g32p_exponents g32p_row13_finiteSupplier := by
  have hc : g32p_classList = List.replicate 6 (g32p_classDatum 0) ++
      List.replicate 6 (g32p_classDatum 6) ++ [g32p_classDatum 12] := rfl
  have h140 : papersExps (m := 12) g32p_row14_finiteSupplier.H g32p_row14_finiteSupplier.χ
      (g32p_classDatum 0) = 0 := g32p_row14_reflectionExponents 0
  have h146 : papersExps (m := 12) g32p_row14_finiteSupplier.H g32p_row14_finiteSupplier.χ
      (g32p_classDatum 6) = 0 := g32p_row14_reflectionExponents 6
  have h130 : papersExps (m := 12) g32p_row13_finiteSupplier.H g32p_row13_finiteSupplier.χ
      (g32p_classDatum 0) = 0 := g32p_row13_reflectionExponents 0
  have h136 : papersExps (m := 12) g32p_row13_finiteSupplier.H g32p_row13_finiteSupplier.χ
      (g32p_classDatum 6) = 0 := g32p_row13_reflectionExponents 6
  have ht : papersExpsTuple (m := 12) g32p_row14_finiteSupplier.H g32p_row14_finiteSupplier.χ
      g32p_classList = papersExpsTuple (m := 12) g32p_row13_finiteSupplier.H
        g32p_row13_finiteSupplier.χ g32p_classList := by
    simp only [papersExpsTuple, hc, List.map_append, List.map_replicate,
      List.map_cons, List.map_nil, List.sum_append, List.sum_replicate,
      List.sum_cons, List.sum_nil, h140, h146, h130, h136,
      g32p_row14_involution_exps_eq, nsmul_zero, zero_add, add_zero]
  change ((papersExpsTuple (m := 12) _ _ _).map ZMod.val).toList =
    ((papersExpsTuple (m := 12) _ _ _).map ZMod.val).toList
  rw [ht]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 200000

theorem g32p_row14_exponents :
    (g32p_exponents g32p_row14_finiteSupplier).Perm (expandExps [(6, 72)]) := by
  rw [g32p_row14_exponents_eq_row13]
  exact g32p_row13_exponents

theorem g32p_row14_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 14 ∧ r.m = g32p_row14_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row14_finiteSupplier.H ∧
      (g32p_exponents g32p_row14_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨14, (-1), 24, 12, 21025, 72, 42120, some 6, [(6, 72)], .Sstar⟩, ?_, rfl, rfl, g32p_row14_finiteSupplier_order.symm, g32p_row14_exponents⟩
  decide

def g32p_row14_complexWitness : g32p_row14_finiteSupplier.H →* ℂˣ := g32p_complexCharacter g32p_row14_finiteSupplier

theorem g32p_row14_supplierWitness :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 14 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) := by
  exact ⟨g32p_row14_finiteSupplier, g32p_row14_complexWitness, g32p_complexCharacter_apply _,
    g32p_row14_finiteSupplier_table⟩

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

def g32p_row15_branchTraces : Fin 96 → HurwitzPrymRex_Zw :=
  ![⟨4, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨4, 4⟩, ⟨0, -2⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨-4, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 4⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨2, 0⟩, ⟨-4, -4⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨-2, -2⟩, ⟨0, 2⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨2, 2⟩, ⟨0, -4⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨0, -2⟩, ⟨-2, 0⟩, ⟨-2, 0⟩, ⟨2, 2⟩, ⟨0, 0⟩, ⟨2, 2⟩, ⟨0, -2⟩, ⟨-2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨-2, -2⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩, ⟨2, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -2⟩, ⟨2, 2⟩]

theorem g32p_row15_branchTraceCheck (i : Fin 96) :
    (⟨∑ j : Fin 4, (g32p_row15_groupNodes i j j).re,
      ∑ j : Fin 4, (g32p_row15_groupNodes i j j).om⟩ : HurwitzPrymRex_Zw) =
      g32p_row15_branchTraces i := by
  revert i
  decide +kernel

theorem g32p_row15_branchCharacter (i : Fin 96) :
    g32p_rho.character (g32p_row15_groupEquiv i : g32p_G) =
      HurwitzPrymRex_ev g32h_omega (g32p_row15_branchTraces i) := by
  rw [g32p_rho_character, g32p_row15_groupEquiv_map, g32p_archive_trace,
    g32p_integral_trace, g32p_row15_branchTraceCheck]

theorem g32p_row15_branchTraceAvoid : ∀ i : Fin 96, ∀ j : Fin 12,
    g32p_row15_branchTraces i ≠ g32p_branchTrace ⟨j.val, by omega⟩ := by
  decide +kernel

theorem g32p_row15_reflectionExponents (j : Fin 12) :
    papersExps g32p_row15_finiteSupplier.H g32p_row15_finiteSupplier.χ
      (g32p_classDatum ⟨j.val, by omega⟩) = 0 := by
  apply g32p_exps_of_character_avoid (p := 3) (by decide) _ _ _
    (by simpa only [if_pos j.isLt] using
      g32p_branch_power ⟨j.val, by omega⟩) g32p_rho
  intro h he
  let i := g32p_row15_groupEquiv.symm h
  have hi : g32p_row15_groupEquiv i = h := g32p_row15_groupEquiv.apply_symm_apply h
  rw [← hi, g32p_row15_branchCharacter, g32p_branch_character] at he
  exact g32p_row15_branchTraceAvoid i j
    (HurwitzPrymRex_ev_injective g32h_omega_sq_add he)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

def g32p_row15_involutionConjugator : g32p_G := g32p_archiveWord [1, 3, 3]

theorem g32p_row15_nontrivial_involutions (i : Fin 96) :
    (g32p_row15_groupEquiv i : g32p_G) ^ 2 = 1 ∧
      g32p_row15_finiteSupplier.χ (g32p_row15_groupEquiv i) ≠ 1 ↔
    i = 7 ∨ i = 10 := by
  rw [g32p_square_iff_integral _ _ (g32p_row15_groupEquiv_map i),
    g32p_row15_finiteSupplier_value]
  change HurwitzPrymRex_mmul (g32p_row15_groupNodes i) (g32p_row15_groupNodes i) = HurwitzPrymRex_mone ∧
    Multiplicative.toAdd (g32p_row15_characterValues i) ≠ (0 : ZMod 12) ↔ i = 7 ∨ i = 10
  revert i
  decide +kernel

theorem g32p_row15_involution_conjugator (i : Fin 24) (hi : i = 3 ∨ i = 4) :
    (g32p_row15_groupEquiv (if i = 3 then 10 else 7) : g32p_G) *
      g32p_row15_involutionConjugator =
    g32p_row15_involutionConjugator * (g32p_row13_groupEquiv i : g32p_G) := by
  apply (show Function.Injective b4b_toMatrix from Subtype.val_injective)
  rw [map_mul, map_mul, g32p_row15_groupEquiv_map, g32p_row13_groupEquiv_map]
  change _ * b4b_toMatrix (g32p_archiveWord [1, 3, 3]) =
    b4b_toMatrix (g32p_archiveWord [1, 3, 3]) * _
  rw [g32p_archiveIntegralWord_map, ← map_mul, ← map_mul,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add]
  congr 2
  rcases hi with rfl | rfl <;> decide +kernel

theorem g32p_row15_involution_conjugate (i : Fin 24) (hi : i = 3 ∨ i = 4) :
    g32p_row15_involutionConjugator⁻¹ *
      (g32p_row15_groupEquiv (if i = 3 then 10 else 7) : g32p_G) *
        g32p_row15_involutionConjugator = (g32p_row13_groupEquiv i : g32p_G) := by
  calc
    _ = g32p_row15_involutionConjugator⁻¹ *
        ((g32p_row15_groupEquiv (if i = 3 then 10 else 7) : g32p_G) *
          g32p_row15_involutionConjugator) := by group
    _ = g32p_row15_involutionConjugator⁻¹ *
        (g32p_row15_involutionConjugator * (g32p_row13_groupEquiv i : g32p_G)) := by
      rw [g32p_row15_involution_conjugator i hi]
    _ = _ := by group

theorem g32p_row15_involution_support (y : g32p_G) (hy : y ^ 2 = 1) :
    (∃ h : g32p_row15_finiteSupplier.H, (h : g32p_G) = y ∧
      g32p_row15_finiteSupplier.χ h ≠ 1) ↔
    (∃ h : g32p_row13_finiteSupplier.H,
      (h : g32p_G) = g32p_row15_involutionConjugator⁻¹ * y *
        g32p_row15_involutionConjugator ∧ g32p_row13_finiteSupplier.χ h ≠ 1) := by
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨i, rfl⟩ := g32p_row15_groupEquiv.surjective h
    have hi := (g32p_row15_nontrivial_involutions i).mp ⟨hh.symm ▸ hy, hc⟩
    rcases hi with rfl | rfl
    · refine ⟨g32p_row13_groupEquiv 4, ?_,
        ((g32p_row13_nontrivial_involutions 4).mpr (Or.inr rfl)).2⟩
      rw [← hh]
      exact (g32p_row15_involution_conjugate 4 (Or.inr rfl)).symm
    · refine ⟨g32p_row13_groupEquiv 3, ?_,
        ((g32p_row13_nontrivial_involutions 3).mpr (Or.inl rfl)).2⟩
      rw [← hh]
      exact (g32p_row15_involution_conjugate 3 (Or.inl rfl)).symm
  · rintro ⟨h, hh, hc⟩
    obtain ⟨i, rfl⟩ := g32p_row13_groupEquiv.surjective h
    have hp : (g32p_row13_groupEquiv i : g32p_G) ^ 2 = 1 := by
      rw [hh]
      calc
        _ = g32p_row15_involutionConjugator⁻¹ * y ^ 2 *
            g32p_row15_involutionConjugator := by
          simp only [pow_two, mul_assoc, mul_inv_cancel_left]
        _ = 1 := by rw [hy]; group
    have hi := (g32p_row13_nontrivial_involutions i).mp ⟨hp, hc⟩
    refine ⟨g32p_row15_groupEquiv (if i = 3 then 10 else 7), ?_, ?_⟩
    · have he := (g32p_row15_involution_conjugate i hi).trans hh
      calc
        _ = g32p_row15_involutionConjugator *
            (g32p_row15_involutionConjugator⁻¹ *
              (g32p_row15_groupEquiv (if i = 3 then 10 else 7) : g32p_G) *
                g32p_row15_involutionConjugator) *
                  g32p_row15_involutionConjugator⁻¹ := by group
        _ = g32p_row15_involutionConjugator *
            (g32p_row15_involutionConjugator⁻¹ * y * g32p_row15_involutionConjugator) *
              g32p_row15_involutionConjugator⁻¹ := by rw [he]
        _ = y := by group
    · apply ((g32p_row15_nontrivial_involutions _).mpr ?_).2
      rcases hi with rfl | rfl <;> decide

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 200000

def g32p_row15_transporterEquiv :
    {x : g32p_G // ∃ h : g32p_row15_finiteSupplier.H,
      (h : g32p_G) = x⁻¹ * g32p_classDatum 12 * x ∧ g32p_row15_finiteSupplier.χ h ≠ 1} ≃
    {x : g32p_G // ∃ h : g32p_row13_finiteSupplier.H,
      (h : g32p_G) = x⁻¹ * g32p_classDatum 12 * x ∧ g32p_row13_finiteSupplier.χ h ≠ 1} where
  toFun x := ⟨x.val * g32p_row15_involutionConjugator, by
    have hp : (x.val⁻¹ * g32p_classDatum 12 * x.val) ^ 2 = 1 := by
      have hg : g32p_classDatum 12 ^ 2 = 1 := g32p_branch_power 12
      calc
        _ = x.val⁻¹ * g32p_classDatum 12 ^ 2 * x.val := by
          simp only [pow_two, mul_assoc, mul_inv_cancel_left]
        _ = 1 := by rw [hg]; group
    obtain ⟨h, hh, hc⟩ := (g32p_row15_involution_support _ hp).mp x.property
    refine ⟨h, hh.trans ?_, hc⟩
    group⟩
  invFun x := ⟨x.val * g32p_row15_involutionConjugator⁻¹, by
    have hp : ((x.val * g32p_row15_involutionConjugator⁻¹)⁻¹ *
        g32p_classDatum 12 * (x.val * g32p_row15_involutionConjugator⁻¹)) ^ 2 = 1 := by
      have hg : g32p_classDatum 12 ^ 2 = 1 := g32p_branch_power 12
      calc
        _ = (x.val * g32p_row15_involutionConjugator⁻¹)⁻¹ * g32p_classDatum 12 ^ 2 *
            (x.val * g32p_row15_involutionConjugator⁻¹) := by
          simp only [pow_two, mul_assoc, mul_inv_cancel_left]
        _ = 1 := by rw [hg]; group
    apply (g32p_row15_involution_support _ hp).mpr
    obtain ⟨h, hh, hc⟩ := x.property
    refine ⟨h, hh.trans ?_, hc⟩
    group⟩
  left_inv x := by apply Subtype.ext; change x.val * _ * _ = x.val; group
  right_inv x := by apply Subtype.ext; change x.val * _ * _ = x.val; group

theorem g32p_row15_involution_exps_card :
    4 * (papersExps g32p_row15_finiteSupplier.H g32p_row15_finiteSupplier.χ
      (g32p_classDatum 12)).card =
    (papersExps g32p_row13_finiteSupplier.H g32p_row13_finiteSupplier.χ
      (g32p_classDatum 12)).card := by
  have he := Nat.card_congr g32p_row15_transporterEquiv
  rw [g32p_involution_transporters_card _ _ _ (g32p_branch_power 12),
    g32p_involution_transporters_card _ _ _ (g32p_branch_power 12),
    g32p_row15_finiteSupplier_order, g32p_row13_finiteSupplier_order] at he
  omega

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 200000

theorem g32p_row15_exponents :
    (g32p_exponents g32p_row15_finiteSupplier).Perm (expandExps [(6, 18)]) := by
  have h0 : papersExps (m := 12) g32p_row15_finiteSupplier.H g32p_row15_finiteSupplier.χ (g32p_classDatum 0) = (([] : List (ZMod 12)) : Multiset (ZMod 12)) := by
    exact g32p_row15_reflectionExponents 0
  have h1 : papersExps (m := 12) g32p_row15_finiteSupplier.H g32p_row15_finiteSupplier.χ (g32p_classDatum 6) = (([] : List (ZMod 12)) : Multiset (ZMod 12)) := by
    exact g32p_row15_reflectionExponents 6
  have h2 : papersExps (m := 12) g32p_row15_finiteSupplier.H g32p_row15_finiteSupplier.χ (g32p_classDatum 12) = (([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List (ZMod 12)) : Multiset (ZMod 12)) := by
    have hc : (papersExps (m := 12) g32p_row15_finiteSupplier.H g32p_row15_finiteSupplier.χ
        (g32p_classDatum 12)).card = 18 := by
      have h13 : (papersExps (m := 12) g32p_row13_finiteSupplier.H g32p_row13_finiteSupplier.χ
          (g32p_classDatum 12)).card = 72 := by
        have ht : papersExpsTuple (m := 12) g32p_row13_finiteSupplier.H g32p_row13_finiteSupplier.χ
            g32p_classList = papersExps (m := 12) g32p_row13_finiteSupplier.H
              g32p_row13_finiteSupplier.χ (g32p_classDatum 12) := by
          have hclass : g32p_classList = List.replicate 6 (g32p_classDatum 0) ++
              List.replicate 6 (g32p_classDatum 6) ++ [g32p_classDatum 12] := rfl
          have h130 : papersExps (m := 12) g32p_row13_finiteSupplier.H
              g32p_row13_finiteSupplier.χ (g32p_classDatum 0) = 0 :=
            g32p_row13_reflectionExponents 0
          have h136 : papersExps (m := 12) g32p_row13_finiteSupplier.H
              g32p_row13_finiteSupplier.χ (g32p_classDatum 6) = 0 :=
            g32p_row13_reflectionExponents 6
          simp only [papersExpsTuple, hclass, List.map_append, List.map_replicate,
            List.map_cons, List.map_nil, List.sum_append, List.sum_replicate,
            List.sum_cons, List.sum_nil, h130, h136, nsmul_zero, zero_add, add_zero]
        have hl := g32p_row13_exponents.length_eq
        change ((papersExpsTuple (m := 12) _ _ _).map ZMod.val).toList.length = 72 at hl
        simpa only [Multiset.length_toList, Multiset.card_map, ht] using hl
      have hm : 4 * (papersExps (m := 12) g32p_row15_finiteSupplier.H
          g32p_row15_finiteSupplier.χ (g32p_classDatum 12)).card =
          (papersExps (m := 12) g32p_row13_finiteSupplier.H
            g32p_row13_finiteSupplier.χ (g32p_classDatum 12)).card :=
        g32p_row15_involution_exps_card
      omega
    erw [g32p_involution_exps_replicate _ _ _ (g32p_branch_power 12), hc]
    decide +kernel
  have hs : papersExpsTuple (m := 12) g32p_row15_finiteSupplier.H g32p_row15_finiteSupplier.χ g32p_classList =
      6 • (([] : List (ZMod 12)) : Multiset (ZMod 12)) + 6 • (([] : List (ZMod 12)) : Multiset (ZMod 12)) + (([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List (ZMod 12)) : Multiset (ZMod 12)) := by
    have hc : g32p_classList = List.replicate 6 (g32p_classDatum 0) ++
        List.replicate 6 (g32p_classDatum 6) ++ [g32p_classDatum 12] := rfl
    simp only [papersExpsTuple, hc, List.map_append, List.map_replicate,
      List.map_cons, List.map_nil, List.sum_append, List.sum_replicate,
      List.sum_cons, List.sum_nil, List.sum_singleton, h0, h1, h2, add_zero]
  apply Multiset.coe_eq_coe.mp
  change (((papersExpsTuple (m := 12) _ _ _).map ZMod.val).toList : Multiset ℕ) = _
  erw [Multiset.coe_toList, hs]
  change (6 • (([] : List (ZMod 12)) : Multiset (ZMod 12)) + 6 • (([] : List (ZMod 12)) : Multiset (ZMod 12)) + (([6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6] : List (ZMod 12)) : Multiset (ZMod 12))).map ZMod.val = ↑(expandExps [(6, 18)])
  decide +kernel

theorem g32p_row15_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 15 ∧ r.m = g32p_row15_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row15_finiteSupplier.H ∧
      (g32p_exponents g32p_row15_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨15, (-1), 96, 12, 5257, 18, 10530, some 6, [(6, 18)], .Sstar⟩, ?_, rfl, rfl, g32p_row15_finiteSupplier_order.symm, g32p_row15_exponents⟩
  decide

def g32p_row15_complexWitness : g32p_row15_finiteSupplier.H →* ℂˣ := g32p_complexCharacter g32p_row15_finiteSupplier

theorem g32p_row15_supplierWitness :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 15 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) := by
  exact ⟨g32p_row15_finiteSupplier, g32p_row15_complexWitness, g32p_complexCharacter_apply _,
    g32p_row15_finiteSupplier_table⟩

end HodgeLean.Foundations.Program

end
end
