import HodgeLean.Foundations.Program.PrymVariationCentreRotation

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b63d_weighted_orbit_sum {G C : Type} [Group G] [Fintype G] [MulAction G C]
    (a : C → ℝ) (ha : ∀ g : G, ∀ x : C, a (g • x) = a x) (x : C) :
    (∑ᶠ y ∈ MulAction.orbit G x,
      (Nat.card (MulAction.stabilizer G y) : ℝ) / Fintype.card G * a y) =
        a x := by
  classical
  have hfin : (MulAction.orbit G x).Finite := Set.finite_range (fun g : G ↦ g • x)
  have he (y : C) (hy : y ∈ MulAction.orbit G x) :
      (Nat.card (MulAction.stabilizer G y) : ℝ) / Fintype.card G * a y =
        (Nat.card (MulAction.stabilizer G x) : ℝ) / Fintype.card G * a x := by
    obtain ⟨g, rfl⟩ := hy
    rw [ha]
    have hc := Nat.card_congr
      (MulAction.stabilizerEquivStabilizer (g := g) (a := x) rfl).toEquiv.symm
    rw [hc]
  have hcard : (MulAction.orbit G x).ncard *
      Nat.card (MulAction.stabilizer G x) = Fintype.card G := by
    have h := Subgroup.index_mul_card (MulAction.stabilizer G x)
    rw [MulAction.index_stabilizer] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hcardR : ((MulAction.orbit G x).ncard : ℝ) *
      Nat.card (MulAction.stabilizer G x) = Fintype.card G := by
    exact_mod_cast hcard
  have hn : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [finsum_mem_congr rfl he, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin]
  calc
    ((MulAction.orbit G x).ncard : ℝ) *
        ((Nat.card (MulAction.stabilizer G x) : ℝ) / Fintype.card G * a x) =
      (((MulAction.orbit G x).ncard : ℝ) *
        Nat.card (MulAction.stabilizer G x) / Fintype.card G) * a x := by ring
    _ = a x := by rw [hcardR, div_self hn, one_mul]

theorem b63d_weighted_orbits_sum {G C ι : Type} [Group G] [Fintype G] [Fintype ι]
    [MulAction G C] (a : C → ℝ) (ha : ∀ g : G, ∀ x : C, a (g • x) = a x)
    (x : ι → C) (hd : Pairwise (fun i j ↦ Disjoint (MulAction.orbit G (x i)) (MulAction.orbit G (x j))))
    (hs : Function.support a ⊆ ⋃ i, MulAction.orbit G (x i)) :
    (∑ᶠ y : C, (Nat.card (MulAction.stabilizer G y) : ℝ) / Fintype.card G * a y) =
      ∑ i, a (x i) := by
  classical
  let f : C → ℝ := fun y ↦
    (Nat.card (MulAction.stabilizer G y) : ℝ) / Fintype.card G * a y
  have hsf : Function.support f ⊆ ⋃ i, MulAction.orbit G (x i) := by
    intro y hy
    apply hs
    intro hay
    exact hy (by simp only [f, hay, mul_zero])
  have hr : (∑ᶠ y : C, f y) = ∑ᶠ y ∈ ⋃ i, MulAction.orbit G (x i), f y := by
    rw [← finsum_mem_univ]
    apply finsum_mem_inter_support_eq'
    intro y hy
    exact iff_of_true (Set.mem_univ y) (hsf hy)
  change (∑ᶠ y : C, f y) = _
  rw [hr, finsum_mem_iUnion hd (fun i ↦ Set.finite_range (fun g : G ↦ g • x i)),
    finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  exact b63d_weighted_orbit_sum a ha (x i)

end HodgeLean.Foundations.Program
