import HodgeLean.Foundations.Program.G32PropFourSixSupplierWitness02CosetData
import HodgeLean.Foundations.Program.G32PropFourSixPacked0629
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448
import HodgeLean.Papers.PapersSupplyProofs
import HodgeLean.Foundations.Program.G32PropFourSixPacked0630
import HodgeLean.Foundations.Program.G32PropFourSixPacked0631
import HodgeLean.Foundations.Program.G32PropFourSixPacked0632
import HodgeLean.Foundations.Program.G32PropFourSixPacked0633
import HodgeLean.Foundations.Program.G32PropFourSixCharacters

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetMonodromy_2_0023 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices 2) (HurwitzPrymRex_mone)) (g32p_row02_cosetRepresentatives 36) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives 36)
        (g32p_row02_groupNodes (g32p_row02_cosetMonodromies2 23)) ∧
    g32p_row02_characterValues (g32p_row02_cosetMonodromies2 23) = g32p_row02_cosetExponents2 23 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetMonodromy_2_0024 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices 2) (HurwitzPrymRex_mone)) (g32p_row02_cosetRepresentatives 37) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives 37)
        (g32p_row02_groupNodes (g32p_row02_cosetMonodromies2 24)) ∧
    g32p_row02_characterValues (g32p_row02_cosetMonodromies2 24) = g32p_row02_cosetExponents2 24 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetMonodromy_2_0025 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices 2) (HurwitzPrymRex_mone)) (g32p_row02_cosetRepresentatives 38) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives 38)
        (g32p_row02_groupNodes (g32p_row02_cosetMonodromies2 25)) ∧
    g32p_row02_characterValues (g32p_row02_cosetMonodromies2 25) = g32p_row02_cosetExponents2 25 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetMonodromy_2_0026 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row02_cosetRepresentatives 39) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives 39)
        (g32p_row02_groupNodes (g32p_row02_cosetMonodromies2 26)) ∧
    g32p_row02_characterValues (g32p_row02_cosetMonodromies2 26) = g32p_row02_cosetExponents2 26 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetMonodromy_2_0027 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices 2) (HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices 2) (HurwitzPrymRex_mone))) (g32p_row02_cosetRepresentatives 40) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives 40)
        (g32p_row02_groupNodes (g32p_row02_cosetMonodromies2 27)) ∧
    g32p_row02_characterValues (g32p_row02_cosetMonodromies2 27) = g32p_row02_cosetExponents2 27 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetMonodromy_2_0028 :
    HurwitzPrymRex_mmul (HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices 2) (HurwitzPrymRex_mone)) (g32p_row02_cosetRepresentatives 43) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives 43)
        (g32p_row02_groupNodes (g32p_row02_cosetMonodromies2 28)) ∧
    g32p_row02_characterValues (g32p_row02_cosetMonodromies2 28) = g32p_row02_cosetExponents2 28 := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 200000

noncomputable def g32p_cosetBranches : Fin 3 → g32p_G :=
  ![g32p_classDatum 0, g32p_classDatum 6, g32p_classDatum 12]

def g32p_cosetIntegralBranches : Fin 3 → HurwitzPrymRex_Mat :=
  ![HurwitzPrymRex_nth HurwitzPrymRex_g32SOne 0,
    HurwitzPrymRex_nth HurwitzPrymRex_g32SOne 1,
    HurwitzPrymRex_mmul (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne 2)
      (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne 2)]

theorem g32p_cosetBranches_map (b : Fin 3) :
    b4b_toMatrix (g32p_cosetBranches b) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_cosetIntegralBranches b)) := by
  fin_cases b
  · exact g32p_integralGenerator_map 0
  · exact g32p_integralGenerator_map 1
  · change b4b_toMatrix (b4b_generators 2 * b4b_generators 2) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega
        (HurwitzPrymRex_mmul (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne 2)
          (HurwitzPrymRex_nth HurwitzPrymRex_g32SOne 2)))
    rw [map_mul, g32p_integralGenerator_map,
      HurwitzPrymRex_evM_mmul g32h_omega_sq_add, map_mul]
    rfl

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetBranchMatrix0 : g32p_row02_cosetBranchMatrices 0 = g32p_cosetIntegralBranches 0 := by
  decide +kernel

theorem g32p_row02_cosetPartition0 : (g32p_row02_cosetCycles0).flatten.Perm (List.range 45) := by
  decide +kernel

theorem g32p_row02_cosetRootLabels0 : ∀ j : Fin 21, g32p_row02_cosetLabels0 (g32p_row02_cosetRoots0 j) = j := by
  decide +kernel

theorem g32p_row02_cosetNextLabels0 : ∀ i : Fin 45, g32p_row02_cosetLabels0 (g32p_row02_cosetBranchNext 0 i) = g32p_row02_cosetLabels0 i := by
  decide +kernel

theorem g32p_row02_cosetReach0 : ∀ i : Fin 45, (g32p_row02_cosetBranchNext 0)^[g32p_row02_cosetDistances0 i] (g32p_row02_cosetRoots0 (g32p_row02_cosetLabels0 i)) = i := by
  decide +kernel

theorem g32p_row02_cosetPeriods0 : ∀ j : Fin 21, 0 < g32p_row02_cosetLengths0 j ∧ (g32p_row02_cosetBranchNext 0)^[g32p_row02_cosetLengths0 j] (g32p_row02_cosetRoots0 j) = g32p_row02_cosetRoots0 j ∧ ∀ t : Fin (g32p_row02_cosetLengths0 j), 0 < t.val → (g32p_row02_cosetBranchNext 0)^[t.val] (g32p_row02_cosetRoots0 j) ≠ g32p_row02_cosetRoots0 j := by
  decide +kernel

theorem g32p_row02_cosetCycleSteps0 : ∀ cycle ∈ g32p_row02_cosetCycles0,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row02_cosetBranchNext 0 ⟨i % 45, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

theorem g32p_row02_cosetPermutation0 : Function.Bijective (g32p_row02_cosetBranchNext 0) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetBranchMatrix1 : g32p_row02_cosetBranchMatrices 1 = g32p_cosetIntegralBranches 1 := by
  decide +kernel

theorem g32p_row02_cosetPartition1 : (g32p_row02_cosetCycles1).flatten.Perm (List.range 45) := by
  decide +kernel

theorem g32p_row02_cosetRootLabels1 : ∀ j : Fin 21, g32p_row02_cosetLabels1 (g32p_row02_cosetRoots1 j) = j := by
  decide +kernel

theorem g32p_row02_cosetNextLabels1 : ∀ i : Fin 45, g32p_row02_cosetLabels1 (g32p_row02_cosetBranchNext 1 i) = g32p_row02_cosetLabels1 i := by
  decide +kernel

theorem g32p_row02_cosetReach1 : ∀ i : Fin 45, (g32p_row02_cosetBranchNext 1)^[g32p_row02_cosetDistances1 i] (g32p_row02_cosetRoots1 (g32p_row02_cosetLabels1 i)) = i := by
  decide +kernel

theorem g32p_row02_cosetPeriods1 : ∀ j : Fin 21, 0 < g32p_row02_cosetLengths1 j ∧ (g32p_row02_cosetBranchNext 1)^[g32p_row02_cosetLengths1 j] (g32p_row02_cosetRoots1 j) = g32p_row02_cosetRoots1 j ∧ ∀ t : Fin (g32p_row02_cosetLengths1 j), 0 < t.val → (g32p_row02_cosetBranchNext 1)^[t.val] (g32p_row02_cosetRoots1 j) ≠ g32p_row02_cosetRoots1 j := by
  decide +kernel

theorem g32p_row02_cosetCycleSteps1 : ∀ cycle ∈ g32p_row02_cosetCycles1,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row02_cosetBranchNext 1 ⟨i % 45, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

theorem g32p_row02_cosetPermutation1 : Function.Bijective (g32p_row02_cosetBranchNext 1) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row02_cosetBranchMatrix2 : g32p_row02_cosetBranchMatrices 2 = g32p_cosetIntegralBranches 2 := by
  decide +kernel

theorem g32p_row02_cosetPartition2 : (g32p_row02_cosetCycles2).flatten.Perm (List.range 45) := by
  decide +kernel

theorem g32p_row02_cosetRootLabels2 : ∀ j : Fin 29, g32p_row02_cosetLabels2 (g32p_row02_cosetRoots2 j) = j := by
  decide +kernel

theorem g32p_row02_cosetNextLabels2 : ∀ i : Fin 45, g32p_row02_cosetLabels2 (g32p_row02_cosetBranchNext 2 i) = g32p_row02_cosetLabels2 i := by
  decide +kernel

theorem g32p_row02_cosetReach2 : ∀ i : Fin 45, (g32p_row02_cosetBranchNext 2)^[g32p_row02_cosetDistances2 i] (g32p_row02_cosetRoots2 (g32p_row02_cosetLabels2 i)) = i := by
  decide +kernel

theorem g32p_row02_cosetPeriods2 : ∀ j : Fin 29, 0 < g32p_row02_cosetLengths2 j ∧ (g32p_row02_cosetBranchNext 2)^[g32p_row02_cosetLengths2 j] (g32p_row02_cosetRoots2 j) = g32p_row02_cosetRoots2 j ∧ ∀ t : Fin (g32p_row02_cosetLengths2 j), 0 < t.val → (g32p_row02_cosetBranchNext 2)^[t.val] (g32p_row02_cosetRoots2 j) ≠ g32p_row02_cosetRoots2 j := by
  decide +kernel

theorem g32p_row02_cosetCycleSteps2 : ∀ cycle ∈ g32p_row02_cosetCycles2,
    cycle.Nodup ∧ 0 < cycle.length ∧
    cycle.map (fun i => (g32p_row02_cosetBranchNext 2 ⟨i % 45, Nat.mod_lt _ (by decide)⟩).val) = cycle.rotate 1 := by
  decide +kernel

theorem g32p_row02_cosetPermutation2 : Function.Bijective (g32p_row02_cosetBranchNext 2) := by
  decide +kernel


end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 200000

def g32p_integralMatrixPower (A : HurwitzPrymRex_Mat) : ℕ → HurwitzPrymRex_Mat
  | 0 => HurwitzPrymRex_mone
  | n + 1 => HurwitzPrymRex_mmul A (g32p_integralMatrixPower A n)

theorem g32p_integralMatrixPower_map (A : HurwitzPrymRex_Mat) (n : ℕ) :
    HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_integralMatrixPower A n)) =
      (HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega A)) ^ n := by
  induction n with
  | zero => rw [g32p_integralMatrixPower, HurwitzPrymRex_evM_mone, map_one, pow_zero]
  | succ n ih =>
    rw [g32p_integralMatrixPower, HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
      map_mul, ih, pow_succ']

theorem g32p_actual_monodromy (g r h : g32p_G)
    (A R M : HurwitzPrymRex_Mat) (n : ℕ)
    (hg : b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega A))
    (hr : b4b_toMatrix r = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega R))
    (hh : b4b_toMatrix h = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega M))
    (hcheck : HurwitzPrymRex_mmul (g32p_integralMatrixPower A n) R =
      HurwitzPrymRex_mmul R M) : g ^ n * r = r * h := by
  apply Subtype.ext
  change b4b_toMatrix (g ^ n * r) = b4b_toMatrix (r * h)
  rw [map_mul, map_mul, map_pow, hg, hr, hh,
    ← g32p_integralMatrixPower_map, ← map_mul, ← map_mul,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add, hcheck]

end HodgeLean.Foundations.Program

end

section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 200000

theorem g32p_exps_of_orbit_enumeration {G : Type*} [Group G] [Finite G]
    {m c : ℕ} (H : Subgroup G) (χ : H →* Multiplicative (ZMod m)) (g : G)
    (e : Fin c ≃ Quotient (orbitRel (Subgroup.zpowers g) (G ⧸ H)))
    (reps : Fin c → G)
    (hreps : ∀ i, Quotient.mk'' (reps i : G ⧸ H) = e i)
    (periods : Fin c → ℕ)
    (hperiods : ∀ i, Function.minimalPeriod (g • ·) (reps i : G ⧸ H) = periods i)
    (monodromies : Fin c → H)
    (hmonodromies : ∀ i, g ^ periods i * reps i = reps i * monodromies i) :
    papersExps H χ g =
      (Finset.univ.val.map (fun i => Multiplicative.toAdd (χ (monodromies i)))).filter
        (· ≠ 0) := by
  classical
  letI := Fintype.ofFinite (Quotient (orbitRel (Subgroup.zpowers g) (G ⧸ H)))
  have hv (i : Fin c) :
      Multiplicative.toAdd (χ (papersLocalMonodromy H g (e i))) =
        Multiplicative.toAdd (χ (monodromies i)) := by
    rw [papersExpVal_eq H χ g (e i) (reps i) (hreps i)]
    unfold papersExpVal
    congr 2
    apply Subtype.ext
    change (reps i)⁻¹ * g ^ Function.minimalPeriod (g • ·) (reps i : G ⧸ H) * reps i = _
    rw [hperiods, mul_assoc, hmonodromies, ← mul_assoc, inv_mul_cancel, one_mul]
  unfold papersExps
  congr 1
  calc
    _ = (Finset.univ.val.map e).map
        (fun q => Multiplicative.toAdd (χ (papersLocalMonodromy H g q))) := by
      rw [Multiset.map_univ_val_equiv]
    _ = _ := by simp only [Multiset.map_map, Function.comp_def, hv]

theorem g32p_cycle_orbit_bijective {G X : Type*} [Group G] [Finite G]
    [MulAction G X] {n c : ℕ} (g : G) (e : Fin n ≃ X)
    (next : Fin n → Fin n) (hstep : ∀ i, e (next i) = g • e i)
    (label : Fin n → Fin c) (root : Fin c → Fin n) (distance : Fin n → ℕ)
    (hroot : ∀ j, label (root j) = j)
    (hlabel : ∀ i, label (next i) = label i)
    (hreach : ∀ i, next^[distance i] (root (label i)) = i) :
    Function.Bijective (fun j =>
      (Quotient.mk'' (e (root j)) : Quotient (orbitRel (Subgroup.zpowers g) X))) := by
  classical
  let L : X → Fin c := fun x => label (e.symm x)
  have hL (x : X) : L (g • x) = L x := by
    obtain ⟨i, rfl⟩ := e.surjective x
    change label (e.symm (g • e i)) = label (e.symm (e i))
    rw [← hstep, e.symm_apply_apply, e.symm_apply_apply, hlabel]
  have hpow (t : ℕ) (x : X) : L (g ^ t • x) = L x := by
    induction t with
    | zero => rw [pow_zero, one_smul]
    | succ t ih => rw [pow_succ', mul_smul, hL, ih]
  have horbit (x y : X) (hxy : orbitRel (Subgroup.zpowers g) X x y) : L x = L y := by
    rw [orbitRel_apply, mem_orbit_iff] at hxy
    obtain ⟨a, ha⟩ := hxy
    have hp := a.property
    rw [mem_zpowers_iff_mem_range_orderOf] at hp
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hp
    have he : (a : G) = g ^ t := ht.symm
    rw [Subgroup.mk_smul, he] at ha
    rw [← ha, hpow]
  have hiter (t : ℕ) (i : Fin n) : e (next^[t] i) = g ^ t • e i := by
    induction t with
    | zero => simp only [Function.iterate_zero, id_eq, pow_zero, one_smul]
    | succ t ih =>
      rw [Function.iterate_succ_apply', hstep, ih, pow_succ', mul_smul]
  constructor
  · intro j k hjk
    have he := horbit _ _ (Quotient.exact hjk)
    simpa only [L, e.symm_apply_apply, hroot] using he
  · intro q
    induction q using Quotient.inductionOn' with
    | h x =>
      let i := e.symm x
      refine ⟨label i, Quotient.sound ?_⟩
      apply Setoid.symm'
      rw [orbitRel_apply, mem_orbit_iff]
      refine ⟨⟨g ^ distance i, Subgroup.npow_mem_zpowers g _⟩, ?_⟩
      change g ^ distance i • e (root (label i)) = x
      rw [← hiter, hreach]
      exact e.apply_symm_apply x

theorem g32p_period_of_cycle {X Y : Type*} (e : X ≃ Y) (f : X → X) (g : Y → Y)
    (hstep : ∀ x, e (f x) = g (e x)) (x : X) (length : ℕ)
    (hpos : 0 < length) (hreturn : f^[length] x = x)
    (hshort : ∀ t, 0 < t → t < length → f^[t] x ≠ x) :
    Function.minimalPeriod g (e x) = length := by
  have hiter (t : ℕ) : e (f^[t] x) = g^[t] (e x) := by
    induction t with
    | zero => rfl
    | succ t ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hstep, ih]
  have hreturn' : Function.IsPeriodicPt g length (e x) := by
    change g^[length] (e x) = e x
    rw [← hiter, hreturn]
  have hle := hreturn'.minimalPeriod_le hpos
  have hperiodpos : 0 < Function.minimalPeriod g (e x) :=
    Function.minimalPeriod_pos_of_mem_periodicPts (Function.mk_mem_periodicPts hpos hreturn')
  apply Nat.le_antisymm hle
  by_contra hn
  have ht : Function.minimalPeriod g (e x) < length := Nat.lt_of_not_ge hn
  apply hshort _ hperiodpos ht
  apply e.injective
  rw [hiter]
  exact Function.isPeriodicPt_minimalPeriod g (e x)

end HodgeLean.Foundations.Program

end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers MulAction

set_option maxHeartbeats 400000

def g32p_row02_cosetEquiv : Fin 45 ≃ (g32p_G ⧸ g32p_row02_finiteSupplier.H) :=
  Equiv.ofBijective _ g32p_row02_cosetEnumeration

theorem g32p_row02_cosetBranchMap (b : Fin 3) :
    b4b_toMatrix (g32p_cosetBranches b) =
      HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega (g32p_row02_cosetBranchMatrices b)) := by
  have he : g32p_row02_cosetBranchMatrices b = g32p_cosetIntegralBranches b := by
    fin_cases b
    · exact g32p_row02_cosetBranchMatrix0
    · exact g32p_row02_cosetBranchMatrix1
    · exact g32p_row02_cosetBranchMatrix2
  rw [he]
  exact g32p_cosetBranches_map b

theorem g32p_row02_cosetBranchCheck (b : Fin 3) (i : Fin 45) :
    HurwitzPrymRex_mmul (g32p_row02_cosetBranchMatrices b) (g32p_row02_cosetRepresentatives i) =
      HurwitzPrymRex_mmul (g32p_row02_cosetRepresentatives (g32p_row02_cosetBranchNext b i))
        (g32p_row02_groupNodes (g32p_row02_cosetBranchFactor b i)) := by
  fin_cases i
  · exact g32p_row02_cosetBranchStep_0000 b
  · exact g32p_row02_cosetBranchStep_0001 b
  · exact g32p_row02_cosetBranchStep_0002 b
  · exact g32p_row02_cosetBranchStep_0003 b
  · exact g32p_row02_cosetBranchStep_0004 b
  · exact g32p_row02_cosetBranchStep_0005 b
  · exact g32p_row02_cosetBranchStep_0006 b
  · exact g32p_row02_cosetBranchStep_0007 b
  · exact g32p_row02_cosetBranchStep_0008 b
  · exact g32p_row02_cosetBranchStep_0009 b
  · exact g32p_row02_cosetBranchStep_0010 b
  · exact g32p_row02_cosetBranchStep_0011 b
  · exact g32p_row02_cosetBranchStep_0012 b
  · exact g32p_row02_cosetBranchStep_0013 b
  · exact g32p_row02_cosetBranchStep_0014 b
  · exact g32p_row02_cosetBranchStep_0015 b
  · exact g32p_row02_cosetBranchStep_0016 b
  · exact g32p_row02_cosetBranchStep_0017 b
  · exact g32p_row02_cosetBranchStep_0018 b
  · exact g32p_row02_cosetBranchStep_0019 b
  · exact g32p_row02_cosetBranchStep_0020 b
  · exact g32p_row02_cosetBranchStep_0021 b
  · exact g32p_row02_cosetBranchStep_0022 b
  · exact g32p_row02_cosetBranchStep_0023 b
  · exact g32p_row02_cosetBranchStep_0024 b
  · exact g32p_row02_cosetBranchStep_0025 b
  · exact g32p_row02_cosetBranchStep_0026 b
  · exact g32p_row02_cosetBranchStep_0027 b
  · exact g32p_row02_cosetBranchStep_0028 b
  · exact g32p_row02_cosetBranchStep_0029 b
  · exact g32p_row02_cosetBranchStep_0030 b
  · exact g32p_row02_cosetBranchStep_0031 b
  · exact g32p_row02_cosetBranchStep_0032 b
  · exact g32p_row02_cosetBranchStep_0033 b
  · exact g32p_row02_cosetBranchStep_0034 b
  · exact g32p_row02_cosetBranchStep_0035 b
  · exact g32p_row02_cosetBranchStep_0036 b
  · exact g32p_row02_cosetBranchStep_0037 b
  · exact g32p_row02_cosetBranchStep_0038 b
  · exact g32p_row02_cosetBranchStep_0039 b
  · exact g32p_row02_cosetBranchStep_0040 b
  · exact g32p_row02_cosetBranchStep_0041 b
  · exact g32p_row02_cosetBranchStep_0042 b
  · exact g32p_row02_cosetBranchStep_0043 b
  · exact g32p_row02_cosetBranchStep_0044 b

theorem g32p_row02_cosetActualBranchStep (b : Fin 3) (i : Fin 45) :
    g32p_cosetBranches b * g32p_row02_cosetActualRepresentatives i =
      g32p_row02_cosetActualRepresentatives (g32p_row02_cosetBranchNext b i) *
        (g32p_row02_groupEquiv (g32p_row02_cosetBranchFactor b i) : g32p_G) := by
  apply Subtype.ext
  change b4b_toMatrix (g32p_cosetBranches b * g32p_row02_cosetActualRepresentatives i) =
    b4b_toMatrix (g32p_row02_cosetActualRepresentatives (g32p_row02_cosetBranchNext b i) *
      (g32p_row02_groupEquiv (g32p_row02_cosetBranchFactor b i) : g32p_G))
  rw [map_mul, map_mul, g32p_row02_cosetBranchMap, g32p_row02_cosetActualRepresentatives_map,
    g32p_row02_cosetActualRepresentatives_map, g32p_row02_groupEquiv_map,
    ← map_mul, ← map_mul, ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add,
    ← HurwitzPrymRex_evM_mmul g32h_omega_sq_add, g32p_row02_cosetBranchCheck]

theorem g32p_row02_cosetQuotientStep (b : Fin 3) (i : Fin 45) :
    g32p_row02_cosetEquiv (g32p_row02_cosetBranchNext b i) = g32p_cosetBranches b • g32p_row02_cosetEquiv i := by
  change (QuotientGroup.mk (g32p_row02_cosetActualRepresentatives (g32p_row02_cosetBranchNext b i)) : g32p_G ⧸ g32p_row02_finiteSupplier.H) =
    g32p_cosetBranches b • (QuotientGroup.mk (g32p_row02_cosetActualRepresentatives i) : g32p_G ⧸ g32p_row02_finiteSupplier.H)
  rw [MulAction.Quotient.smul_coe, smul_eq_mul]
  apply QuotientGroup.eq.mpr
  rw [g32p_row02_cosetActualBranchStep, ← mul_assoc, inv_mul_cancel, one_mul]
  exact (g32p_row02_groupEquiv (g32p_row02_cosetBranchFactor b i)).property

def g32p_row02_cosetOrbitEquiv0 : Fin 21 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 0)) (g32p_G ⧸ g32p_row02_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 0) g32p_row02_cosetEquiv
    (g32p_row02_cosetBranchNext 0) (g32p_row02_cosetQuotientStep 0) g32p_row02_cosetLabels0 g32p_row02_cosetRoots0
    g32p_row02_cosetDistances0 g32p_row02_cosetRootLabels0 g32p_row02_cosetNextLabels0 g32p_row02_cosetReach0)

theorem g32p_row02_cosetPeriod0 (j : Fin 21) :
    Function.minimalPeriod ((g32p_cosetBranches 0) • ·) (g32p_row02_cosetEquiv (g32p_row02_cosetRoots0 j)) = g32p_row02_cosetLengths0 j := by
  apply g32p_period_of_cycle g32p_row02_cosetEquiv (g32p_row02_cosetBranchNext 0) ((g32p_cosetBranches 0) • ·)
    (g32p_row02_cosetQuotientStep 0) _ _ (g32p_row02_cosetPeriods0 j).1 (g32p_row02_cosetPeriods0 j).2.1
  intro t ht hlt
  exact (g32p_row02_cosetPeriods0 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row02_cosetActualMonodromy0 (j : Fin 21) :
    (g32p_cosetBranches 0) ^ g32p_row02_cosetLengths0 j * g32p_row02_cosetActualRepresentatives (g32p_row02_cosetRoots0 j) =
      g32p_row02_cosetActualRepresentatives (g32p_row02_cosetRoots0 j) *
        (g32p_row02_groupEquiv (g32p_row02_cosetMonodromies0 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row02_cosetBranchMatrices 0)
    (g32p_row02_cosetRepresentatives (g32p_row02_cosetRoots0 j))
    (g32p_row02_groupNodes (g32p_row02_cosetMonodromies0 j))
    (g32p_row02_cosetLengths0 j) (g32p_row02_cosetBranchMap 0)
    (g32p_row02_cosetActualRepresentatives_map _) (g32p_row02_groupEquiv_map _)
  fin_cases j
  · exact g32p_row02_cosetMonodromy_0_0000.1
  · exact g32p_row02_cosetMonodromy_0_0001.1
  · exact g32p_row02_cosetMonodromy_0_0002.1
  · exact g32p_row02_cosetMonodromy_0_0003.1
  · exact g32p_row02_cosetMonodromy_0_0004.1
  · exact g32p_row02_cosetMonodromy_0_0005.1
  · exact g32p_row02_cosetMonodromy_0_0006.1
  · exact g32p_row02_cosetMonodromy_0_0007.1
  · exact g32p_row02_cosetMonodromy_0_0008.1
  · exact g32p_row02_cosetMonodromy_0_0009.1
  · exact g32p_row02_cosetMonodromy_0_0010.1
  · exact g32p_row02_cosetMonodromy_0_0011.1
  · exact g32p_row02_cosetMonodromy_0_0012.1
  · exact g32p_row02_cosetMonodromy_0_0013.1
  · exact g32p_row02_cosetMonodromy_0_0014.1
  · exact g32p_row02_cosetMonodromy_0_0015.1
  · exact g32p_row02_cosetMonodromy_0_0016.1
  · exact g32p_row02_cosetMonodromy_0_0017.1
  · exact g32p_row02_cosetMonodromy_0_0018.1
  · exact g32p_row02_cosetMonodromy_0_0019.1
  · exact g32p_row02_cosetMonodromy_0_0020.1

theorem g32p_row02_cosetCharacter0 (j : Fin 21) :
    g32p_row02_finiteSupplier.χ (g32p_row02_groupEquiv (g32p_row02_cosetMonodromies0 j)) = g32p_row02_cosetExponents0 j := by
  rw [g32p_row02_finiteSupplier_value]
  fin_cases j
  · exact g32p_row02_cosetMonodromy_0_0000.2
  · exact g32p_row02_cosetMonodromy_0_0001.2
  · exact g32p_row02_cosetMonodromy_0_0002.2
  · exact g32p_row02_cosetMonodromy_0_0003.2
  · exact g32p_row02_cosetMonodromy_0_0004.2
  · exact g32p_row02_cosetMonodromy_0_0005.2
  · exact g32p_row02_cosetMonodromy_0_0006.2
  · exact g32p_row02_cosetMonodromy_0_0007.2
  · exact g32p_row02_cosetMonodromy_0_0008.2
  · exact g32p_row02_cosetMonodromy_0_0009.2
  · exact g32p_row02_cosetMonodromy_0_0010.2
  · exact g32p_row02_cosetMonodromy_0_0011.2
  · exact g32p_row02_cosetMonodromy_0_0012.2
  · exact g32p_row02_cosetMonodromy_0_0013.2
  · exact g32p_row02_cosetMonodromy_0_0014.2
  · exact g32p_row02_cosetMonodromy_0_0015.2
  · exact g32p_row02_cosetMonodromy_0_0016.2
  · exact g32p_row02_cosetMonodromy_0_0017.2
  · exact g32p_row02_cosetMonodromy_0_0018.2
  · exact g32p_row02_cosetMonodromy_0_0019.2
  · exact g32p_row02_cosetMonodromy_0_0020.2

theorem g32p_row02_cosetBranchExponents0 :
    papersExps g32p_row02_finiteSupplier.H g32p_row02_finiteSupplier.χ (g32p_cosetBranches 0) =
      (Finset.univ.val.map (fun j : Fin 21 => Multiplicative.toAdd (g32p_row02_cosetExponents0 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row02_cosetOrbitEquiv0
    (fun j => g32p_row02_cosetActualRepresentatives (g32p_row02_cosetRoots0 j)) (fun _ => rfl) g32p_row02_cosetLengths0 g32p_row02_cosetPeriod0
    (fun j => g32p_row02_groupEquiv (g32p_row02_cosetMonodromies0 j)) g32p_row02_cosetActualMonodromy0]
  simp only [g32p_row02_cosetCharacter0]
  rfl

def g32p_row02_cosetOrbitEquiv1 : Fin 21 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 1)) (g32p_G ⧸ g32p_row02_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 1) g32p_row02_cosetEquiv
    (g32p_row02_cosetBranchNext 1) (g32p_row02_cosetQuotientStep 1) g32p_row02_cosetLabels1 g32p_row02_cosetRoots1
    g32p_row02_cosetDistances1 g32p_row02_cosetRootLabels1 g32p_row02_cosetNextLabels1 g32p_row02_cosetReach1)

theorem g32p_row02_cosetPeriod1 (j : Fin 21) :
    Function.minimalPeriod ((g32p_cosetBranches 1) • ·) (g32p_row02_cosetEquiv (g32p_row02_cosetRoots1 j)) = g32p_row02_cosetLengths1 j := by
  apply g32p_period_of_cycle g32p_row02_cosetEquiv (g32p_row02_cosetBranchNext 1) ((g32p_cosetBranches 1) • ·)
    (g32p_row02_cosetQuotientStep 1) _ _ (g32p_row02_cosetPeriods1 j).1 (g32p_row02_cosetPeriods1 j).2.1
  intro t ht hlt
  exact (g32p_row02_cosetPeriods1 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row02_cosetActualMonodromy1 (j : Fin 21) :
    (g32p_cosetBranches 1) ^ g32p_row02_cosetLengths1 j * g32p_row02_cosetActualRepresentatives (g32p_row02_cosetRoots1 j) =
      g32p_row02_cosetActualRepresentatives (g32p_row02_cosetRoots1 j) *
        (g32p_row02_groupEquiv (g32p_row02_cosetMonodromies1 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row02_cosetBranchMatrices 1)
    (g32p_row02_cosetRepresentatives (g32p_row02_cosetRoots1 j))
    (g32p_row02_groupNodes (g32p_row02_cosetMonodromies1 j))
    (g32p_row02_cosetLengths1 j) (g32p_row02_cosetBranchMap 1)
    (g32p_row02_cosetActualRepresentatives_map _) (g32p_row02_groupEquiv_map _)
  fin_cases j
  · exact g32p_row02_cosetMonodromy_1_0000.1
  · exact g32p_row02_cosetMonodromy_1_0001.1
  · exact g32p_row02_cosetMonodromy_1_0002.1
  · exact g32p_row02_cosetMonodromy_1_0003.1
  · exact g32p_row02_cosetMonodromy_1_0004.1
  · exact g32p_row02_cosetMonodromy_1_0005.1
  · exact g32p_row02_cosetMonodromy_1_0006.1
  · exact g32p_row02_cosetMonodromy_1_0007.1
  · exact g32p_row02_cosetMonodromy_1_0008.1
  · exact g32p_row02_cosetMonodromy_1_0009.1
  · exact g32p_row02_cosetMonodromy_1_0010.1
  · exact g32p_row02_cosetMonodromy_1_0011.1
  · exact g32p_row02_cosetMonodromy_1_0012.1
  · exact g32p_row02_cosetMonodromy_1_0013.1
  · exact g32p_row02_cosetMonodromy_1_0014.1
  · exact g32p_row02_cosetMonodromy_1_0015.1
  · exact g32p_row02_cosetMonodromy_1_0016.1
  · exact g32p_row02_cosetMonodromy_1_0017.1
  · exact g32p_row02_cosetMonodromy_1_0018.1
  · exact g32p_row02_cosetMonodromy_1_0019.1
  · exact g32p_row02_cosetMonodromy_1_0020.1

theorem g32p_row02_cosetCharacter1 (j : Fin 21) :
    g32p_row02_finiteSupplier.χ (g32p_row02_groupEquiv (g32p_row02_cosetMonodromies1 j)) = g32p_row02_cosetExponents1 j := by
  rw [g32p_row02_finiteSupplier_value]
  fin_cases j
  · exact g32p_row02_cosetMonodromy_1_0000.2
  · exact g32p_row02_cosetMonodromy_1_0001.2
  · exact g32p_row02_cosetMonodromy_1_0002.2
  · exact g32p_row02_cosetMonodromy_1_0003.2
  · exact g32p_row02_cosetMonodromy_1_0004.2
  · exact g32p_row02_cosetMonodromy_1_0005.2
  · exact g32p_row02_cosetMonodromy_1_0006.2
  · exact g32p_row02_cosetMonodromy_1_0007.2
  · exact g32p_row02_cosetMonodromy_1_0008.2
  · exact g32p_row02_cosetMonodromy_1_0009.2
  · exact g32p_row02_cosetMonodromy_1_0010.2
  · exact g32p_row02_cosetMonodromy_1_0011.2
  · exact g32p_row02_cosetMonodromy_1_0012.2
  · exact g32p_row02_cosetMonodromy_1_0013.2
  · exact g32p_row02_cosetMonodromy_1_0014.2
  · exact g32p_row02_cosetMonodromy_1_0015.2
  · exact g32p_row02_cosetMonodromy_1_0016.2
  · exact g32p_row02_cosetMonodromy_1_0017.2
  · exact g32p_row02_cosetMonodromy_1_0018.2
  · exact g32p_row02_cosetMonodromy_1_0019.2
  · exact g32p_row02_cosetMonodromy_1_0020.2

theorem g32p_row02_cosetBranchExponents1 :
    papersExps g32p_row02_finiteSupplier.H g32p_row02_finiteSupplier.χ (g32p_cosetBranches 1) =
      (Finset.univ.val.map (fun j : Fin 21 => Multiplicative.toAdd (g32p_row02_cosetExponents1 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row02_cosetOrbitEquiv1
    (fun j => g32p_row02_cosetActualRepresentatives (g32p_row02_cosetRoots1 j)) (fun _ => rfl) g32p_row02_cosetLengths1 g32p_row02_cosetPeriod1
    (fun j => g32p_row02_groupEquiv (g32p_row02_cosetMonodromies1 j)) g32p_row02_cosetActualMonodromy1]
  simp only [g32p_row02_cosetCharacter1]
  rfl

def g32p_row02_cosetOrbitEquiv2 : Fin 29 ≃ Quotient (orbitRel (Subgroup.zpowers (g32p_cosetBranches 2)) (g32p_G ⧸ g32p_row02_finiteSupplier.H)) :=
  Equiv.ofBijective _ (g32p_cycle_orbit_bijective (g32p_cosetBranches 2) g32p_row02_cosetEquiv
    (g32p_row02_cosetBranchNext 2) (g32p_row02_cosetQuotientStep 2) g32p_row02_cosetLabels2 g32p_row02_cosetRoots2
    g32p_row02_cosetDistances2 g32p_row02_cosetRootLabels2 g32p_row02_cosetNextLabels2 g32p_row02_cosetReach2)

theorem g32p_row02_cosetPeriod2 (j : Fin 29) :
    Function.minimalPeriod ((g32p_cosetBranches 2) • ·) (g32p_row02_cosetEquiv (g32p_row02_cosetRoots2 j)) = g32p_row02_cosetLengths2 j := by
  apply g32p_period_of_cycle g32p_row02_cosetEquiv (g32p_row02_cosetBranchNext 2) ((g32p_cosetBranches 2) • ·)
    (g32p_row02_cosetQuotientStep 2) _ _ (g32p_row02_cosetPeriods2 j).1 (g32p_row02_cosetPeriods2 j).2.1
  intro t ht hlt
  exact (g32p_row02_cosetPeriods2 j).2.2 ⟨t, hlt⟩ ht

theorem g32p_row02_cosetActualMonodromy2 (j : Fin 29) :
    (g32p_cosetBranches 2) ^ g32p_row02_cosetLengths2 j * g32p_row02_cosetActualRepresentatives (g32p_row02_cosetRoots2 j) =
      g32p_row02_cosetActualRepresentatives (g32p_row02_cosetRoots2 j) *
        (g32p_row02_groupEquiv (g32p_row02_cosetMonodromies2 j) : g32p_G) := by
  apply g32p_actual_monodromy _ _ _ (g32p_row02_cosetBranchMatrices 2)
    (g32p_row02_cosetRepresentatives (g32p_row02_cosetRoots2 j))
    (g32p_row02_groupNodes (g32p_row02_cosetMonodromies2 j))
    (g32p_row02_cosetLengths2 j) (g32p_row02_cosetBranchMap 2)
    (g32p_row02_cosetActualRepresentatives_map _) (g32p_row02_groupEquiv_map _)
  fin_cases j
  · exact g32p_row02_cosetMonodromy_2_0000.1
  · exact g32p_row02_cosetMonodromy_2_0001.1
  · exact g32p_row02_cosetMonodromy_2_0002.1
  · exact g32p_row02_cosetMonodromy_2_0003.1
  · exact g32p_row02_cosetMonodromy_2_0004.1
  · exact g32p_row02_cosetMonodromy_2_0005.1
  · exact g32p_row02_cosetMonodromy_2_0006.1
  · exact g32p_row02_cosetMonodromy_2_0007.1
  · exact g32p_row02_cosetMonodromy_2_0008.1
  · exact g32p_row02_cosetMonodromy_2_0009.1
  · exact g32p_row02_cosetMonodromy_2_0010.1
  · exact g32p_row02_cosetMonodromy_2_0011.1
  · exact g32p_row02_cosetMonodromy_2_0012.1
  · exact g32p_row02_cosetMonodromy_2_0013.1
  · exact g32p_row02_cosetMonodromy_2_0014.1
  · exact g32p_row02_cosetMonodromy_2_0015.1
  · exact g32p_row02_cosetMonodromy_2_0016.1
  · exact g32p_row02_cosetMonodromy_2_0017.1
  · exact g32p_row02_cosetMonodromy_2_0018.1
  · exact g32p_row02_cosetMonodromy_2_0019.1
  · exact g32p_row02_cosetMonodromy_2_0020.1
  · exact g32p_row02_cosetMonodromy_2_0021.1
  · exact g32p_row02_cosetMonodromy_2_0022.1
  · exact g32p_row02_cosetMonodromy_2_0023.1
  · exact g32p_row02_cosetMonodromy_2_0024.1
  · exact g32p_row02_cosetMonodromy_2_0025.1
  · exact g32p_row02_cosetMonodromy_2_0026.1
  · exact g32p_row02_cosetMonodromy_2_0027.1
  · exact g32p_row02_cosetMonodromy_2_0028.1

theorem g32p_row02_cosetCharacter2 (j : Fin 29) :
    g32p_row02_finiteSupplier.χ (g32p_row02_groupEquiv (g32p_row02_cosetMonodromies2 j)) = g32p_row02_cosetExponents2 j := by
  rw [g32p_row02_finiteSupplier_value]
  fin_cases j
  · exact g32p_row02_cosetMonodromy_2_0000.2
  · exact g32p_row02_cosetMonodromy_2_0001.2
  · exact g32p_row02_cosetMonodromy_2_0002.2
  · exact g32p_row02_cosetMonodromy_2_0003.2
  · exact g32p_row02_cosetMonodromy_2_0004.2
  · exact g32p_row02_cosetMonodromy_2_0005.2
  · exact g32p_row02_cosetMonodromy_2_0006.2
  · exact g32p_row02_cosetMonodromy_2_0007.2
  · exact g32p_row02_cosetMonodromy_2_0008.2
  · exact g32p_row02_cosetMonodromy_2_0009.2
  · exact g32p_row02_cosetMonodromy_2_0010.2
  · exact g32p_row02_cosetMonodromy_2_0011.2
  · exact g32p_row02_cosetMonodromy_2_0012.2
  · exact g32p_row02_cosetMonodromy_2_0013.2
  · exact g32p_row02_cosetMonodromy_2_0014.2
  · exact g32p_row02_cosetMonodromy_2_0015.2
  · exact g32p_row02_cosetMonodromy_2_0016.2
  · exact g32p_row02_cosetMonodromy_2_0017.2
  · exact g32p_row02_cosetMonodromy_2_0018.2
  · exact g32p_row02_cosetMonodromy_2_0019.2
  · exact g32p_row02_cosetMonodromy_2_0020.2
  · exact g32p_row02_cosetMonodromy_2_0021.2
  · exact g32p_row02_cosetMonodromy_2_0022.2
  · exact g32p_row02_cosetMonodromy_2_0023.2
  · exact g32p_row02_cosetMonodromy_2_0024.2
  · exact g32p_row02_cosetMonodromy_2_0025.2
  · exact g32p_row02_cosetMonodromy_2_0026.2
  · exact g32p_row02_cosetMonodromy_2_0027.2
  · exact g32p_row02_cosetMonodromy_2_0028.2

theorem g32p_row02_cosetBranchExponents2 :
    papersExps g32p_row02_finiteSupplier.H g32p_row02_finiteSupplier.χ (g32p_cosetBranches 2) =
      (Finset.univ.val.map (fun j : Fin 29 => Multiplicative.toAdd (g32p_row02_cosetExponents2 j))).filter (· ≠ 0) := by
  rw [g32p_exps_of_orbit_enumeration _ _ _ g32p_row02_cosetOrbitEquiv2
    (fun j => g32p_row02_cosetActualRepresentatives (g32p_row02_cosetRoots2 j)) (fun _ => rfl) g32p_row02_cosetLengths2 g32p_row02_cosetPeriod2
    (fun j => g32p_row02_groupEquiv (g32p_row02_cosetMonodromies2 j)) g32p_row02_cosetActualMonodromy2]
  simp only [g32p_row02_cosetCharacter2]
  rfl

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers

set_option maxHeartbeats 400000

theorem g32p_row02_exponents :
    (g32p_exponents g32p_row02_finiteSupplier).Perm (expandExps [(3, 12)]) := by
  have h0 : papersExps g32p_row02_finiteSupplier.H g32p_row02_finiteSupplier.χ (g32p_classDatum 0) = 0 := by
    change papersExps g32p_row02_finiteSupplier.H g32p_row02_finiteSupplier.χ (g32p_cosetBranches 0) = _
    rw [g32p_row02_cosetBranchExponents0]
    change ((Finset.univ : Finset (Fin 21)).val.map
      (fun j => Multiplicative.toAdd (g32p_row02_cosetExponents0 j))).filter (· ≠ 0) = 0
    decide +kernel
  have h1 : papersExps g32p_row02_finiteSupplier.H g32p_row02_finiteSupplier.χ (g32p_classDatum 6) = 0 := by
    change papersExps g32p_row02_finiteSupplier.H g32p_row02_finiteSupplier.χ (g32p_cosetBranches 1) = _
    rw [g32p_row02_cosetBranchExponents1]
    change ((Finset.univ : Finset (Fin 21)).val.map
      (fun j => Multiplicative.toAdd (g32p_row02_cosetExponents1 j))).filter (· ≠ 0) = 0
    decide +kernel
  have h2 : papersExps g32p_row02_finiteSupplier.H g32p_row02_finiteSupplier.χ (g32p_classDatum 12) = Multiset.replicate 12 (3 : ZMod 6) := by
    change papersExps g32p_row02_finiteSupplier.H g32p_row02_finiteSupplier.χ (g32p_cosetBranches 2) = _
    rw [g32p_row02_cosetBranchExponents2]
    change ((Finset.univ : Finset (Fin 29)).val.map
      (fun j => Multiplicative.toAdd (g32p_row02_cosetExponents2 j))).filter (· ≠ 0) = Multiset.replicate 12 (3 : ZMod 6)
    decide +kernel
  have hs : papersExpsTuple g32p_row02_finiteSupplier.H g32p_row02_finiteSupplier.χ g32p_classList =
      Multiset.replicate 12 (3 : ZMod 6) := by
    have hc : g32p_classList = List.replicate 6 (g32p_classDatum 0) ++
        List.replicate 6 (g32p_classDatum 6) ++ [g32p_classDatum 12] := rfl
    simp only [papersExpsTuple, hc, List.map_append, List.map_replicate,
      List.map_cons, List.map_nil, List.sum_append, List.sum_replicate,
      List.sum_cons, List.sum_nil, List.sum_singleton, h0, h1, h2, nsmul_zero, zero_add, add_zero]
    rfl
  apply Multiset.coe_eq_coe.mp
  change (((papersExpsTuple _ _ _).map ZMod.val).toList : Multiset ℕ) = _
  rw [Multiset.coe_toList, hs]
  change (Multiset.replicate 12 (3 : ZMod 6)).map ZMod.val = ↑(expandExps [(3, 12)])
  decide +kernel

theorem g32p_row02_finiteSupplier_table :
    ∃ r ∈ g32WitnessTable, r.i = 2 ∧ r.m = g32p_row02_finiteSupplier.m ∧
      r.orderH = Nat.card g32p_row02_finiteSupplier.H ∧
      (g32p_exponents g32p_row02_finiteSupplier).Perm (expandExps r.exps) := by
  refine ⟨⟨2, (-1), 3456, 6, 108, 12, 226, some 3, [(3, 12)], .S⟩,
    ?_, rfl, rfl, g32p_row02_finiteSupplier_order.symm, g32p_row02_exponents⟩
  decide

def g32p_row02_complexWitness : g32p_row02_finiteSupplier.H →* ℂˣ := g32p_complexCharacter g32p_row02_finiteSupplier

theorem g32p_row02_supplierWitness :
    ∃ (S : g32p_Supplier) (χc : S.H →* ℂˣ),
      (∀ h, (χc h : ℂ) = g32p_root S.m ^ (Multiplicative.toAdd (S.χ h)).val) ∧
      (∃ r ∈ g32WitnessTable, r.i = 2 ∧ r.m = S.m ∧
        r.orderH = Nat.card S.H ∧ (g32p_exponents S).Perm (expandExps r.exps)) := by
  exact ⟨g32p_row02_finiteSupplier, g32p_row02_complexWitness, g32p_complexCharacter_apply _,
    g32p_row02_finiteSupplier_table⟩

end HodgeLean.Foundations.Program

end
end
