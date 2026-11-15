import HodgeLean.Foundations.Program.G32PropFourSixPacked0201
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019
import HodgeLean.Foundations.Program.G32PropFourSixPacked0191
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixPacked0187
import HodgeLean.Foundations.Program.G32PropFourSixPacked0202
import HodgeLean.Foundations.Program.G32PropFourSixPacked0203
import HodgeLean.Foundations.Program.G32PropFourSixPacked0204
import HodgeLean.Foundations.Program.G32PropFourSixPacked0205
import HodgeLean.Foundations.Program.G32PropFourSixPacked0206

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound100_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 27, 31, 32, 33, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 47, 48, 49, 53, 54, 55, 58, 59, 61, 62, 63, 65, 66, 67, 70, 72, 73, 75, 76, 77, 78, 80, 81, 82, 83, 84, 86, 87, 88, 89, 90, 94, 95, 96, 99, 100, 102, 103, 104, 106, 107, 108, 111, 113, 114, 116, 117, 118, 119, 121, 122, 123, 124, 125, 129, 131, 132, 136, 138, 139, 143, 144, 146, 149, 151, 152, 153, 155, 156, 157, 160, 162, 163, 165, 166, 167, 168, 170, 171, 172, 173, 174, 177, 179, 180, 184, 186, 187, 190, 191, 193, 196, 197, 198, 200, 201, 202, 203, 204, 206, 207, 208, 209, 210, 211, 212, 214, 216, 217, 219, 221, 224, 225, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239}

def g32p_centralizerBound100_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (1, 3), (7, 8), (10, 5), (12, 7), (14, 5), (15, 7), (19, 0), (23, 4), (27, 4), (32, 4), (33, 6), (36, 1), (37, 2), (39, 2), (41, 6), (48, 6), (50, 2), (52, 6), (60, 5), (62, 2), (63, 7), (66, 0), (71, 1)}

theorem g32p_centralizerBound100_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) := by
  decide +kernel

theorem g32p_centralizerBound100_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) := by
  decide +kernel

theorem g32p_centralizerBound100_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) := by
  decide +kernel

theorem g32p_centralizerBound100_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) := by
  decide +kernel

theorem g32p_centralizerBound100_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) := by
  decide +kernel

theorem g32p_centralizerBound100_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) := by
  decide +kernel

theorem g32p_centralizerBound100_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) := by
  decide +kernel

theorem g32p_centralizerBound100_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) := by
  decide +kernel

theorem g32p_centralizerBound100_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) := by
  decide +kernel

theorem g32p_centralizerBound100_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) := by
  decide +kernel

theorem g32p_centralizerBound100_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) := by
  decide +kernel

theorem g32p_centralizerBound100_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) := by
  decide +kernel

theorem g32p_centralizerBound100_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) := by
  decide +kernel

theorem g32p_centralizerBound100_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) := by
  decide +kernel

theorem g32p_centralizerBound100_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) := by
  decide +kernel

theorem g32p_centralizerBound100_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 100) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound100_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound100_point_block00 t
  · exact g32p_centralizerBound100_point_block01 t
  · exact g32p_centralizerBound100_point_block02 t
  · exact g32p_centralizerBound100_point_block03 t
  · exact g32p_centralizerBound100_point_block04 t
  · exact g32p_centralizerBound100_point_block05 t
  · exact g32p_centralizerBound100_point_block06 t
  · exact g32p_centralizerBound100_point_block07 t
  · exact g32p_centralizerBound100_point_block08 t
  · exact g32p_centralizerBound100_point_block09 t
  · exact g32p_centralizerBound100_point_block10 t
  · exact g32p_centralizerBound100_point_block11 t
  · exact g32p_centralizerBound100_point_block12 t
  · exact g32p_centralizerBound100_point_block13 t
  · exact g32p_centralizerBound100_point_block14 t

theorem g32p_centralizerBound100_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 100) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 100)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound100_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound100_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 100) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 100)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound100_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound100_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 100) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 100)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound100_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound100_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 100) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 100)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound100_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound100_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 100) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 100)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound100_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound100_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 100) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 100) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound100_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 100) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 100)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound100_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound100_stabilizer_block00 t r
  · exact g32p_centralizerBound100_stabilizer_block01 t r
  · exact g32p_centralizerBound100_stabilizer_block02 t r
  · exact g32p_centralizerBound100_stabilizer_block03 t r
  · exact g32p_centralizerBound100_stabilizer_block04 t r

theorem g32p_centralizerBound100_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 100}) ≤ g32p_literalCentralizer 100 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 100 g32p_centralizerBound100_points
    g32p_centralizerBound100_stabilizers ?_ g32p_centralizerBound100_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound100_point_mem i (g32p_centralizer_point_moments 100 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
open scoped Classical
set_option maxHeartbeats 400000

def g32p_conjugationFiberEquiv_of_eq {G : Type*} [Group G] (g y a : G)
    (ha : a * g * a⁻¹ = y) :
    {x : G // x * g * x⁻¹ = y} ≃ Subgroup.centralizer {g} where
  toFun x := ⟨a⁻¹ * x, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      (a⁻¹ * x.val) * g * (a⁻¹ * x.val)⁻¹ = a⁻¹ * (x.val * g * x.val⁻¹) * a := by group
      _ = a⁻¹ * y * a := by rw [x.property]
      _ = g := by rw [← ha]; group⟩
  invFun z := ⟨a * z, by
    have hz := Subgroup.mem_centralizer_singleton_iff.mp z.property
    calc
      (a * z.val) * g * (a * z.val)⁻¹ = a * (z.val * g * z.val⁻¹) * a⁻¹ := by group
      _ = a * g * a⁻¹ := by rw [hz]; group
      _ = y := ha⟩
  left_inv x := by apply Subtype.ext; change a * (a⁻¹ * x.val) = x.val; group
  right_inv z := by apply Subtype.ext; change a⁻¹ * (a * z.val) = z.val; group

theorem g32p_conjugationFiber_card_general {G : Type*} [Group G] (g y : G) :
    Nat.card {x : G // x * g * x⁻¹ = y} =
      if IsConj g y then Nat.card (Subgroup.centralizer {g}) else 0 := by
  classical
  by_cases h : IsConj g y
  · rw [ite_eq_left h]
    obtain ⟨a, ha⟩ := isConj_iff.mp h
    exact Nat.card_congr (g32p_conjugationFiberEquiv_of_eq g y a ha)
  · rw [ite_eq_right h]
    have : IsEmpty {x : G // x * g * x⁻¹ = y} :=
      ⟨fun x => h (isConj_iff.mpr ⟨x.val, x.property⟩)⟩
    exact Nat.card_of_isEmpty

theorem g32p_conjugation_sum {G : Type*} [Group G] [Fintype G]
    (g : G) (f : G → ℂ) :
    ∑ x : G, f (x * g * x⁻¹) =
      (Nat.card (Subgroup.centralizer {g}) : ℂ) *
        ∑ y : G, if IsConj g y then f y else 0 := by
  classical
  rw [← Fintype.sum_fiberwise' (fun x : G => x * g * x⁻¹) f, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_eq_nat_card, g32p_conjugationFiber_card_general]
  by_cases h : IsConj g y <;> simp only [h, ite_true, ite_false, Nat.cast_zero, zero_mul, mul_zero]

theorem g32p_coinduced_character_by_supplier {G : Type} [Group G] [Fintype G]
    (H : Subgroup G) (χ : H →* ℂˣ) (g : G) :
    (g32p_coinduced H χ).character g =
      (Nat.card H : ℂ)⁻¹ * (Nat.card (Subgroup.centralizer {g}) : ℂ) *
        ∑ h : H, if IsConj g (h : G) then (χ h : ℂ) else 0 := by
  classical
  rw [g32p_coinduced_character_direct]
  let f : G → ℂ := fun y => if hy : y ∈ H then (χ ⟨y, hy⟩ : ℂ) else 0
  change (Nat.card H : ℂ)⁻¹ * ∑ x : G, f (x * g * x⁻¹) = _
  rw [g32p_conjugation_sum, ← mul_assoc]
  congr 1
  apply Finset.sum_congr_set (H : Set G)
  · intro y hy
    exact congrArg (fun z : ℂ => if IsConj g y then z else 0)
      (show f y = (χ ⟨y, hy⟩ : ℂ) from dif_pos hy)
  · intro y hy
    calc
      (if IsConj g y then f y else 0) = (if IsConj g y then (0 : ℂ) else 0) :=
        congrArg (fun z : ℂ => if IsConj g y then z else 0)
          (show f y = 0 from dif_neg hy)
      _ = 0 := by split <;> rfl

theorem g32p_coinduced_character_by_enumeration {G : Type} [Group G] [Fintype G]
    {n : ℕ} (H : Subgroup G) (χ : H →* ℂˣ) (g : G) (e : Fin n ≃ H)
    (classify : Fin n → Fin 102) (c : Fin 102)
    (hclass : ∀ j, IsConj g (e j : G) ↔ classify j = c) :
    (g32p_coinduced H χ).character g =
      (Nat.card H : ℂ)⁻¹ * (Nat.card (Subgroup.centralizer {g}) : ℂ) *
        ∑ j : Fin n, if classify j = c then (χ (e j) : ℂ) else 0 := by
  classical
  rw [g32p_coinduced_character_by_supplier]
  congr 1
  rw [← e.sum_comp (fun h : H => if IsConj g (h : G) then (χ h : ℂ) else 0)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [hclass j]

theorem g32p_literal_centralizer_card_of_class_card (c : Fin 102)
    (hc : Nat.card (conjugatesOf (g32p_literalRepresentative c)) = g32p_literalSize c) :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative c}) = g32p_literalCentralizer c := by
  have h := (Subgroup.centralizer {g32p_literalRepresentative c}).index_mul_card
  rw [Subgroup.index_centralizer_eq_ncard, ← Nat.card_coe_set_eq, hc] at h
  have hG : Nat.card g32p_G = 155520 :=
    (Nat.card_coe_set_eq (g32h_G : Set (Matrix (Fin 4) (Fin 4) ℂ))).trans
      HurwitzPrymRex_g32_ncard
  rw [hG] at h
  have hm := g32p_literalSize_mul_centralizer c
  have hp : 0 < g32p_literalSize c := by
    by_contra hn
    have hz : g32p_literalSize c = 0 := by omega
    rw [hz, zero_mul] at hm
    contradiction
  exact Nat.eq_of_mul_eq_mul_left hp (h.trans hm.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
open scoped Classical
set_option maxHeartbeats 400000

theorem g32p_literal_class_cardinalities_of_centralizer_bounds
    (hbound : ∀ c, Nat.card (Subgroup.centralizer {g32p_literalRepresentative c}) ≤
      g32p_literalCentralizer c) :
    ∀ c, Nat.card (conjugatesOf (g32p_literalRepresentative c)) = g32p_literalSize c := by
  have hG : Nat.card g32p_G = 155520 :=
    (Nat.card_coe_set_eq (g32h_G : Set (Matrix (Fin 4) (Fin 4) ℂ))).trans
      HurwitzPrymRex_g32_ncard
  have hle (c : Fin 102) : g32p_literalSize c ≤
      Nat.card (conjugatesOf (g32p_literalRepresentative c)) := by
    have h := (Subgroup.centralizer {g32p_literalRepresentative c}).index_mul_card
    rw [Subgroup.index_centralizer_eq_ncard, ← Nat.card_coe_set_eq, hG] at h
    have hm := g32p_literalSize_mul_centralizer c
    have hp : 0 < g32p_literalCentralizer c := by
      by_contra hn
      have hz : g32p_literalCentralizer c = 0 := by omega
      rw [hz, mul_zero] at hm
      contradiction
    apply Nat.le_of_mul_le_mul_right (c := g32p_literalCentralizer c) ?_ hp
    calc
      g32p_literalSize c * g32p_literalCentralizer c = 155520 := hm
      _ = Nat.card (conjugatesOf (g32p_literalRepresentative c)) *
          Nat.card (Subgroup.centralizer {g32p_literalRepresentative c}) := h.symm
      _ ≤ _ := Nat.mul_le_mul_left _ (hbound c)
  let f : (Σ c : Fin 102, conjugatesOf (g32p_literalRepresentative c)) → g32p_G :=
    fun x => x.2.val
  have hi : Function.Injective f := by
    rintro ⟨c, g⟩ ⟨d, h⟩ he
    have he' : g.val = h.val := he
    have hg : IsConj (g32p_literalRepresentative c) h.val := he' ▸ g.property
    have hcd : c = d := g32p_literalRepresentative_classes_injective
      (ConjClasses.mk_eq_mk_iff_isConj.mpr (hg.trans h.property.symm))
    subst d
    congr 1
    exact Subtype.ext he'
  have hsum : (∑ c : Fin 102, Nat.card (conjugatesOf (g32p_literalRepresentative c))) ≤
      155520 := by
    simpa only [Nat.card_sigma, hG] using Nat.card_le_card_of_injective f hi
  intro c
  by_contra hn
  have hstrict := Finset.sum_lt_sum (s := Finset.univ)
    (fun i _ => hle i)
    ⟨c, Finset.mem_univ c, lt_of_le_of_ne (hle c) (Ne.symm hn)⟩
  rw [← List.sum_ofFn, g32p_literalSize_sum] at hstrict
  omega

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

open HodgeLean.Papers
open scoped Classical

set_option maxHeartbeats 400000

theorem g32p_conjugatesOf_eq_singleton_of_commute {G : Type*} [Group G]
    (a : G) (ha : ∀ g, Commute a g) : conjugatesOf a = {a} := by
  ext b
  change IsConj a b ↔ b = a
  constructor
  · rintro ⟨u, hu⟩
    have hc := ha (u : G)
    have he : (u : G) * a = a * (u : G) := hc.eq.symm
    have h := hu
    change (u : G) * a = b * (u : G) at h
    rw [he] at h
    exact (mul_right_cancel h).symm
  · rintro rfl
    exact IsConj.refl _

theorem g32p_conjugatesOf_card_of_scalar (a : g32p_G) (z : ℂ)
    (ha : b4b_toMatrix a = Matrix.scalar (Fin 4) z) :
    Nat.card (conjugatesOf a) = 1 := by
  have hc : ∀ g : g32p_G, Commute a g := by
    intro g
    apply Subtype.val_injective
    change b4b_toMatrix (a * g) = b4b_toMatrix (g * a)
    rw [map_mul, map_mul, ha]
    exact Matrix.scalar_comm z (Commute.all z) _
  rw [g32p_conjugatesOf_eq_singleton_of_commute a hc]
  exact Nat.card_unique

theorem g32p_g32conj_scalar (z : ℂ) :
    HurwitzPrymRex_g32conj (Matrix.scalar (Fin 4) z) = Matrix.scalar (Fin 4) z := by
  change HurwitzPrymRex_g32P * Matrix.scalar (Fin 4) z * HurwitzPrymRex_g32Pinv = _
  rw [← Matrix.scalar_comm z (Commute.all z), mul_assoc,
    HurwitzPrymRex_g32_P_Pinv, mul_one]

theorem g32p_literalRepresentative_card_of_scalar (c : Fin 102)
    (z : HurwitzPrymRex_Zw)
    (h : g32p_literalRepresentativeMatrix c = fun i j =>
      if i = j then z else ⟨0, 0⟩) :
    Nat.card (conjugatesOf (g32p_literalRepresentative c)) = 1 := by
  apply g32p_conjugatesOf_card_of_scalar _ (HurwitzPrymRex_ev g32h_omega z)
  change b4b_toMatrix (g32p_archiveWord (g32p_literalRepresentativeWord c)) = _
  rw [g32p_archiveIntegralWord_map, g32p_literalRepresentative_integral, h]
  have he : HurwitzPrymRex_evM g32h_omega
      (fun i j : Fin 4 => if i = j then z else ⟨0, 0⟩) =
      Matrix.scalar (Fin 4) (HurwitzPrymRex_ev g32h_omega z) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [HurwitzPrymRex_evM, Matrix.of_apply, ite_true, Matrix.scalar_apply,
        Matrix.diagonal_apply_eq]
    · simp only [HurwitzPrymRex_evM, Matrix.of_apply, ite_eq_right hij, Matrix.scalar_apply,
        Matrix.diagonal_apply_ne _ hij, HurwitzPrymRex_ev, Int.cast_zero,
        zero_mul, add_zero]
  rw [he, g32p_g32conj_scalar]

end HodgeLean.Foundations.Program

end
end

section

noncomputable section

namespace HodgeLean.Foundations.Program

set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_literalClass_card_000 :
    Nat.card (conjugatesOf (g32p_literalRepresentative 0)) =
      g32p_literalSize 0 := by
  change Nat.card (conjugatesOf (g32p_literalRepresentative 0)) = 1
  apply g32p_literalRepresentative_card_of_scalar 0 ⟨1, 0⟩
  decide +kernel

theorem g32p_literalClass_card_037 :
    Nat.card (conjugatesOf (g32p_literalRepresentative 37)) =
      g32p_literalSize 37 := by
  change Nat.card (conjugatesOf (g32p_literalRepresentative 37)) = 1
  apply g32p_literalRepresentative_card_of_scalar 37 ⟨1, 1⟩
  decide +kernel

theorem g32p_literalClass_card_096 :
    Nat.card (conjugatesOf (g32p_literalRepresentative 96)) =
      g32p_literalSize 96 := by
  change Nat.card (conjugatesOf (g32p_literalRepresentative 96)) = 1
  apply g32p_literalRepresentative_card_of_scalar 96 ⟨0, 1⟩
  decide +kernel

theorem g32p_literalClass_card_097 :
    Nat.card (conjugatesOf (g32p_literalRepresentative 97)) =
      g32p_literalSize 97 := by
  change Nat.card (conjugatesOf (g32p_literalRepresentative 97)) = 1
  apply g32p_literalRepresentative_card_of_scalar 97 ⟨0, -1⟩
  decide +kernel

theorem g32p_literalClass_card_099 :
    Nat.card (conjugatesOf (g32p_literalRepresentative 99)) =
      g32p_literalSize 99 := by
  change Nat.card (conjugatesOf (g32p_literalRepresentative 99)) = 1
  apply g32p_literalRepresentative_card_of_scalar 99 ⟨-1, 0⟩
  decide +kernel

theorem g32p_literalClass_card_101 :
    Nat.card (conjugatesOf (g32p_literalRepresentative 101)) =
      g32p_literalSize 101 := by
  change Nat.card (conjugatesOf (g32p_literalRepresentative 101)) = 1
  apply g32p_literalRepresentative_card_of_scalar 101 ⟨-1, -1⟩
  decide +kernel

theorem g32p_literalClass_card_of_size_one (c : Fin 102)
    (h : g32p_literalSize c = 1) :
    Nat.card (conjugatesOf (g32p_literalRepresentative c)) = g32p_literalSize c := by
  have hc : c = 0 ∨ c = 37 ∨ c = 96 ∨ c = 97 ∨ c = 99 ∨ c = 101 := by
    revert h
    fin_cases c <;> decide +kernel
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact g32p_literalClass_card_000
  · exact g32p_literalClass_card_037
  · exact g32p_literalClass_card_096
  · exact g32p_literalClass_card_097
  · exact g32p_literalClass_card_099
  · exact g32p_literalClass_card_101

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

theorem g32p_literalCentralizer_bound (c : Fin 102) :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative c}) ≤ g32p_literalCentralizer c := by
  fin_cases c
  · exact (g32p_literal_centralizer_card_of_class_card 0 g32p_literalClass_card_000).le
  · exact g32p_centralizerBound001_actual
  · exact g32p_centralizerBound002_actual
  · exact g32p_centralizerBound003_actual
  · exact g32p_centralizerBound004_actual
  · exact g32p_centralizerBound005_actual
  · exact g32p_centralizerBound006_actual
  · exact g32p_centralizerBound007_actual
  · exact g32p_centralizerBound008_actual
  · exact g32p_centralizerBound009_actual
  · exact g32p_centralizerBound010_actual
  · exact g32p_centralizerBound011_actual
  · exact g32p_centralizerBound012_actual
  · exact g32p_centralizerBound013_actual
  · exact g32p_centralizerBound014_actual
  · exact g32p_centralizerBound015_actual
  · exact g32p_centralizerBound016_actual
  · exact g32p_centralizerBound017_actual
  · exact g32p_centralizerBound018_actual
  · exact g32p_centralizerBound019_actual
  · exact g32p_centralizerBound020_actual
  · exact g32p_centralizerBound021_actual
  · exact g32p_centralizerBound022_actual
  · exact g32p_centralizerBound023_actual
  · exact g32p_centralizerBound024_actual
  · exact g32p_centralizerBound025_actual
  · exact g32p_centralizerBound026_actual
  · exact g32p_centralizerBound027_actual
  · exact g32p_centralizerBound028_actual
  · exact g32p_centralizerBound029_actual
  · exact g32p_centralizerBound030_actual
  · exact g32p_centralizerBound031_actual
  · exact g32p_centralizerBound032_actual
  · exact g32p_centralizerBound033_actual
  · exact g32p_centralizerBound034_actual
  · exact g32p_centralizerBound035_actual
  · exact g32p_centralizerBound036_actual
  · exact (g32p_literal_centralizer_card_of_class_card 37 g32p_literalClass_card_037).le
  · exact g32p_centralizerBound038_actual
  · exact g32p_centralizerBound039_actual
  · exact g32p_centralizerBound040_actual
  · exact g32p_centralizerBound041_actual
  · exact g32p_centralizerBound042_actual
  · exact g32p_centralizerBound043_actual
  · exact g32p_centralizerBound044_actual
  · exact g32p_centralizerBound045_actual
  · exact g32p_centralizerBound046_actual
  · exact g32p_centralizerBound047_actual
  · exact g32p_centralizerBound048_actual
  · exact g32p_centralizerBound049_actual
  · exact g32p_centralizerBound050_actual
  · exact g32p_centralizerBound051_actual
  · exact g32p_centralizerBound052_actual
  · exact g32p_centralizerBound053_actual
  · exact g32p_centralizerBound054_actual
  · exact g32p_centralizerBound055_actual
  · exact g32p_centralizerBound056_actual
  · exact g32p_centralizerBound057_actual
  · exact g32p_centralizerBound058_actual
  · exact g32p_centralizerBound059_actual
  · exact g32p_centralizerBound060_actual
  · exact g32p_centralizerBound061_actual
  · exact g32p_centralizerBound062_actual
  · exact g32p_centralizerBound063_actual
  · exact g32p_centralizerBound064_actual
  · exact g32p_centralizerBound065_actual
  · exact g32p_centralizerBound066_actual
  · exact g32p_centralizerBound067_actual
  · exact g32p_centralizerBound068_actual
  · exact g32p_centralizerBound069_actual
  · exact g32p_centralizerBound070_actual
  · exact g32p_centralizerBound071_actual
  · exact g32p_centralizerBound072_actual
  · exact g32p_centralizerBound073_actual
  · exact g32p_centralizerBound074_actual
  · exact g32p_centralizerBound075_actual
  · exact g32p_centralizerBound076_actual
  · exact g32p_centralizerBound077_actual
  · exact g32p_centralizerBound078_actual
  · exact g32p_centralizerBound079_actual
  · exact g32p_centralizerBound080_actual
  · exact g32p_centralizerBound081_actual
  · exact g32p_centralizerBound082_actual
  · exact g32p_centralizerBound083_actual
  · exact g32p_centralizerBound084_actual
  · exact g32p_centralizerBound085_actual
  · exact g32p_centralizerBound086_actual
  · exact g32p_centralizerBound087_actual
  · exact g32p_centralizerBound088_actual
  · exact g32p_centralizerBound089_actual
  · exact g32p_centralizerBound090_actual
  · exact g32p_centralizerBound091_actual
  · exact g32p_centralizerBound092_actual
  · exact g32p_centralizerBound093_actual
  · exact g32p_centralizerBound094_actual
  · exact g32p_centralizerBound095_actual
  · exact (g32p_literal_centralizer_card_of_class_card 96 g32p_literalClass_card_096).le
  · exact (g32p_literal_centralizer_card_of_class_card 97 g32p_literalClass_card_097).le
  · exact g32p_centralizerBound098_actual
  · exact (g32p_literal_centralizer_card_of_class_card 99 g32p_literalClass_card_099).le
  · exact g32p_centralizerBound100_actual
  · exact (g32p_literal_centralizer_card_of_class_card 101 g32p_literalClass_card_101).le

theorem g32p_literalClass_card (c : Fin 102) :
    Nat.card (conjugatesOf (g32p_literalRepresentative c)) = g32p_literalSize c :=
  g32p_literal_class_cardinalities_of_centralizer_bounds g32p_literalCentralizer_bound c

theorem g32p_literalCentralizer_card (c : Fin 102) :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative c}) = g32p_literalCentralizer c :=
  g32p_literal_centralizer_card_of_class_card c (g32p_literalClass_card c)

theorem g32p_literal_class_coverage :
    ∃ classify : g32p_G → Fin 102, ∀ g, IsConj g (g32p_literalRepresentative (classify g)) :=
  g32p_literal_class_coverage_of_cardinalities g32p_literalClass_card

theorem g32p_literal_class_fibres :
    ∃ classify : g32p_G → Fin 102,
      (∀ g, IsConj g (g32p_literalRepresentative (classify g))) ∧
      ∀ c, Nat.card {g : g32p_G // classify g = c} = g32p_literalSize c :=
  g32p_literal_class_fibres_of_cardinalities g32p_literalClass_card

end HodgeLean.Foundations.Program

end
end
