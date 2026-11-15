import HodgeLean.Foundations.Program.SchoenTowerInvariantLifting
import Mathlib.Algebra.Group.Subgroup.Finite

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

namespace HodgeLean.Foundations.Program

/-- A factor-selecting element lifts stabilizer-fixed elements to group-fixed elements
by a weighted trace.
Source: Serre, Linear Representations of Finite Groups, Chapter 1, Section 2, averaging. -/
theorem s2t_stabilizer_trace_lift {K B C G : Type*}
    [Field K] [CharZero K] [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G K B]
    (H : Subgroup G) [Fintype H] [MulSemiringAction H C] [SMulCommClass H K C]
    (f : B →ₐ[K] C) (hsurj : Function.Surjective f)
    (heq : ∀ (h : H) (a : B), f ((h : G) • a) = h • f a)
    (e : B) (hsel_in : ∀ g ∈ H, f (g • e) = 1)
    (hsel_out : ∀ g ∉ H, f (g • e) = 0)
    (b : FixedPoints.subalgebra K C H) :
    ∃ a : FixedPoints.subalgebra K B G, f a = (b : C) := by
  classical
  obtain ⟨a, ha⟩ := hsurj (b : C)
  let t : B := ∑ g : G, g • (e * a)
  have ht (g : G) : g • t = t := by
    dsimp [t]
    rw [Finset.smul_sum]
    simp only [smul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft g) (fun h : G => h • (e * a))
  have hterm (g : G) : f (g • (e * a)) = if g ∈ H then (b : C) else 0 := by
    rw [smul_mul', map_mul]
    by_cases hg : g ∈ H
    · rw [if_pos hg, hsel_in g hg, one_mul]
      calc
        f (g • a) = (⟨g, hg⟩ : H) • f a := heq ⟨g, hg⟩ a
        _ = (b : C) := by
          rw [ha]
          exact (FixedPoints.mem_subalgebra.mp b.property) ⟨g, hg⟩
    · rw [if_neg hg, hsel_out g hg, zero_mul]
  have hft : f t = (Fintype.card H : K) • (b : C) := by
    dsimp [t]
    rw [map_sum]
    simp only [hterm]
    rw [← Finset.sum_filter, Finset.sum_const,
      ← Fintype.card_subtype (fun g : G => g ∈ H), Nat.cast_smul_eq_nsmul]
  refine ⟨⟨(Fintype.card H : K)⁻¹ • t, ?_⟩, ?_⟩
  · intro g
    rw [smul_comm, ht]
  · change f ((Fintype.card H : K)⁻¹ • t) = (b : C)
    rw [map_smul, hft, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_smul]

/-- Projection to a factor sends group invariants to stabilizer invariants. -/
def s2t_stabilizerFixedMap {K B C G : Type*}
    [Field K] [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    [Group G] [MulSemiringAction G B] [SMulCommClass G K B]
    (H : Subgroup G) [MulSemiringAction H C] [SMulCommClass H K C]
    (f : B →ₐ[K] C)
    (heq : ∀ (h : H) (a : B), f ((h : G) • a) = h • f a) :
    FixedPoints.subalgebra K B G →+* FixedPoints.subalgebra K C H := by
  refine (f.toRingHom.comp (FixedPoints.subalgebra K B G).toSubring.subtype).codRestrict _ ?_
  intro a h
  change h • f (a : B) = f (a : B)
  rw [← heq]
  exact congrArg f (((FixedPoints.mem_subalgebra (A := K)).mp a.property) h.val)

/-- A selecting factor detects group invariants when its translates span the unit. -/
theorem s2t_stabilizerFixedMap_injective {K B C G : Type*}
    [Field K] [CharZero K] [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G K B]
    (H : Subgroup G) [Fintype H] [MulSemiringAction H C] [SMulCommClass H K C]
    (f : B →ₐ[K] C)
    (heq : ∀ (h : H) (a : B), f ((h : G) • a) = h • f a)
    (e : B) (hker : ∀ a : B, f a = 0 → e * a = 0)
    (htrace : ∑ g : G, g • e = (Fintype.card H : K) • (1 : B)) :
    Function.Injective (s2t_stabilizerFixedMap H f heq) := by
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have hfa : f (a : B) = 0 := congrArg Subtype.val ha
  have hea := hker (a : B) hfa
  have htrans (g : G) : (g • e) * (a : B) = 0 := by
    have h := congrArg (fun b : B => g • b) hea
    simpa only [smul_mul', ((FixedPoints.mem_subalgebra (A := K)).mp a.property) g, smul_zero] using h
  have hz : (Fintype.card H : K) • (a : B) = 0 := by
    calc
      (Fintype.card H : K) • (a : B) =
          ((Fintype.card H : K) • (1 : B)) * (a : B) := by rw [smul_mul_assoc, one_mul]
      _ = (∑ g : G, g • e) * (a : B) := by rw [htrace]
      _ = 0 := by rw [Finset.sum_mul]; simp only [htrans, Finset.sum_const_zero]
  apply Subtype.ext
  exact (smul_eq_zero.mp hz).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- A selecting factor with a unit trace identifies group invariants with stabilizer invariants.
Source: Serre, Linear Representations of Finite Groups, Chapter 1, Section 2, averaging. -/
def s2t_stabilizerFixedEquiv {K B C G : Type*}
    [Field K] [CharZero K] [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
    [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G K B]
    (H : Subgroup G) [Fintype H] [MulSemiringAction H C] [SMulCommClass H K C]
    (f : B →ₐ[K] C) (hsurj : Function.Surjective f)
    (heq : ∀ (h : H) (a : B), f ((h : G) • a) = h • f a)
    (e : B) (hsel_in : ∀ g ∈ H, f (g • e) = 1)
    (hsel_out : ∀ g ∉ H, f (g • e) = 0)
    (hker : ∀ a : B, f a = 0 → e * a = 0)
    (htrace : ∑ g : G, g • e = (Fintype.card H : K) • (1 : B)) :
    FixedPoints.subalgebra K B G ≃+* FixedPoints.subalgebra K C H := by
  apply RingEquiv.ofBijective (s2t_stabilizerFixedMap H f heq)
  constructor
  · exact s2t_stabilizerFixedMap_injective H f heq e hker htrace
  · intro b
    obtain ⟨a, ha⟩ := s2t_stabilizer_trace_lift H f hsurj heq e hsel_in hsel_out b
    exact ⟨a, Subtype.ext ha⟩

end HodgeLean.Foundations.Program
