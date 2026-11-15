import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Invariant.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_uniform_localization_exponent
    {A L G : Type*} [CommRing A] [CommRing L] [Finite G]
    [Algebra A L] (r : A) [IsLocalization.Away r L]
    (a b : G → A)
    (h : ∀ g, algebraMap A L (a g) = algebraMap A L (b g)) :
    ∃ n : ℕ, ∀ g, r ^ n * a g = r ^ n * b g := by
  classical
  letI := Fintype.ofFinite G
  have hs (g : G) : ∃ n : ℕ, r ^ n * a g = r ^ n * b g :=
    IsLocalization.Away.exists_of_eq r (h g)
  choose k hk using hs
  refine ⟨Finset.univ.sup k, fun g => ?_⟩
  have hle : k g ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ g)
  calc
    r ^ Finset.univ.sup k * a g =
        r ^ (Finset.univ.sup k - k g) * (r ^ k g * a g) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    _ = r ^ (Finset.univ.sup k - k g) * (r ^ k g * b g) := by rw [hk g]
    _ = r ^ Finset.univ.sup k * b g := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

lemma s2v_i1ahi_invariant_localized_numerator
    {A L G : Type*} [CommRing A] [CommRing L] [Group G] [Finite G]
    [Algebra A L] [MulSemiringAction G A] [MulSemiringAction G L]
    (r : A) [IsLocalization.Away r L]
    (hr : ∀ g : G, g • r = r)
    (hequiv : ∀ (g : G) (x : A), algebraMap A L (g • x) = g • algebraMap A L x)
    (z : L) (hz : ∀ g : G, g • z = z) :
    ∃ (n : ℕ) (a : A), (∀ g : G, g • a = a) ∧
      z * algebraMap A L r ^ n = algebraMap A L a := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj r z
  have hi (g : G) : algebraMap A L (g • a) = algebraMap A L a := by
    rw [hequiv, ← ha, smul_mul', smul_pow', ← hequiv, hr, hz]
  obtain ⟨k, hk⟩ := s2v_i1ahi_uniform_localization_exponent r
    (fun g : G => g • a) (fun _ => a) hi
  refine ⟨n + k, r ^ k * a, fun g => ?_, ?_⟩
  · rw [smul_mul', smul_pow', hr, hk g]
  · rw [pow_add, ← mul_assoc, ha, map_mul, map_pow, mul_comm]

lemma s2v_i1ahi_fixed_subring_isUnit
    {A G : Type*} [CommRing A] [Group G] [MulSemiringAction G A]
    (B : Subring A) (hB : ∀ a : A, a ∈ B ↔ ∀ g : G, g • a = a)
    (b : B) (hb : IsUnit (b : A)) : IsUnit b := by
  obtain ⟨c, hc⟩ := isUnit_iff_exists_inv.mp hb
  have hfix (g : G) : g • c = c := by
    have hg : (b : A) * (g • c) = 1 := by
      rw [← (hB b).mp b.property g, ← smul_mul', hc, smul_one]
    calc
      g • c = (c * (b : A)) * (g • c) := by rw [mul_comm c, hc, one_mul]
      _ = c * ((b : A) * (g • c)) := mul_assoc _ _ _
      _ = c := by rw [hg, mul_one]
  apply isUnit_iff_exists_inv.mpr
  refine ⟨⟨c, (hB c).mpr hfix⟩, ?_⟩
  exact Subtype.ext hc

lemma s2v_i1ahi_fixed_subrings_localization
    {A L G : Type*} [CommRing A] [CommRing L] [Group G] [Finite G]
    [Algebra A L] [MulSemiringAction G A] [MulSemiringAction G L]
    (B : Subring A) (C : Subring L)
    (hB : ∀ a : A, a ∈ B ↔ ∀ g : G, g • a = a)
    (hC : ∀ z : L, z ∈ C ↔ ∀ g : G, g • z = z)
    (r : B) [IsLocalization.Away (r : A) L]
    (hequiv : ∀ (g : G) (x : A), algebraMap A L (g • x) = g • algebraMap A L x)
    (f : B →+* C) (hf : ∀ b : B, (f b : L) = algebraMap A L (b : A)) :
    letI := f.toAlgebra
    IsLocalization.Away r C := by
  letI := f.toAlgebra
  apply IsLocalization.Away.mk
  · apply s2v_i1ahi_fixed_subring_isUnit C hC (f r)
    rw [hf]
    exact IsLocalization.Away.algebraMap_isUnit (r : A)
  · intro z
    obtain ⟨n, a, ha, hz⟩ := s2v_i1ahi_invariant_localized_numerator
      (r : A) ((hB r).mp r.property) hequiv (z : L) ((hC z).mp z.property)
    refine ⟨n, ⟨a, (hB a).mpr ha⟩, ?_⟩
    apply Subtype.ext
    change (z : L) * (f r : L) ^ n = (f ⟨a, (hB a).mpr ha⟩ : L)
    rw [hf, hf]
    exact hz
  · intro a b hab
    have he : algebraMap A L (a : A) = algebraMap A L (b : A) := by
      rw [← hf a, ← hf b]
      exact congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (r : A) he
    exact ⟨n, Subtype.ext hn⟩

end HodgeLean.Foundations.Program
