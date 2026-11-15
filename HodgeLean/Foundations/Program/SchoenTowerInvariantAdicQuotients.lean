import HodgeLean.Foundations.Program.SchoenTowerReynolds
import HodgeLean.Foundations.Program.SchoenTowerInvariantQuotients
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

namespace HodgeLean.Foundations.Program

/-- An ideal extended from the fixed subalgebra is stable under the action. -/
theorem s2t_extended_fixed_ideal_stable {K A G : Type*}
    [Field K] [CommRing A] [Algebra K A] [Group G]
    [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) (g : G) (a : A)
    (ha : a ∈ J.map (FixedPoints.subalgebra K A G).toSubring.subtype) :
    g • a ∈ J.map (FixedPoints.subalgebra K A G).toSubring.subtype := by
  let f := (FixedPoints.subalgebra K A G).toSubring.subtype
  have heq : (MulSemiringAction.toRingHom G A g).comp f = f := by
    ext r
    exact (FixedPoints.mem_subalgebra (A := K)).mp r.property g
  have hmap : (J.map f).map (MulSemiringAction.toRingHom G A g) = J.map f := by
    rw [Ideal.map_map, heq]
  have h := Ideal.mem_map_of_mem (MulSemiringAction.toRingHom G A g) ha
  rwa [hmap] at h

/-- Quotients by extended ideals retain precisely the original fixed residue ring.
Source: Serre, Linear Representations of Finite Groups, Chapter 1, Section 2, averaging. -/
def s2t_fixedExtendedQuotientEquiv {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) :
    let I := J.map (FixedPoints.subalgebra K A G).toSubring.subtype
    let hI := s2t_extended_fixed_ideal_stable J
    letI := s2t_quotientAction I hI
    letI := s2t_quotientAction_smulCommClass (K := K) I hI
    (FixedPoints.subalgebra K A G ⧸ J) ≃+*
      FixedPoints.subalgebra K (A ⧸ I) G :=
  (Ideal.quotEquivOfEq (s2t_fixed_ideal_comap_map J).symm).trans
    (s2t_fixedQuotientEquiv _ (s2t_extended_fixed_ideal_stable J))

/-- The extended-ideal comparison preserves the specified fixed representatives. -/
theorem s2t_fixedExtendedQuotientEquiv_mk {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) (a : FixedPoints.subalgebra K A G) :
    ((s2t_fixedExtendedQuotientEquiv J) (Ideal.Quotient.mk J a)).val =
      Ideal.Quotient.mk (J.map (FixedPoints.subalgebra K A G).toSubring.subtype) (a : A) := by
  simp only [s2t_fixedExtendedQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk]
  exact s2t_fixedQuotientEquiv_mk _ _ a

/-- The comparison for powers of an ideal commutes with the quotient transition maps. -/
theorem s2t_fixedExtendedQuotientEquiv_transition {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) {m n : ℕ} (hmn : m ≤ n)
    (x : FixedPoints.subalgebra K A G ⧸ J ^ n) :
    Ideal.Quotient.factor (Ideal.map_mono (Ideal.pow_le_pow_right hmn))
      ((s2t_fixedExtendedQuotientEquiv (J ^ n)) x).val =
        ((s2t_fixedExtendedQuotientEquiv (J ^ m))
          (Ideal.Quotient.factorPow J hmn x)).val := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [s2t_fixedExtendedQuotientEquiv_mk]
  change Ideal.Quotient.mk _ (a : A) =
    ((s2t_fixedExtendedQuotientEquiv (J ^ m)) (Ideal.Quotient.mk _ a)).val
  exact (s2t_fixedExtendedQuotientEquiv_mk (J ^ m) a).symm

/-- Powers of an extended fixed ideal contract to the corresponding original powers. -/
theorem s2t_fixed_power_comap_map {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) (n : ℕ) :
    ((J.map (FixedPoints.subalgebra K A G).toSubring.subtype) ^ n).comap
      (FixedPoints.subalgebra K A G).toSubring.subtype = J ^ n := by
  rw [← Ideal.map_pow]
  exact s2t_fixed_ideal_comap_map (J ^ n)

end HodgeLean.Foundations.Program
