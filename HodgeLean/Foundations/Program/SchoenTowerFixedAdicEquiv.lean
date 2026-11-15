import HodgeLean.Foundations.Program.SchoenTowerFixedAdicResidues

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- Inclusion of the fixed ring induces a map into the fixed adic ring. -/
def s2t_fixedAdicMap {K A G : Type*}
    [Field K] [CommRing A] [Algebra K A] [Group G]
    [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) :
    let I := J.map (FixedPoints.subalgebra K A G).toSubring.subtype
    letI := s2t_adicAction I (s2t_extended_fixed_ideal_stable J)
    AdicCompletion J (FixedPoints.subalgebra K A G) →+*
      FixedPoints.subring (AdicCompletion I A) G := by
  let I := J.map (FixedPoints.subalgebra K A G).toSubring.subtype
  let hI := s2t_extended_fixed_ideal_stable J
  let f := (FixedPoints.subalgebra K A G).toSubring.subtype
  letI := s2t_adicAction I hI
  refine (s2t_adicMap J I f Ideal.le_comap_map).codRestrict _ ?_
  intro x g
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ I n
    (s2t_adicActionHom I hI g (s2t_adicMap J I f Ideal.le_comap_map x)) = _
  rw [s2t_adicActionHom_eval I hI g, s2t_adicMap_eval]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
  rw [← ha]
  change Ideal.Quotient.mk (I ^ n) (g • (a : A)) = Ideal.Quotient.mk (I ^ n) (a : A)
  rw [(FixedPoints.mem_subalgebra (A := K)).mp a.property g]

/-- The fixed adic map evaluates as the inclusion-induced residue map. -/
theorem s2t_fixedAdicMap_eval {K A G : Type*}
    [Field K] [CommRing A] [Algebra K A] [Group G]
    [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) (n : ℕ)
    (x : AdicCompletion J (FixedPoints.subalgebra K A G)) :
    AdicCompletion.evalₐ (J.map (FixedPoints.subalgebra K A G).toSubring.subtype) n
      (s2t_fixedAdicMap J x).val =
      Ideal.quotientMap ((J.map (FixedPoints.subalgebra K A G).toSubring.subtype) ^ n)
        (FixedPoints.subalgebra K A G).toSubring.subtype
        (s2t_adicMap_pow _ _ _ Ideal.le_comap_map n) (AdicCompletion.evalₐ J n x) :=
  s2t_adicMap_eval _ _ _ _ _ _

/-- The inverse map has the prescribed fixed-ring residue at every power. -/
theorem s2t_fixedAdicInverse_eval {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) (n : ℕ) :
    let I := J.map (FixedPoints.subalgebra K A G).toSubring.subtype
    letI := s2t_adicAction I (s2t_extended_fixed_ideal_stable J)
    ∀ x : FixedPoints.subring (AdicCompletion I A) G,
      AdicCompletion.evalₐ J n (s2t_fixedAdicInverse J x) =
        s2t_fixedAdicInverseResidue J n x := by
  intro I x
  exact AdicCompletion.evalₐ_liftRingHom J _ (s2t_fixedAdicInverseResidue_compat J) n x

/-- Inclusion after the inverse adic map recovers the invariant element. -/
theorem s2t_fixedAdicMap_inverse {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) :
    let I := J.map (FixedPoints.subalgebra K A G).toSubring.subtype
    letI := s2t_adicAction I (s2t_extended_fixed_ideal_stable J)
    ∀ x : FixedPoints.subring (AdicCompletion I A) G,
      s2t_fixedAdicMap J (s2t_fixedAdicInverse J x) = x := by
  intro I x
  apply Subtype.ext
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [s2t_fixedAdicMap_eval, s2t_fixedAdicInverse_eval,
    s2t_fixedAdicInverseResidue_eval]

/-- The inverse adic map after inclusion recovers the original element. -/
theorem s2t_fixedAdicInverse_map {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G))
    (x : AdicCompletion J (FixedPoints.subalgebra K A G)) :
    s2t_fixedAdicInverse J (s2t_fixedAdicMap J x) = x := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [s2t_fixedAdicInverse_eval]
  apply Ideal.quotientMap_injective' (le_of_eq (s2t_fixed_power_comap_map J n))
  rw [s2t_fixedAdicInverseResidue_eval, s2t_fixedAdicMap_eval]

/-- The adic ring of the fixed subalgebra is the fixed subring of the adic ring
along the extended ideal.
Source: Serre, Linear Representations of Finite Groups, Chapter 1, Section 2, averaging;
the compatible residue-quotient construction of adic rings. -/
def s2t_fixedAdicEquiv {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) :
    let I := J.map (FixedPoints.subalgebra K A G).toSubring.subtype
    letI := s2t_adicAction I (s2t_extended_fixed_ideal_stable J)
    AdicCompletion J (FixedPoints.subalgebra K A G) ≃+*
      FixedPoints.subring (AdicCompletion I A) G := by
  apply RingEquiv.ofBijective (s2t_fixedAdicMap J)
  constructor
  · intro x y h
    have hh := congrArg (s2t_fixedAdicInverse J) h
    simpa only [s2t_fixedAdicInverse_map] using hh
  · intro x
    exact ⟨s2t_fixedAdicInverse J x, s2t_fixedAdicMap_inverse J x⟩

end HodgeLean.Foundations.Program
