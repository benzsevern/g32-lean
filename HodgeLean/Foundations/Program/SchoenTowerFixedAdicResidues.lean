import HodgeLean.Foundations.Program.SchoenTowerInvariantAdicQuotients
import HodgeLean.Foundations.Program.SchoenTowerAdicMaps

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- Evaluation of an invariant adic element gives an invariant residue. -/
def s2t_fixedAdicResidueMap {K A G : Type*}
    [Field K] [CommRing A] [Algebra K A] [Group G]
    [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) (n : ℕ) :
    let I := J.map (FixedPoints.subalgebra K A G).toSubring.subtype
    let hI := s2t_extended_fixed_ideal_stable J
    letI := s2t_adicAction I hI
    letI := s2t_quotientAction (I ^ n) (s2t_stable_ideal_pow I hI n)
    letI := s2t_quotientAction_smulCommClass (K := K) (I ^ n)
      (s2t_stable_ideal_pow I hI n)
    FixedPoints.subring (AdicCompletion I A) G →+*
      FixedPoints.subalgebra K (A ⧸ I ^ n) G := by
  let I := J.map (FixedPoints.subalgebra K A G).toSubring.subtype
  let hI := s2t_extended_fixed_ideal_stable J
  letI := s2t_adicAction I hI
  letI := s2t_quotientAction (I ^ n) (s2t_stable_ideal_pow I hI n)
  letI := s2t_quotientAction_smulCommClass (K := K) (I ^ n)
    (s2t_stable_ideal_pow I hI n)
  refine ((AdicCompletion.evalₐ I n).toRingHom.comp
    (FixedPoints.subring (AdicCompletion I A) G).subtype).codRestrict _ ?_
  intro x g
  change Ideal.quotientMap (I ^ n) (MulSemiringAction.toRingHom G A g)
    (s2t_stable_ideal_pow I hI n g) (AdicCompletion.evalₐ I n x.val) =
      AdicCompletion.evalₐ I n x.val
  rw [← s2t_adicActionHom_eval I hI g n x.val]
  have hx : s2t_adicActionHom I hI g x.val = x.val := x.property g
  rw [hx]

/-- The fixed residue comparison with powers written in the acted-on ring. -/
def s2t_fixedPowerResidueEquiv {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) (n : ℕ) :
    let I := J.map (FixedPoints.subalgebra K A G).toSubring.subtype
    let hI := s2t_extended_fixed_ideal_stable J
    letI := s2t_quotientAction (I ^ n) (s2t_stable_ideal_pow I hI n)
    letI := s2t_quotientAction_smulCommClass (K := K) (I ^ n)
      (s2t_stable_ideal_pow I hI n)
    (FixedPoints.subalgebra K A G ⧸ J ^ n) ≃+*
      FixedPoints.subalgebra K (A ⧸ I ^ n) G :=
  (Ideal.quotEquivOfEq (s2t_fixed_power_comap_map J n).symm).trans
    (s2t_fixedQuotientEquiv _ (s2t_stable_ideal_pow _
      (s2t_extended_fixed_ideal_stable J) n))

/-- The comparison on a fixed representative is its residue in the acted-on ring. -/
theorem s2t_fixedPowerResidueEquiv_mk {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) (n : ℕ)
    (a : FixedPoints.subalgebra K A G) :
    ((s2t_fixedPowerResidueEquiv J n) (Ideal.Quotient.mk _ a)).val =
      Ideal.Quotient.mk ((J.map (FixedPoints.subalgebra K A G).toSubring.subtype) ^ n)
        (a : A) := by
  simp only [s2t_fixedPowerResidueEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact s2t_fixedQuotientEquiv_mk _ _ a

/-- The underlying residue map of the fixed comparison is induced by inclusion. -/
theorem s2t_fixedPowerResidueEquiv_val {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) (n : ℕ)
    (x : FixedPoints.subalgebra K A G ⧸ J ^ n) :
    ((s2t_fixedPowerResidueEquiv J n) x).val =
      Ideal.quotientMap ((J.map (FixedPoints.subalgebra K A G).toSubring.subtype) ^ n)
        (FixedPoints.subalgebra K A G).toSubring.subtype
        (s2t_adicMap_pow _ _ _ Ideal.le_comap_map n) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [s2t_fixedPowerResidueEquiv_mk]
  rfl

/-- The inverse fixed comparison converts an invariant adic element to a fixed-ring residue. -/
def s2t_fixedAdicInverseResidue {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) (n : ℕ) :
    let I := J.map (FixedPoints.subalgebra K A G).toSubring.subtype
    letI := s2t_adicAction I (s2t_extended_fixed_ideal_stable J)
    FixedPoints.subring (AdicCompletion I A) G →+*
      FixedPoints.subalgebra K A G ⧸ J ^ n :=
  (s2t_fixedPowerResidueEquiv J n).symm.toRingHom.comp (s2t_fixedAdicResidueMap J n)

/-- Including the inverse residue gives the original adic residue. -/
theorem s2t_fixedAdicInverseResidue_eval {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) (n : ℕ) :
    let I := J.map (FixedPoints.subalgebra K A G).toSubring.subtype
    letI := s2t_adicAction I (s2t_extended_fixed_ideal_stable J)
    ∀ x : FixedPoints.subring (AdicCompletion I A) G,
      Ideal.quotientMap (I ^ n) (FixedPoints.subalgebra K A G).toSubring.subtype
        (s2t_adicMap_pow J I _ Ideal.le_comap_map n)
        (s2t_fixedAdicInverseResidue J n x) = AdicCompletion.evalₐ I n x.val := by
  intro I x
  rw [← s2t_fixedPowerResidueEquiv_val]
  change ((s2t_fixedPowerResidueEquiv J n)
    ((s2t_fixedPowerResidueEquiv J n).symm (s2t_fixedAdicResidueMap J n x))).val = _
  rw [RingEquiv.apply_symm_apply]
  rfl

/-- The inverse fixed-ring residues commute with all adic transition maps. -/
theorem s2t_fixedAdicInverseResidue_compat {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) :
    let I := J.map (FixedPoints.subalgebra K A G).toSubring.subtype
    letI := s2t_adicAction I (s2t_extended_fixed_ideal_stable J)
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow J hmn).comp (s2t_fixedAdicInverseResidue J n) =
        s2t_fixedAdicInverseResidue J m := by
  intro I m n hmn
  let f := (FixedPoints.subalgebra K A G).toSubring.subtype
  let q (n : ℕ) : (FixedPoints.subalgebra K A G ⧸ J ^ n) →+* A ⧸ I ^ n :=
    Ideal.quotientMap (I ^ n) f (s2t_adicMap_pow J I f Ideal.le_comap_map n)
  ext x
  apply Ideal.quotientMap_injective' (le_of_eq (s2t_fixed_power_comap_map J m))
  change q m (Ideal.Quotient.factorPow J hmn (s2t_fixedAdicInverseResidue J n x)) =
    q m (s2t_fixedAdicInverseResidue J m x)
  have hcomm (z : FixedPoints.subalgebra K A G ⧸ J ^ n) :
      q m (Ideal.Quotient.factorPow J hmn z) = Ideal.Quotient.factorPow I hmn (q n z) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  rw [hcomm]
  change Ideal.Quotient.factorPow I hmn
    (Ideal.quotientMap (I ^ n) f _ (s2t_fixedAdicInverseResidue J n x)) =
      Ideal.quotientMap (I ^ m) f _ (s2t_fixedAdicInverseResidue J m x)
  rw [s2t_fixedAdicInverseResidue_eval, s2t_fixedAdicInverseResidue_eval,
    s2t_adic_eval_transition]

/-- Compatible inverse residues give a map to the adic ring of the fixed subalgebra. -/
def s2t_fixedAdicInverse {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (J : Ideal (FixedPoints.subalgebra K A G)) :
    let I := J.map (FixedPoints.subalgebra K A G).toSubring.subtype
    letI := s2t_adicAction I (s2t_extended_fixed_ideal_stable J)
    FixedPoints.subring (AdicCompletion I A) G →+*
      AdicCompletion J (FixedPoints.subalgebra K A G) :=
  AdicCompletion.liftRingHom J (s2t_fixedAdicInverseResidue J)
    (s2t_fixedAdicInverseResidue_compat J)

end HodgeLean.Foundations.Program
