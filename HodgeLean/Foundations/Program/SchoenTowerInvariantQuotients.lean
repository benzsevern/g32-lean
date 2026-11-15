import HodgeLean.Foundations.Program.SchoenTowerInvariantLifting
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Ring.Action.Group

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

namespace HodgeLean.Foundations.Program

/-- A ring action descends through a stable ideal. -/
@[instance_reducible]
def s2t_quotientAction {A G : Type*} [CommRing A] [Group G]
    [MulSemiringAction G A] (I : Ideal A)
    (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I) :
    MulSemiringAction G (A ⧸ I) where
  smul g := Ideal.quotientMap I (MulSemiringAction.toRingHom G A g) (hI g)
  one_smul x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk I ((1 : G) • a) = Ideal.Quotient.mk I a
    rw [one_smul]
  mul_smul g h x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk I ((g * h) • a) = Ideal.Quotient.mk I (g • h • a)
    rw [mul_smul]
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

/-- The descended action commutes with the quotient projection. -/
theorem s2t_quotientAction_mk {A G : Type*} [CommRing A] [Group G]
    [MulSemiringAction G A] (I : Ideal A)
    (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I) (g : G) (a : A) :
    letI := s2t_quotientAction I hI
    g • Ideal.Quotient.mk I a = Ideal.Quotient.mk I (g • a) := rfl

/-- Scalars commute with the descended action. -/
theorem s2t_quotientAction_smulCommClass {K A G : Type*}
    [Field K] [CommRing A] [Algebra K A] [Group G]
    [MulSemiringAction G A] [SMulCommClass G K A]
    (I : Ideal A) (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I) :
    letI := s2t_quotientAction I hI
    SMulCommClass G K (A ⧸ I) := by
  letI := s2t_quotientAction I hI
  constructor
  intro g c x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk I (g • c • a) = Ideal.Quotient.mk I (c • g • a)
  rw [smul_comm]

/-- Every fixed residue class has a fixed representative in characteristic zero.
Source: Serre, Linear Representations of Finite Groups, Chapter 1, Section 2, averaging. -/
theorem s2t_fixed_quotient_representative {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (I : Ideal A) (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I) :
    letI := s2t_quotientAction I hI
    letI := s2t_quotientAction_smulCommClass (K := K) I hI
    ∀ b : FixedPoints.subalgebra K (A ⧸ I) G,
      ∃ a : FixedPoints.subalgebra K A G, Ideal.Quotient.mk I a = (b : A ⧸ I) := by
  letI := s2t_quotientAction I hI
  letI := s2t_quotientAction_smulCommClass (K := K) I hI
  exact s2t_fixedSubalgebra_lift (Ideal.Quotient.mkₐ K I)
    Ideal.Quotient.mk_surjective (fun g a => (s2t_quotientAction_mk I hI g a).symm)

/-- Projection of fixed elements to fixed residue classes. -/
def s2t_fixedQuotientMap {K A G : Type*}
    [Field K] [CommRing A] [Algebra K A] [Group G]
    [MulSemiringAction G A] [SMulCommClass G K A]
    (I : Ideal A) (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I) :
    letI := s2t_quotientAction I hI
    letI := s2t_quotientAction_smulCommClass (K := K) I hI
    FixedPoints.subalgebra K A G →+* FixedPoints.subalgebra K (A ⧸ I) G := by
  letI := s2t_quotientAction I hI
  letI := s2t_quotientAction_smulCommClass (K := K) I hI
  refine ((Ideal.Quotient.mk I).comp (FixedPoints.subalgebra K A G).toSubring.subtype).codRestrict _ ?_
  intro a g
  change g • Ideal.Quotient.mk I a.val = Ideal.Quotient.mk I a.val
  rw [s2t_quotientAction_mk, a.property g]

/-- The kernel of projection on fixed elements is the contracted ideal. -/
theorem s2t_fixedQuotientMap_ker {K A G : Type*}
    [Field K] [CommRing A] [Algebra K A] [Group G]
    [MulSemiringAction G A] [SMulCommClass G K A]
    (I : Ideal A) (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I) :
    RingHom.ker (s2t_fixedQuotientMap (K := K) I hI) =
      I.comap (FixedPoints.subalgebra K A G).toSubring.subtype := by
  ext a
  change s2t_fixedQuotientMap I hI a = 0 ↔ a.val ∈ I
  rw [← Subtype.val_inj]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- Fixed elements commute with quotient by a stable ideal in characteristic zero.
Source: Serre, Linear Representations of Finite Groups, Chapter 1, Section 2, averaging. -/
def s2t_fixedQuotientEquiv {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (I : Ideal A) (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I) :
    letI := s2t_quotientAction I hI
    letI := s2t_quotientAction_smulCommClass (K := K) I hI
    (FixedPoints.subalgebra K A G ⧸
      I.comap (FixedPoints.subalgebra K A G).toSubring.subtype) ≃+*
      FixedPoints.subalgebra K (A ⧸ I) G := by
  letI := s2t_quotientAction I hI
  letI := s2t_quotientAction_smulCommClass (K := K) I hI
  apply (Ideal.quotEquivOfEq (s2t_fixedQuotientMap_ker (K := K) I hI).symm).trans
  apply RingHom.quotientKerEquivOfSurjective
  intro b
  obtain ⟨a, ha⟩ := s2t_fixed_quotient_representative I hI b
  exact ⟨a, Subtype.ext ha⟩

/-- The fixed residue isomorphism sends each fixed representative to its residue. -/
theorem s2t_fixedQuotientEquiv_mk {K A G : Type*}
    [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Group G] [Fintype G] [MulSemiringAction G A] [SMulCommClass G K A]
    (I : Ideal A) (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I)
    (a : FixedPoints.subalgebra K A G) :
    ((s2t_fixedQuotientEquiv (K := K) I hI)
      (Ideal.Quotient.mk _ a)).val = Ideal.Quotient.mk I (a : A) := by
  simp only [s2t_fixedQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  rfl

end HodgeLean.Foundations.Program
