import HodgeLean.Foundations.Program.SchoenTowerInvariantQuotients
import Mathlib.RingTheory.AdicCompletion.Algebra

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- Evaluation of an adic ring element commutes with reduction to a smaller power. -/
theorem s2t_adic_eval_transition {A : Type*} [CommRing A] (I : Ideal A)
    {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hmn (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk (I ^ m) (a.val n) = Ideal.Quotient.mk (I ^ m) (a.val m)
  apply Ideal.Quotient.eq.mpr
  have h := (a.property hmn).symm
  simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using h

/-- Every power of a stable ideal is stable. -/
theorem s2t_stable_ideal_pow {A G : Type*} [CommRing A] [Group G]
    [MulSemiringAction G A] (I : Ideal A)
    (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I)
    (n : ℕ) (g : G) (a : A) (ha : a ∈ I ^ n) : g • a ∈ I ^ n := by
  let f := MulSemiringAction.toRingHom G A g
  have hle : I.map f ≤ I := Ideal.map_le_iff_le_comap.mpr (hI g)
  have hp : (I ^ n).map f ≤ I ^ n := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hle n
  exact hp (Ideal.mem_map_of_mem f ha)

/-- Residue actions commute with the transitions defining the adic ring. -/
theorem s2t_adicAction_compat {A G : Type*} [CommRing A] [Group G]
    [MulSemiringAction G A] (I : Ideal A)
    (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I) (g : G) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow I hmn).comp
        ((Ideal.quotientMap (I ^ n) (MulSemiringAction.toRingHom G A g)
          (s2t_stable_ideal_pow I hI n g)).comp (AdicCompletion.evalₐ I n).toRingHom) =
        (Ideal.quotientMap (I ^ m) (MulSemiringAction.toRingHom G A g)
          (s2t_stable_ideal_pow I hI m g)).comp (AdicCompletion.evalₐ I m).toRingHom := by
  intro m n hmn
  ext x
  change Ideal.Quotient.factorPow I hmn
    (Ideal.quotientMap (I ^ n) (MulSemiringAction.toRingHom G A g) (s2t_stable_ideal_pow I hI n g)
      (AdicCompletion.evalₐ I n x)) = _
  have hcomm (z : A ⧸ I ^ n) :
      Ideal.Quotient.factorPow I hmn
        (Ideal.quotientMap (I ^ n) (MulSemiringAction.toRingHom G A g) (s2t_stable_ideal_pow I hI n g) z) =
      Ideal.quotientMap (I ^ m) (MulSemiringAction.toRingHom G A g) (s2t_stable_ideal_pow I hI m g)
        (Ideal.Quotient.factorPow I hmn z) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  rw [hcomm, s2t_adic_eval_transition]
  rfl

/-- A stable-ideal ring action extends to the adic ring. -/
def s2t_adicActionHom {A G : Type*} [CommRing A] [Group G]
    [MulSemiringAction G A] (I : Ideal A)
    (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I) (g : G) :
    AdicCompletion I A →+* AdicCompletion I A :=
  AdicCompletion.liftRingHom I
    (fun n => (Ideal.quotientMap (I ^ n) (MulSemiringAction.toRingHom G A g)
      (s2t_stable_ideal_pow I hI n g)).comp (AdicCompletion.evalₐ I n).toRingHom)
    (s2t_adicAction_compat I hI g)

/-- The extended action is the original action on every residue quotient. -/
theorem s2t_adicActionHom_eval {A G : Type*} [CommRing A] [Group G]
    [MulSemiringAction G A] (I : Ideal A)
    (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I) (g : G)
    (n : ℕ) (x : AdicCompletion I A) :
    AdicCompletion.evalₐ I n (s2t_adicActionHom I hI g x) =
      Ideal.quotientMap (I ^ n) (MulSemiringAction.toRingHom G A g)
        (s2t_stable_ideal_pow I hI n g) (AdicCompletion.evalₐ I n x) := by
  exact AdicCompletion.evalₐ_liftRingHom I _ (s2t_adicAction_compat I hI g) n x

/-- The adic extensions form a ring action of the original group. -/
@[instance_reducible]
def s2t_adicAction {A G : Type*} [CommRing A] [Group G]
    [MulSemiringAction G A] (I : Ideal A)
    (hI : ∀ (g : G) (a : A), a ∈ I → g • a ∈ I) :
    MulSemiringAction G (AdicCompletion I A) where
  smul g := s2t_adicActionHom I hI g
  one_smul x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ I n (s2t_adicActionHom I hI (1 : G) x) = _
    rw [s2t_adicActionHom_eval]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    rw [← ha]
    change Ideal.Quotient.mk (I ^ n) ((1 : G) • a) = Ideal.Quotient.mk (I ^ n) a
    rw [one_smul]
  mul_smul g h x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ I n (s2t_adicActionHom I hI (g * h) x) =
      AdicCompletion.evalₐ I n (s2t_adicActionHom I hI g (s2t_adicActionHom I hI h x))
    rw [s2t_adicActionHom_eval, s2t_adicActionHom_eval, s2t_adicActionHom_eval]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    rw [← ha]
    change Ideal.Quotient.mk (I ^ n) ((g * h) • a) =
      Ideal.Quotient.mk (I ^ n) (g • h • a)
    rw [mul_smul]
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

end HodgeLean.Foundations.Program
