import HodgeLean.Foundations.Program.SchoenTowerAdicAction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- A ring map preserving two ideals also preserves their powers. -/
theorem s2t_adicMap_pow {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B) (f : A →+* B) (hf : I ≤ J.comap f) (n : ℕ) :
    I ^ n ≤ (J ^ n).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hf) n

/-- The residue maps of a map preserving two ideals commute with adic transitions. -/
theorem s2t_adicMap_compat {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B) (f : A →+* B) (hf : I ≤ J.comap f) :
    ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow J hmn).comp
        ((Ideal.quotientMap (J ^ n) f (s2t_adicMap_pow I J f hf n)).comp
          (AdicCompletion.evalₐ I n).toRingHom) =
        (Ideal.quotientMap (J ^ m) f (s2t_adicMap_pow I J f hf m)).comp
          (AdicCompletion.evalₐ I m).toRingHom := by
  intro m n hmn
  ext x
  change Ideal.Quotient.factorPow J hmn
    (Ideal.quotientMap (J ^ n) f (s2t_adicMap_pow I J f hf n)
      (AdicCompletion.evalₐ I n x)) = _
  have hcomm (z : A ⧸ I ^ n) :
      Ideal.Quotient.factorPow J hmn
        (Ideal.quotientMap (J ^ n) f (s2t_adicMap_pow I J f hf n) z) =
      Ideal.quotientMap (J ^ m) f (s2t_adicMap_pow I J f hf m)
        (Ideal.Quotient.factorPow I hmn z) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  rw [hcomm, s2t_adic_eval_transition]
  rfl

/-- A map preserving two ideals induces a map of their adic rings. -/
def s2t_adicMap {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B) (f : A →+* B) (hf : I ≤ J.comap f) :
    AdicCompletion I A →+* AdicCompletion J B :=
  AdicCompletion.liftRingHom J
    (fun n => (Ideal.quotientMap (J ^ n) f (s2t_adicMap_pow I J f hf n)).comp
      (AdicCompletion.evalₐ I n).toRingHom)
    (s2t_adicMap_compat I J f hf)

/-- Evaluation of the induced adic map is the induced residue map. -/
theorem s2t_adicMap_eval {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B) (f : A →+* B) (hf : I ≤ J.comap f)
    (n : ℕ) (x : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (s2t_adicMap I J f hf x) =
      Ideal.quotientMap (J ^ n) f (s2t_adicMap_pow I J f hf n)
        (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom J _ (s2t_adicMap_compat I J f hf) n x

end HodgeLean.Foundations.Program
