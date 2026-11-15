import HodgeLean.Foundations.Program.SchoenTowerAdicMaps
import Mathlib.RingTheory.Finiteness.Ideal

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- The actual adic map for two ideals is bijective when their power filtrations are cofinal. -/
theorem s2t_adicMap_bijective_of_cofinal {A : Type*} [CommRing A]
    (I J : Ideal A) (hIJ : I ≤ J) (k : ℕ) (hk : 0 < k) (hJI : J ^ k ≤ I) :
    Function.Bijective (s2t_adicMap I J (RingHom.id A) hIJ) := by
  have hpow (n : ℕ) : J ^ (k * n) ≤ I ^ n := by
    rw [pow_mul]
    exact Ideal.pow_right_mono hJI n
  have hkn (n : ℕ) : n ≤ k * n := by
    calc
      n = 1 * n := (one_mul n).symm
      _ ≤ k * n := Nat.mul_le_mul_right n hk
  let v (n : ℕ) : AdicCompletion J A →+* A ⧸ I ^ n :=
    (Ideal.Quotient.factor (hpow n)).comp (AdicCompletion.evalₐ J (k * n)).toRingHom
  have hcompat : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow I hmn).comp (v n) = v m := by
    intro m n hmn
    apply RingHom.ext
    intro x
    change Ideal.Quotient.factorPow I hmn
      (Ideal.Quotient.factor (hpow n) (AdicCompletion.evalₐ J (k * n) x)) =
      Ideal.Quotient.factor (hpow m) (AdicCompletion.evalₐ J (k * m) x)
    have hcomm (z : A ⧸ J ^ (k * n)) :
        Ideal.Quotient.factorPow I hmn (Ideal.Quotient.factor (hpow n) z) =
        Ideal.Quotient.factor (hpow m)
          (Ideal.Quotient.factorPow J (Nat.mul_le_mul_left k hmn) z) := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      rfl
    rw [hcomm, s2t_adic_eval_transition]
  let g := AdicCompletion.liftRingHom I v hcompat
  have hg (n : ℕ) (x : AdicCompletion J A) :
      AdicCompletion.evalₐ I n (g x) =
        Ideal.Quotient.factor (hpow n) (AdicCompletion.evalₐ J (k * n) x) :=
    AdicCompletion.evalₐ_liftRingHom I v hcompat n x
  have hleft (x : AdicCompletion I A) : g (s2t_adicMap I J (RingHom.id A) hIJ x) = x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [hg, s2t_adicMap_eval]
    have hcomm (z : A ⧸ I ^ (k * n)) :
        Ideal.Quotient.factor (hpow n)
          (Ideal.quotientMap (J ^ (k * n)) (RingHom.id A)
            (s2t_adicMap_pow I J (RingHom.id A) hIJ (k * n)) z) =
        Ideal.Quotient.factorPow I (hkn n) z := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      rfl
    rw [hcomm, s2t_adic_eval_transition]
  have hright (x : AdicCompletion J A) : s2t_adicMap I J (RingHom.id A) hIJ (g x) = x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [s2t_adicMap_eval, hg]
    have hcomm (z : A ⧸ J ^ (k * n)) :
        Ideal.quotientMap (J ^ n) (RingHom.id A)
          (s2t_adicMap_pow I J (RingHom.id A) hIJ n)
          (Ideal.Quotient.factor (hpow n) z) =
        Ideal.Quotient.factorPow J (hkn n) z := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      rfl
    rw [hcomm, s2t_adic_eval_transition]
  exact ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩

/-- An intermediate finitely generated ideal inside the radical defines the same adic ring. -/
theorem s2t_adicMap_bijective_of_le_radical {A : Type*} [CommRing A]
    (I J : Ideal A) (hIJ : I ≤ J) (hJI : J ≤ I.radical) (hJ : J.FG) :
    Function.Bijective (s2t_adicMap I J (RingHom.id A) hIJ) := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJI hJ
  exact s2t_adicMap_bijective_of_cofinal I J hIJ (k + 1) (Nat.succ_pos k)
    ((Ideal.pow_le_pow_right (Nat.le_succ k)).trans hk)

end HodgeLean.Foundations.Program
