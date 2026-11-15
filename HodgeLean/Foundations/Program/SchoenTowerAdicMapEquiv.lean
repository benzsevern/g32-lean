import HodgeLean.Foundations.Program.SchoenTowerAdicMaps

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- An adic map is bijective if each of its ideal-power residue maps is bijective. -/
theorem s2t_adicMap_bijective_of_residues {A B : Type*} [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B) (f : A →+* B) (hf : I ≤ J.comap f)
    (hbij : ∀ n : ℕ, Function.Bijective
      (Ideal.quotientMap (J ^ n) f (s2t_adicMap_pow I J f hf n))) :
    Function.Bijective (s2t_adicMap I J f hf) := by
  let q (n : ℕ) : A ⧸ I ^ n →+* B ⧸ J ^ n :=
    Ideal.quotientMap (J ^ n) f (s2t_adicMap_pow I J f hf n)
  let e (n : ℕ) := RingEquiv.ofBijective (q n) (hbij n)
  let v (n : ℕ) : AdicCompletion J B →+* A ⧸ I ^ n :=
    (e n).symm.toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom
  have hv (n : ℕ) (x : AdicCompletion J B) :
      q n (v n x) = AdicCompletion.evalₐ J n x := (e n).apply_symm_apply _
  have hcompat : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow I hmn).comp (v n) = v m := by
    intro m n hmn
    apply RingHom.ext
    intro x
    apply (hbij m).injective
    change q m (Ideal.Quotient.factorPow I hmn (v n x)) = q m (v m x)
    have hcomm (z : A ⧸ I ^ n) :
        q m (Ideal.Quotient.factorPow I hmn z) = Ideal.Quotient.factorPow J hmn (q n z) := by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      rfl
    rw [hcomm, hv, hv, s2t_adic_eval_transition]
  let g : AdicCompletion J B →+* AdicCompletion I A :=
    AdicCompletion.liftRingHom I v hcompat
  have hg (n : ℕ) (x : AdicCompletion J B) :
      AdicCompletion.evalₐ I n (g x) = v n x :=
    AdicCompletion.evalₐ_liftRingHom I v hcompat n x
  have hleft (x : AdicCompletion I A) : g (s2t_adicMap I J f hf x) = x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [hg]
    change (e n).symm (AdicCompletion.evalₐ J n (s2t_adicMap I J f hf x)) = _
    rw [s2t_adicMap_eval]
    exact (e n).symm_apply_apply _
  have hright (x : AdicCompletion J B) : s2t_adicMap I J f hf (g x) = x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [s2t_adicMap_eval, hg]
    exact hv n x
  exact ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩

end HodgeLean.Foundations.Program
