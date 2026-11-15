import HodgeLean.Foundations.Program.SchoenTowerCoprimePowerQuotients
import HodgeLean.Foundations.Program.SchoenTowerAdicMaps

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Function

namespace HodgeLean.Foundations.Program

/-- The actual adic maps from an intersection ideal to its factors, assembled as a ring map. -/
def s2t_adicProductMap {A ι : Type*} [CommRing A]
    (I : ι → Ideal A) :
    AdicCompletion (⨅ i, I i) A →+* ∀ i, AdicCompletion (I i) A :=
  RingHom.pi (fun i => s2t_adicMap (⨅ j, I j) (I i) (RingHom.id A) (iInf_le I i))

/-- The adic ring along a finite coprime intersection maps bijectively to the factor adic rings. -/
theorem s2t_adicProductMap_bijective {A ι : Type*} [CommRing A] [Fintype ι]
    (I : ι → Ideal A) (hI : Pairwise (IsCoprime on I)) :
    Function.Bijective (s2t_adicProductMap I) := by
  let J := ⨅ i, I i
  let e (n : ℕ) := s2t_coprimePowerQuotientEquiv I hI n
  let w (n : ℕ) : (∀ i, AdicCompletion (I i) A) →+* ∀ i, A ⧸ I i ^ n :=
    RingHom.pi (fun i => (AdicCompletion.evalₐ (I i) n).toRingHom.comp
      (Pi.evalRingHom (fun i => AdicCompletion (I i) A) i))
  let v (n : ℕ) := (e n).symm.toRingHom.comp (w n)
  have hv (n : ℕ) (x : ∀ i, AdicCompletion (I i) A) : e n (v n x) = w n x :=
    (e n).apply_symm_apply _
  have hcompat : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorPow J hmn).comp (v n) = v m := by
    intro m n hmn
    apply RingHom.ext
    intro x
    apply (e m).injective
    change e m (Ideal.Quotient.factorPow J hmn (v n x)) = e m (v m x)
    apply funext
    intro i
    rw [s2t_coprimePowerQuotientEquiv_transition, hv, hv]
    exact s2t_adic_eval_transition (I i) hmn (x i)
  let g := AdicCompletion.liftRingHom J v hcompat
  have hg (n : ℕ) (x : ∀ i, AdicCompletion (I i) A) :
      AdicCompletion.evalₐ J n (g x) = v n x :=
    AdicCompletion.evalₐ_liftRingHom J v hcompat n x
  have heval (n : ℕ) (x : AdicCompletion J A) (i : ι) :
      AdicCompletion.evalₐ (I i) n (s2t_adicProductMap I x i) =
        e n (AdicCompletion.evalₐ J n x) i := by
    change AdicCompletion.evalₐ (I i) n
      (s2t_adicMap J (I i) (RingHom.id A) (iInf_le I i) x) = _
    rw [s2t_adicMap_eval]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ J n x)
    rw [← ha]
    rfl
  have hleft (x : AdicCompletion J A) : g (s2t_adicProductMap I x) = x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [hg]
    apply (e n).injective
    rw [hv]
    apply funext
    intro i
    exact heval n x i
  have hright (x : ∀ i, AdicCompletion (I i) A) : s2t_adicProductMap I (g x) = x := by
    apply funext
    intro i
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [heval, hg, hv]
    rfl
  exact ⟨Function.LeftInverse.injective hleft, Function.RightInverse.surjective hright⟩

/-- The ring isomorphism induced by the actual factor maps of a coprime intersection. -/
def s2t_adicProductEquiv {A ι : Type*} [CommRing A] [Fintype ι]
    (I : ι → Ideal A) (hI : Pairwise (IsCoprime on I)) :
    AdicCompletion (⨅ i, I i) A ≃+* ∀ i, AdicCompletion (I i) A :=
  RingEquiv.ofBijective (s2t_adicProductMap I) (s2t_adicProductMap_bijective I hI)

end HodgeLean.Foundations.Program
