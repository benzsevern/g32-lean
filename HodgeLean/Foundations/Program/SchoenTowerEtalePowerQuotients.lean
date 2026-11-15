import HodgeLean.Foundations.Program.SchoenTowerEtaleNilpotent
import HodgeLean.Foundations.Program.SchoenTowerAdicMapEquiv

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- A formally étale map bijective on the first ideal quotient is bijective on every
power quotient, with the actual inclusion-induced quotient maps.
Source: EGA IV, 17.1.1, infinitesimal lifting for étale morphisms. -/
theorem s2t_etale_power_quotient_bijective {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallyEtale R S]
    (I : Ideal R)
    (hbij : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap ((I.map (algebraMap R S)) ^ n)
      (algebraMap R S) (s2t_adicMap_pow I _ _ Ideal.le_comap_map n)) := by
  let J := I.map (algebraMap R S)
  let q₁ : R ⧸ I →ₐ[R] S ⧸ J :=
    Ideal.quotientMapₐ J (Algebra.ofId R S) Ideal.le_comap_map
  let e : (R ⧸ I) ≃ₐ[R] (S ⧸ J) := AlgEquiv.ofBijective q₁ hbij
  let q : R ⧸ I ^ n →ₐ[R] S ⧸ J ^ n :=
    Ideal.quotientMapₐ (J ^ n) (Algebra.ofId R S)
      (s2t_adicMap_pow I J _ Ideal.le_comap_map n)
  change Function.Bijective q
  by_cases hn : n = 0
  · subst n
    haveI : Subsingleton (R ⧸ I ^ 0) := by rw [pow_zero, Ideal.one_eq_top]; infer_instance
    haveI : Subsingleton (S ⧸ J ^ 0) := by rw [pow_zero, Ideal.one_eq_top]; infer_instance
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨0, Subsingleton.elim _ _⟩⟩
  · let f₀ : S →ₐ[R] R ⧸ I := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R J)
    let p : R ⧸ I ^ n →ₐ[R] R ⧸ I := Ideal.Quotient.factorₐ R (I.pow_le_self hn)
    let f : S →ₐ[R] R ⧸ I ^ n := Algebra.FormallySmooth.liftOfSurjective f₀ p
      (Ideal.Quotient.factor_surjective (I.pow_le_self hn)) (s2t_adic_firstReduction_nilpotent I n hn)
    have hf : p.comp f = f₀ := Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
    have hk : J ^ n ≤ RingHom.ker f.toRingHom := by
      change (I.map (algebraMap R S)) ^ n ≤ _
      rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
      intro r hr
      change f (algebraMap R S r) = 0
      rw [f.commutes]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
    have hcomm (z : R ⧸ I ^ n) :
        Ideal.Quotient.factor (J.pow_le_self hn) (q z) = q₁ (p z) := by
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
      rfl
    have heq : q.comp f = Ideal.Quotient.mkₐ R (J ^ n) := by
      apply Algebra.FormallyUnramified.lift_unique_of_ringHom
        (Ideal.Quotient.factor (J.pow_le_self hn)) (s2t_adic_firstReduction_nilpotent J n hn)
      ext s
      change Ideal.Quotient.factor (J.pow_le_self hn) (q (f s)) = Ideal.Quotient.mk J s
      rw [hcomm]
      calc
        q₁ (p (f s)) = q₁ (f₀ s) := congrArg q₁ (congrArg (fun k : S →ₐ[R] R ⧸ I => k s) hf)
        _ = Ideal.Quotient.mk J s := e.apply_symm_apply _
    constructor
    · apply (injective_iff_map_eq_zero q.toRingHom).mpr
      intro x hx
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hr : algebraMap R S r ∈ J ^ n := Ideal.Quotient.eq_zero_iff_mem.mp hx
      have hh : f (algebraMap R S r) = 0 := hk hr
      rw [f.commutes] at hh
      exact hh
    · intro x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨f s, congrArg (fun k : S →ₐ[R] S ⧸ J ^ n => k s) heq⟩

/-- A formally étale map identifying the first ideal quotients induces an adic ring
isomorphism along the extended ideal.
Source: EGA IV, 17.1.1, infinitesimal lifting for étale morphisms. -/
def s2t_etaleAdicEquiv {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallyEtale R S]
    (I : Ideal R)
    (hbij : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    AdicCompletion I R ≃+* AdicCompletion (I.map (algebraMap R S)) S :=
  RingEquiv.ofBijective (s2t_adicMap I (I.map (algebraMap R S))
    (algebraMap R S) Ideal.le_comap_map)
    (s2t_adicMap_bijective_of_residues I _ _ Ideal.le_comap_map
      (s2t_etale_power_quotient_bijective I hbij))

end HodgeLean.Foundations.Program
