import HodgeLean.Foundations.Program.SchoenTowerEtalePowerQuotients

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- A formally étale map identifying specified first quotients identifies their power
quotients, including a selected component of an étale fibre. -/
theorem s2t_etale_selected_power_quotient_bijective {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallyEtale R S]
    (I : Ideal R) (J : Ideal S) (h : I ≤ J.comap (algebraMap R S))
    (hbij : Function.Bijective (Ideal.quotientMap J (algebraMap R S) h)) (n : ℕ) :
    Function.Bijective (Ideal.quotientMap (J ^ n) (algebraMap R S)
      (s2t_adicMap_pow I J _ h n)) := by
  let q₁ : R ⧸ I →ₐ[R] S ⧸ J :=
    Ideal.quotientMapₐ J (Algebra.ofId R S) h
  let e : (R ⧸ I) ≃ₐ[R] (S ⧸ J) := AlgEquiv.ofBijective q₁ hbij
  let q : R ⧸ I ^ n →ₐ[R] S ⧸ J ^ n :=
    Ideal.quotientMapₐ (J ^ n) (Algebra.ofId R S)
      (s2t_adicMap_pow I J _ h n)
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
      have hJ : J ≤ (RingHom.ker p.toRingHom).comap f.toRingHom := by
        intro s hs
        change p (f s) = 0
        have he := congrArg (fun k : S →ₐ[R] R ⧸ I => k s) hf
        change p (f s) = f₀ s at he
        rw [he]
        change e.symm (Ideal.Quotient.mk J s) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hs, map_zero]
      have hp : (RingHom.ker p.toRingHom) ^ n = 0 := by
        change (RingHom.ker (Ideal.Quotient.factor (I.pow_le_self hn))) ^ n = 0
        rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, Ideal.map_quotient_self]
        rfl
      have hmap : (J ^ n).map f.toRingHom ≤ 0 := by
        rw [Ideal.map_pow]
        exact (Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hJ) n).trans_eq hp
      exact Ideal.map_le_iff_le_comap.mp hmap
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

/-- The actual adic map at specified quotient ideals is bijective when the formally étale
map identifies their first quotients. -/
theorem s2t_etale_selected_adicMap_bijective {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallyEtale R S]
    (I : Ideal R) (J : Ideal S) (h : I ≤ J.comap (algebraMap R S))
    (hbij : Function.Bijective (Ideal.quotientMap J (algebraMap R S) h)) :
    Function.Bijective (s2t_adicMap I J (algebraMap R S) h) := by
  exact s2t_adicMap_bijective_of_residues I J (algebraMap R S) h
    (s2t_etale_selected_power_quotient_bijective I J h hbij)

end HodgeLean.Foundations.Program
