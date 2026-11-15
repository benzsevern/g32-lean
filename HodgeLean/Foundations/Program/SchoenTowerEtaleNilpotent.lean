import HodgeLean.Foundations.Program.SchoenTowerEtaleAdicLifting

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace HodgeLean.Foundations.Program

/-- A formally étale structure map is bijective if its reduction modulo a nilpotent ideal
is bijective.
Source: EGA IV, 17.1.1, infinitesimal lifting for étale morphisms. -/
theorem s2t_etale_bijective_of_nilpotent_reduction {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallyEtale R S]
    (I : Ideal R) (hI : IsNilpotent I)
    (hbij : Function.Bijective (Ideal.quotientMap (I.map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    Function.Bijective (algebraMap R S) := by
  let J := I.map (algebraMap R S)
  let q : R ⧸ I →ₐ[R] S ⧸ J :=
    Ideal.quotientMapₐ J (Algebra.ofId R S) Ideal.le_comap_map
  let e : (R ⧸ I) ≃ₐ[R] (S ⧸ J) := AlgEquiv.ofBijective q hbij
  let f₀ : S →ₐ[R] R ⧸ I := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R J)
  let f : S →ₐ[R] R := Algebra.FormallySmooth.lift I hI f₀
  have hf : (Ideal.Quotient.mkₐ R I).comp f = f₀ :=
    Algebra.FormallySmooth.comp_lift I hI f₀
  have hJ : IsNilpotent J := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    change (I.map (algebraMap R S)) ^ n = 0
    rw [← Ideal.map_pow, hn]
    exact Ideal.map_bot
  let u : S →ₐ[R] S := (Algebra.ofId R S).comp f
  have hu : (Ideal.Quotient.mkₐ R J).comp u =
      (Ideal.Quotient.mkₐ R J).comp (AlgHom.id R S) := by
    apply AlgHom.ext
    intro s
    change Ideal.Quotient.mk J (algebraMap R S (f s)) = Ideal.Quotient.mk J s
    calc
      Ideal.Quotient.mk J (algebraMap R S (f s)) = q (Ideal.Quotient.mk I (f s)) := rfl
      _ = q (f₀ s) := congrArg q (congrArg (fun k : S →ₐ[R] R ⧸ I => k s) hf)
      _ = Ideal.Quotient.mk J s := e.apply_symm_apply _
  have huid : u = AlgHom.id R S :=
    Algebra.FormallyUnramified.lift_unique J hJ u (AlgHom.id R S) hu
  constructor
  · intro x y hxy
    have h := congrArg f hxy
    simpa only [f.commutes, Algebra.algebraMap_self, RingHom.id_apply] using h
  · intro s
    exact ⟨f s, congrArg (fun k : S →ₐ[R] S => k s) huid⟩

end HodgeLean.Foundations.Program
