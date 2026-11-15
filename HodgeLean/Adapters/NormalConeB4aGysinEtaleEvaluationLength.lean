import HodgeLean.Adapters.NormalConeB4aGysinFiniteEvaluationLength
import HodgeLean.Adapters.NormalConeB4aGysinModelStalk

noncomputable section
namespace HodgeLean.Adapters

set_option backward.isDefEq.respectTransparency.types false in
/-- Compatible complex evaluations in an etale change of base and source
have equal full local parameter quotient lengths. -/
theorem a3b4a_gysin_etale_evaluation_slice_length
    {A B S T : Type} [CommRing A] [CommRing B] [CommRing S] [CommRing T]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ S] [Algebra ℂ T]
    [Algebra A B] [Algebra A S] [Algebra A T] [Algebra B T] [Algebra S T]
    [IsScalarTower A B T] [IsScalarTower A S T]
    [IsScalarTower ℂ A B] [IsScalarTower ℂ A S]
    [IsScalarTower ℂ B T] [IsScalarTower ℂ S T]
    [Algebra.Etale A B] [Algebra.Etale S T]
    (u : B →ₐ[ℂ] ℂ) (w : T →ₐ[ℂ] ℂ)
    (hw : w.comp (IsScalarTower.toAlgHom ℂ B T) = u) :
    a3b4a_gysin_evaluationSliceLength
      (u.comp (IsScalarTower.toAlgHom ℂ A B))
      (w.comp (IsScalarTower.toAlgHom ℂ S T)) =
        a3b4a_gysin_evaluationSliceLength u w := by
  let v := u.comp (IsScalarTower.toAlgHom ℂ A B)
  let z := w.comp (IsScalarTower.toAlgHom ℂ S T)
  let p := RingHom.ker v
  let P := RingHom.ker u
  let q := RingHom.ker z
  let r := RingHom.ker w
  letI : p.IsPrime := RingHom.ker_isPrime v
  letI : P.IsPrime := RingHom.ker_isPrime u
  letI : q.IsPrime := RingHom.ker_isPrime z
  letI : r.IsPrime := RingHom.ker_isPrime w
  letI : P.LiesOver p := ⟨(RingHom.comap_ker u.toRingHom (algebraMap A B)).symm⟩
  letI : r.LiesOver q := ⟨(RingHom.comap_ker w.toRingHom (algebraMap S T)).symm⟩
  letI : r.LiesOver P := by
    constructor
    change P = (RingHom.ker w.toRingHom).comap (algebraMap B T)
    rw [RingHom.comap_ker]
    exact (congrArg (fun f : B →ₐ[ℂ] ℂ => RingHom.ker f.toRingHom) hw).symm
  let Lq := Localization.AtPrime q
  let Lr := Localization.AtPrime r
  letI : Algebra (Localization.AtPrime P) Lr := Localization.AtPrime.algebraOfLiesOver P r
  haveI : IsScalarTower A (Localization.AtPrime P) Lr :=
    IsScalarTower.to₁₃₄ A B (Localization.AtPrime P) Lr
  have hid := congrArg (Ideal.map (algebraMap (Localization.AtPrime P) Lr))
    (a3b4a_gysin_etale_base_prime_ideal p P)
  simp_rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at hid
  have hsource := a3b4a_gysin_etale_localization_quotient_length q r
    (p.map (algebraMap A S))
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    Ideal.map_map, ← IsScalarTower.algebraMap_eq, hid] at hsource
  let Jq := p.map (algebraMap A Lq)
  let Jr := P.map (algebraMap B Lr)
  change Module.length Lq (Lq ⧸ Jq) = Module.length Lr (Lr ⧸ Jr)
  calc
    Module.length Lq (Lq ⧸ Jq) = Module.length (Lq ⧸ Jq) (Lq ⧸ Jq) :=
      Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
    _ = Module.length (Lr ⧸ Jr) (Lr ⧸ Jr) := hsource.symm
    _ = Module.length Lr (Lr ⧸ Jr) :=
      (Module.length_eq_of_surjective Ideal.Quotient.mk_surjective).symm

end HodgeLean.Adapters
