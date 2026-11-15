import HodgeLean.Adapters.NormalConeB4aGysinEtaleEvaluationLength

noncomputable section
namespace HodgeLean.Adapters

set_option backward.isDefEq.respectTransparency.types false in
/-- An etale source change preserves every parameter quotient length
at corresponding complex evaluations, with the parameter base fixed. -/
theorem a3b4a_gysin_etale_source_evaluation_slice_length
    {A S T : Type} [CommRing A] [CommRing S] [CommRing T]
    [Algebra ℂ A] [Algebra ℂ S] [Algebra ℂ T]
    [Algebra A S] [Algebra A T] [Algebra S T]
    [IsScalarTower A S T] [IsScalarTower ℂ S T]
    [Algebra.Etale S T]
    (u : A →ₐ[ℂ] ℂ) (v : T →ₐ[ℂ] ℂ) :
    a3b4a_gysin_evaluationSliceLength u (v.comp (IsScalarTower.toAlgHom ℂ S T)) =
      a3b4a_gysin_evaluationSliceLength u v := by
  let z := v.comp (IsScalarTower.toAlgHom ℂ S T)
  let q := RingHom.ker z
  let r := RingHom.ker v
  letI : q.IsPrime := RingHom.ker_isPrime z
  letI : r.IsPrime := RingHom.ker_isPrime v
  letI : r.LiesOver q := ⟨(RingHom.comap_ker v.toRingHom (algebraMap S T)).symm⟩
  let Lq := Localization.AtPrime q
  let Lr := Localization.AtPrime r
  let Iq := (RingHom.ker u).map (algebraMap A Lq)
  let Ir := (RingHom.ker u).map (algebraMap A Lr)
  have h := a3b4a_gysin_etale_localization_quotient_length q r
    ((RingHom.ker u).map (algebraMap A S))
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    Ideal.map_map, ← IsScalarTower.algebraMap_eq] at h
  change Module.length Lq (Lq ⧸ Iq) = Module.length Lr (Lr ⧸ Ir)
  calc
    Module.length Lq (Lq ⧸ Iq) = Module.length (Lq ⧸ Iq) (Lq ⧸ Iq) :=
      Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
    _ = Module.length (Lr ⧸ Ir) (Lr ⧸ Ir) := h.symm
    _ = Module.length Lr (Lr ⧸ Ir) :=
      (Module.length_eq_of_surjective Ideal.Quotient.mk_surjective).symm

end HodgeLean.Adapters
