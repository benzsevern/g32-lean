import HodgeLean.Foundations.Program.SchoenTowerI2aNormalCover

/-! # Transporting a normal-cover generator action to inertia
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A normal cover containing the original field generator transfers its fixed evaluation to every original integral element.
Source: Mathlib, IsFractionRing.liftAlgHom, IsFractionRing.algEquivOfAlgEquiv and integral-closure functoriality. -/
theorem s2v_i2a_normal_generator_inertia
    {R K A L C : Type*} [CommRing R] [Field K] [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field L] [CommRing C]
    [Algebra R K] [Algebra R A] [Algebra R L]
    (v : K) (hgen : Subfield.closure (Set.range (algebraMap R K) ∪ {v}) = ⊤)
    (f : K →ₐ[R] L) (σ : A →ₐ[R] L) (hinj : Function.Injective σ)
    (V : A) (hV : σ V = f v) (t : R)
    (d : K ≃ₐ[R] K) (hd : d v = algebraMap R K t * v)
    (G : A ≃ₐ[R] A) (hG : G V = algebraMap R A t * V)
    (p : integralClosure R K →+* C) (q : A →+* C)
    (hq : ∀ a, q (G a) = q a)
    (hp : ∀ a (b : integralClosure R K), σ a = f (b : K) → q a = p b) :
    ∀ b, p (d.mapIntegralClosure b) = p b := by
  let F := FractionRing A
  let σF : F →ₐ[R] L := IsFractionRing.liftAlgHom hinj
  have hσF (a : A) : σF (algebraMap A F a) = σ a :=
    IsFractionRing.lift_algebraMap hinj a
  obtain ⟨fF, hfF⟩ := s2v_i2a_lift_generated_field v hgen f σF
    ⟨algebraMap A F V, (hσF V).trans hV⟩
  have hfF' (x : K) : σF (fF x) = f x := AlgHom.congr_fun hfF x
  have hVF : fF v = algebraMap A F V := by
    apply σF.injective
    change σF (fF v) = σF (algebraMap A F V)
    rw [hfF', hσF, hV]
  obtain ⟨β, hβ⟩ := s2v_i2a_integralClosure_lift_to_normal_cover (A := A) fF
  let GF : F ≃ₐ[R] F := IsFractionRing.algEquivOfAlgEquiv G
  have hGF (a : A) : GF (algebraMap A F a) = algebraMap A F (G a) :=
    IsFractionRing.algEquivOfAlgEquiv_algebraMap G a
  have hgenaction : GF (fF v) = fF (d v) := by
    rw [hVF, hGF, hG, map_mul, ← IsScalarTower.algebraMap_apply R A F,
      hd, map_mul, fF.commutes, hVF]
  have hpβ (b : integralClosure R K) : p b = q (β b) := by
    symm
    apply hp
    rw [← hσF, hβ, hfF']
  exact s2v_i2a_normal_cover_inertia v hgen fF
    (IsScalarTower.toAlgHom R A F) (IsFractionRing.injective A F) β hβ
    d G GF (fun a => (hGF a).symm) hgenaction p q hpβ hq

end HodgeLean.Foundations.Program
