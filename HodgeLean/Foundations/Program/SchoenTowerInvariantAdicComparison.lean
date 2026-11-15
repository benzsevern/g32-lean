import HodgeLean.Foundations.Program.SchoenTowerCompletedStabilizer
import HodgeLean.Foundations.Program.SchoenTowerStabilizerRelabel
import HodgeLean.Foundations.Program.SchoenTowerEquivariantFixedMaps
import HodgeLean.Foundations.Program.SchoenTowerEtaleSelectedPowers
import HodgeLean.Foundations.Program.SchoenTowerAdicAlgHom

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Pointwise

namespace HodgeLean.Foundations.Program

/-- The actual map of invariant-base adic rings is bijective for an equivariant formally
étale map preserving the specified residue fields and stabilizers. -/
theorem s2t_invariant_adicMap_bijective_of_etale {K A B G : Type*}
    [Field K] [CharZero K] [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra K A] [Algebra K B]
    [Group G] [Fintype G] [MulSemiringAction G A] [MulSemiringAction G B]
    [SMulCommClass G K A] [SMulCommClass G K B]
    (f : A →ₐ[K] B) (heq : ∀ (g : G) (a : A), f (g • a) = g • f a)
    (qA : Ideal A) (qB : Ideal B) [qA.IsMaximal] [qB.IsMaximal]
    (h : qA ≤ qB.comap f.toRingHom) (hEt : f.toRingHom.FormallyEtale)
    (hres : Function.Bijective (Ideal.quotientMap qB f.toRingHom h))
    (hstab : ∀ g : G, g • qA = qA ↔ g • qB = qB) :
    let RA := FixedPoints.subalgebra K A G
    let RB := FixedPoints.subalgebra K B G
    let F := s2t_fixedSubalgebraMap f heq
    Function.Bijective (s2t_adicMap (qA.under RA) (qB.under RB) F.toRingHom
      (fun _ ha => h ha)) := by
  classical
  let RA := FixedPoints.subalgebra K A G
  let RB := FixedPoints.subalgebra K B G
  let F₀ := s2t_fixedSubalgebraMap f heq
  let hF₀ : qA.under RA ≤ (qB.under RB).comap F₀.toRingHom := fun _ ha => h ha
  let m := s2t_adicMap (qA.under RA) (qB.under RB) F₀.toRingHom hF₀
  change Function.Bijective m
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : Algebra.FormallyEtale A B := hEt
  letI : Fintype (MulAction.orbit G qA) := (Finite.finite_mulAction_orbit (M := G) qA).fintype
  letI : Fintype (MulAction.orbit G qB) := (Finite.finite_mulAction_orbit (M := G) qB).fintype
  let iA : MulAction.orbit G qA := ⟨qA, MulAction.mem_orbit_self qA⟩
  let iB : MulAction.orbit G qB := ⟨qB, MulAction.mem_orbit_self qB⟩
  let HA := MulAction.stabilizer G iA
  let HB := MulAction.stabilizer G iB
  letI : Fintype HA := Fintype.ofFinite HA
  letI : Fintype HB := Fintype.ofFinite HB
  let eH : HA ≃* HB := s2t_orbitStabilizerEquiv qA qB hstab
  let hqA := s2t_orbitStabilizerIdeal_stable qA iA
  let hqB := s2t_orbitStabilizerIdeal_stable qB iB
  letI := MulSemiringAction.compHom A HA.subtype
  letI := s2t_subgroup_action_smulCommClass (K := K) (A := A) HA
  letI := s2t_adicAction qA hqA
  letI := s2t_adicAction_smulCommClass (R := K) qA hqA
  letI := MulSemiringAction.compHom B HB.subtype
  letI := s2t_subgroup_action_smulCommClass (K := K) (A := B) HB
  letI := s2t_adicAction qB hqB
  letI := s2t_adicAction_smulCommClass (R := K) qB hqB
  let Fhat := s2t_adicMapAlgHom qA qB f h
  have hbijHat : Function.Bijective Fhat :=
    s2t_etale_selected_adicMap_bijective qA qB h hres
  have heqHat (g : HA) (x : AdicCompletion qA A) : Fhat (g • x) = eH g • Fhat x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ qB n
      (s2t_adicMap qA qB f.toRingHom h (s2t_adicActionHom qA hqA g x)) =
      AdicCompletion.evalₐ qB n
        (s2t_adicActionHom qB hqB (eH g) (s2t_adicMap qA qB f.toRingHom h x))
    rw [s2t_adicMap_eval, s2t_adicActionHom_eval qA hqA g,
      s2t_adicActionHom_eval qB hqB (eH g), s2t_adicMap_eval]
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ qA n x)
    rw [← ha]
    change Ideal.Quotient.mk (qB ^ n) (f ((g : G) • a)) =
      Ideal.Quotient.mk (qB ^ n) ((eH g : G) • f a)
    have hv : (eH g : G) = (g : G) := rfl
    rw [hv, heq]
  let eA := s2t_invariantBaseAdicStabilizerEquiv (K := K) qA iA
  let eB := s2t_invariantBaseAdicStabilizerEquiv (K := K) qB iB
  let eFixed := s2t_fixedSubalgebraEquivOfEquivariant eH Fhat hbijHat heqHat
  have hcomm (x : AdicCompletion (qA.under RA) RA) : eFixed (eA x) = eB (m x) := by
    apply Subtype.ext
    change s2t_adicMap qA qB f.toRingHom h
      (s2t_invariantBaseAdicStabilizerEquiv (K := K) qA iA x).val =
      (s2t_invariantBaseAdicStabilizerEquiv (K := K) qB iB (m x)).val
    rw [s2t_invariantBaseAdicStabilizerEquiv_apply, s2t_invariantBaseAdicStabilizerEquiv_apply]
    change s2t_adicMap qA qB f.toRingHom h
      (s2t_adicMap (qA.under RA) qA (algebraMap RA A) _ x) =
      s2t_adicMap (qB.under RB) qB (algebraMap RB B) _
        (s2t_adicMap (qA.under RA) (qB.under RB) F₀.toRingHom hF₀ x)
    rw [s2t_adicMap_comp, s2t_adicMap_comp]
    rfl
  constructor
  · intro x y hxy
    apply eA.injective
    apply eFixed.injective
    rw [hcomm, hcomm, hxy]
  · intro y
    refine ⟨eA.symm (eFixed.symm (eB y)), ?_⟩
    apply eB.injective
    rw [← hcomm, eA.apply_symm_apply, eFixed.apply_symm_apply]

end HodgeLean.Foundations.Program
