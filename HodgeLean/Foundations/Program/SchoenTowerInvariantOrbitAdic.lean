import HodgeLean.Foundations.Program.SchoenTowerOrbitRadical
import HodgeLean.Foundations.Program.SchoenTowerAdicCofinal
import HodgeLean.Foundations.Program.SchoenTowerAdicProduct
import HodgeLean.Foundations.Program.SchoenTowerAdicFunctor
import Mathlib.RingTheory.Noetherian.Basic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Pointwise

namespace HodgeLean.Foundations.Program

/-- The adic ring over an invariant-base image point decomposes over the distinct maximal
ideals in its actual orbit. -/
def s2t_invariantOrbitAdicEquiv {R A G : Type*}
    [CommRing R] [CommRing A] [IsNoetherianRing A] [Algebra R A]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.IsInvariant R A G] (q : Ideal A) [q.IsMaximal] :
    AdicCompletion ((q.under R).map (algebraMap R A)) A ≃+*
      ∀ i : MulAction.orbit G q, AdicCompletion (i : Ideal A) A := by
  classical
  letI : Fintype (MulAction.orbit G q) :=
    (Finite.finite_mulAction_orbit (M := G) q).fintype
  let I := (q.under R).map (algebraMap R A)
  let J := ⨅ i : MulAction.orbit G q, (i : Ideal A)
  have hrad : I.radical = J := s2t_radical_extended_maximal_eq_distinctOrbit (R := R) (G := G) q
  have hIJ : I ≤ J := Ideal.le_radical.trans hrad.le
  have hbij := s2t_adicMap_bijective_of_le_radical I J hIJ hrad.symm.le
    J.fg_of_isNoetherianRing
  exact (RingEquiv.ofBijective (s2t_adicMap I J (RingHom.id A) hIJ) hbij).trans
    (s2t_adicProductEquiv (fun i : MulAction.orbit G q => (i : Ideal A))
      (s2t_orbit_maximal_pairwise_coprime q))

/-- Each orbit-product coordinate is the canonical adic map from the extended image-point ideal. -/
theorem s2t_invariantOrbitAdicEquiv_apply {R A G : Type*}
    [CommRing R] [CommRing A] [IsNoetherianRing A] [Algebra R A]
    [Group G] [Finite G] [MulSemiringAction G A] [SMulCommClass G R A]
    [Algebra.IsInvariant R A G] (q : Ideal A) [q.IsMaximal]
    (x : AdicCompletion ((q.under R).map (algebraMap R A)) A)
    (i : MulAction.orbit G q) :
    s2t_invariantOrbitAdicEquiv (R := R) (G := G) q x i =
      s2t_adicMap ((q.under R).map (algebraMap R A)) (i : Ideal A) (RingHom.id A)
        (s2t_extended_under_le_orbit (R := R) q i) x := by
  classical
  letI : Fintype (MulAction.orbit G q) :=
    (Finite.finite_mulAction_orbit (M := G) q).fintype
  let M := (q.under R).map (algebraMap R A)
  let J := ⨅ j : MulAction.orbit G q, (j : Ideal A)
  have hrad : M.radical = J := s2t_radical_extended_maximal_eq_distinctOrbit (R := R) (G := G) q
  have hMJ : M ≤ J := Ideal.le_radical.trans hrad.le
  change s2t_adicMap J (i : Ideal A) (RingHom.id A)
    (iInf_le (fun j : MulAction.orbit G q => (j : Ideal A)) i)
    (s2t_adicMap M J (RingHom.id A) hMJ x) = _
  rw [s2t_adicMap_comp]
  rfl

end HodgeLean.Foundations.Program
