import HodgeLean.Foundations.Program.SchoenTowerInvariantAdicComparison
import HodgeLean.Foundations.Program.SchoenTowerClosedResidues
import HodgeLean.Foundations.Program.SchoenTowerEtaleAdicMapCriterion
import HodgeLean.Foundations.Program.SchoenInvariantFiniteType

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Pointwise

namespace HodgeLean.Foundations.Program

/-- An equivariant étale map over an algebraically closed field induces an étale map
of invariant rings at a maximal ideal with unchanged stabilizer. -/
theorem s2t_invariant_isEtaleAt {K A B G : Type}
    [Field K] [IsAlgClosed K] [CharZero K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra.FiniteType K A] [Algebra.FiniteType K B]
    [Group G] [Fintype G] [MulSemiringAction G A] [MulSemiringAction G B]
    [SMulCommClass G K A] [SMulCommClass G K B]
    (f : A →ₐ[K] B) (heq : ∀ (g : G) (a : A), f (g • a) = g • f a)
    (qA : Ideal A) (qB : Ideal B) [qA.IsMaximal] [qB.IsMaximal]
    (h : qA ≤ qB.comap f.toRingHom) (hEt : f.toRingHom.FormallyEtale)
    (hstab : ∀ g : G, g • qA = qA ↔ g • qB = qB) :
    let RA := FixedPoints.subalgebra K A G
    let RB := FixedPoints.subalgebra K B G
    letI := (s2t_fixedSubalgebraMap f heq).toRingHom.toAlgebra
    Algebra.IsEtaleAt RA (qB.under RB) := by
  let RA := FixedPoints.subalgebra K A G
  let RB := FixedPoints.subalgebra K B G
  let F := s2t_fixedSubalgebraMap f heq
  letI : Algebra RA RB := F.toRingHom.toAlgebra
  letI : IsScalarTower K RA RB := IsScalarTower.of_algebraMap_eq (fun k => (F.commutes k).symm)
  letI : Algebra.FiniteType K RA := s2_fixedAlgebra_finiteType K A G
  letI : Algebra.FiniteType K RB := s2_fixedAlgebra_finiteType K B G
  letI : IsNoetherianRing RA := Algebra.FiniteType.isNoetherianRing K RA
  letI : IsNoetherianRing RB := Algebra.FiniteType.isNoetherianRing K RB
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  letI : Algebra.FiniteType RA RB := Algebra.FiniteType.of_restrictScalars_finiteType K RA RB
  letI : Algebra.FinitePresentation RA RB := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let pA := qA.under RA
  let pB := qB.under RB
  letI : Algebra.IsIntegral RA A := Algebra.IsInvariant.isIntegral RA A G
  letI : Algebra.IsIntegral RB B := Algebra.IsInvariant.isIntegral RB B G
  letI : pA.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := RA) qA
  letI : pB.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := RB) qB
  have hF : pA ≤ pB.comap (algebraMap RA RB) := fun _ ha => h ha
  letI : pB.LiesOver pA := by
    apply (Ideal.liesOver_iff _ _).mpr
    exact (Ideal.IsMaximal.eq_of_le inferInstance
      (Ideal.comap_ne_top (algebraMap RA RB) (Ideal.IsMaximal.ne_top inferInstance)) hF)
  have hres := s2t_quotientMap_bijective_of_algClosed f qA qB h
  have hbij := s2t_invariant_adicMap_bijective_of_etale f heq qA qB h hEt hres hstab
  letI := Localization.AtPrime.algebraOfLiesOver pA pB
  let Rp := Localization.AtPrime pA
  let Sq := Localization.AtPrime pB
  letI : IsScalarTower K RA Sq := IsScalarTower.to₁₂₄ K RA RB Sq
  letI : IsScalarTower K Rp Sq := IsScalarTower.to₁₃₄ K RA Rp Sq
  letI : Module.Finite K (IsLocalRing.ResidueField Sq) := s2t_atPrimeResidue_finite pB
  letI : Algebra.IsSeparable (IsLocalRing.ResidueField Rp) (IsLocalRing.ResidueField Sq) :=
    s2t_residue_separable_of_algClosed (K := K)
  exact s2t_isEtaleAt_of_adicMap_bijective pA pB hF hbij

end HodgeLean.Foundations.Program
