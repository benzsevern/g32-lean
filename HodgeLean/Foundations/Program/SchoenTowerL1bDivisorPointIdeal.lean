import HodgeLean.Foundations.Program.SchoenTowerL1aPointSections
import Mathlib.AlgebraicGeometry.Stalk

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program

/-- The ideal of a complex point on an affine chart is its actual affine prime ideal. -/
theorem s2v_l1b_divisor_point_ideal_affine
    (Z : Over (Spec ↧ℂ)) (b : ComplexPoint Z) (U : Z.left.affineOpens)
    (hb : b.underlying ∈ U.1) :
    b.left.ker.ideal U = (U.2.primeIdealOf ⟨b.underlying, hb⟩).asIdeal := by
  have hpre : b.left ⁻¹ᵁ U.1 = ⊤ := by
    apply top_unique
    intro q _
    change b.left q ∈ U.1
    rw [Subsingleton.elim (α := Spec ↧ℂ) q (closedPoint ℂ)]
    exact hb
  have htop : ⊤ ≤ b.left ⁻¹ᵁ U.1 := by rw [hpre]
  letI : IsIso (homOfLE htop) := homOfLE_isIso_of_eq htop hpre.symm
  have hc : Z.left.presheaf.germ U.1 b.underlying hb ≫ b.stalkHom =
      b.left.appLE U.1 ⊤ htop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom := by
    change Z.left.presheaf.germ U.1 (b.left (closedPoint ℂ)) hb ≫
      Scheme.stalkClosedPointTo b.left = _
    erw [Scheme.germ_stalkClosedPointTo (f := b.left)]
    dsimp only [Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
    simp only [Category.assoc]
    congr 2
  have hk : RingHom.ker b.stalkHom.hom = maximalIdeal (Z.left.presheaf.stalk b.underlying) := by
    change (⊥ : Ideal ℂ).comap b.stalkHom.hom = _
    rw [← maximalIdeal_eq_bot (R := ℂ), maximalIdeal_comap]
  rw [Scheme.Hom.ker_apply]
  have hker : RingHom.ker (b.left.app U.1).hom =
      RingHom.ker (b.left.appLE U.1 ⊤ htop).hom := by
    change RingHom.ker (b.left.app U.1).hom =
      RingHom.ker (((Spec ↧ℂ).presheaf.map (homOfLE htop).op).hom.comp (b.left.app U.1).hom)
    exact (RingHom.ker_equiv_comp (b.left.app U.1).hom
      (asIso ((Spec ↧ℂ).presheaf.map (homOfLE htop).op)).commRingCatIsoToRingEquiv).symm
  rw [hker, ← RingHom.ker_equiv_comp (b.left.appLE U.1 ⊤ htop).hom
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv]
  change RingHom.ker (b.left.appLE U.1 ⊤ htop ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom = _
  rw [← hc]
  change (RingHom.ker b.stalkHom.hom).comap (Z.left.presheaf.germ U.1 b.underlying hb).hom = _
  rw [hk, U.2.primeIdealOf_eq_map_closedPoint]
  rfl

end HodgeLean.Foundations.Program
