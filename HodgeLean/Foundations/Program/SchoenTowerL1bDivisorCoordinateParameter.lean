import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCoordinateGeneric
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorIdealGerm
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorPointIdealGerm

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters IsLocalRing
namespace HodgeLean.Foundations.Program

/-- The maximal ideal of a complex curve coordinate pulls back to a prime ideal at its coordinate-fibre generic point. -/
theorem s2v_l1b_divisor_coordinate_maximal_ideal_prime
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1) (n : ℕ)
    (b : ComplexPoint Z) (i : Fin (n + 1))
    (y : (g3_power Z (n + 1)).left) (hy : Order.coheight y = 1)
    (hyi : (g3_proj Z (n + 1) i).left y = b.underlying) :
    (Ideal.map ((g3_proj Z (n + 1) i).left.stalkMap y).hom
      (maximalIdeal (Z.left.presheaf.stalk ((g3_proj Z (n + 1) i).left y)))).IsPrime := by
  let X := (g3_power Z (n + 1)).left
  let f := (g3_proj Z (n + 1) i).left
  obtain ⟨U, hU, hbU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show b.underlying ∈ (⊤ : Z.left.Opens) from trivial)
  let Ub : Z.left.affineOpens := ⟨U, hU⟩
  have hyU : f y ∈ U := by simpa only [f, hyi] using hbU
  obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : X.Opens) from trivial)
  let Vb : X.affineOpens := ⟨V, hV⟩
  let ins := (s2c_branchInsertion Z n b ≫ s2_permute Z (n + 1) (Equiv.swap 0 i)).left
  have hygen : ins (genericPoint (g3_power Z n).left) = y :=
    (s2v_l1b_divisor_coordinate_fibre_generic Z hdimZ n b i y hy hyi).symm
  letI : Nonempty (ins ⁻¹ᵁ V) := ⟨⟨genericPoint _, by
    change ins (genericPoint _) ∈ V
    rwa [hygen]⟩⟩
  have hIp := s2v_l1b_divisor_coordinate_ideal_prime Z n b i Vb
  have H := s2v_l1b_divisor_comap_ideal_germ f b.left.ker y Ub Vb hyU hyV
  have Hpoint : (b.left.ker.ideal Ub).map (Z.left.presheaf.germ U (f y) hyU).hom =
      maximalIdeal (Z.left.presheaf.stalk (f y)) := by
    have hpoint (q : Z.left) (he : b.underlying = q) (hq : q ∈ U) :
        (b.left.ker.ideal Ub).map (Z.left.presheaf.germ U q hq).hom =
          maximalIdeal (Z.left.presheaf.stalk q) := by
      subst q
      exact s2v_l1b_divisor_point_ideal_germ Z b Ub hq
    exact hpoint (f y) hyi.symm hyU
  rw [Hpoint] at H
  let P := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
  letI : Algebra Γ(X, V) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨y, hyV⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk y) P := hV.isLocalization_stalk ⟨y, hyV⟩
  have hle : (b.left.ker.comap f).ideal Vb ≤ P := by
    change (b.left.ker.comap f).ideal Vb ≤ (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
    rw [hV.primeIdealOf_eq_map_closedPoint]
    apply Ideal.map_le_iff_le_comap.mp
    rw [H]
    exact IsLocalRing.map_maximalIdeal_le (f.stalkMap y).hom
  have hd : Disjoint (P.primeCompl : Set Γ(X, V)) ((b.left.ker.comap f).ideal Vb : Set Γ(X, V)) := by
    rw [Set.disjoint_left]
    intro a ha hI
    exact ha (hle hI)
  have hp := IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl
    (X.presheaf.stalk y) _ hIp hd
  change (((b.left.ker.comap f).ideal Vb).map (X.presheaf.germ V y hyV).hom).IsPrime at hp
  change ((b.left.ker.comap f).ideal Vb).map (X.presheaf.germ V y hyV).hom = _ at H
  exact H ▸ hp

end HodgeLean.Foundations.Program
