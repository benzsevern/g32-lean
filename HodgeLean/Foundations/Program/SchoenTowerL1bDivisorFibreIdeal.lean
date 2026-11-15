import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCoordinateParameter
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorIdealUnit
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorIdealProduct

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters IsLocalRing
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- At a coordinate-fibre generic point, the full incidence ideal pulls back to the single curve maximal ideal. -/
theorem s2v_l1b_divisor_coordinate_fibre_ideal
    (Z B : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1) (h : ℕ)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ σ, s2_permute Z (h + 1) σ ≫ γ = γ)
    (hγ : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power Z (h + 1) ⟶ T),
      (∀ σ, s2_permute Z (h + 1) σ ≫ f = f) → ∃! b : B ⟶ T, γ ≫ b = f)
    (b : ComplexPoint Z) (i : Fin (h + 1))
    (y : (g3_power Z (h + 1)).left) (hy : Order.coheight y = 1)
    (hyi : (g3_proj Z (h + 1) i).left y = b.underlying)
    (U : B.left.affineOpens) (hyU : γ.left y ∈ U.1) :
    (((s2c_branchIdeal Z B h γ b).ideal U).map
      (B.left.presheaf.germ U.1 (γ.left y) hyU).hom).map (γ.left.stalkMap y).hom =
      (maximalIdeal (Z.left.presheaf.stalk ((g3_proj Z (h + 1) i).left y))).map
        ((g3_proj Z (h + 1) i).left.stalkMap y).hom := by
  classical
  let X := (g3_power Z (h + 1)).left
  let I (j : Fin (h + 1)) := b.left.ker.comap (g3_proj Z (h + 1) j).left
  obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : X.Opens) from trivial)
  let Vb : X.affineOpens := ⟨V, hV⟩
  have hleft := s2v_l1b_divisor_comap_ideal_germ γ.left
    (s2c_branchIdeal Z B h γ b) y U Vb hyU hyV
  rw [s2v_l1a_pre_local_to_global_aux Z B hdimZ h γ hγsurj hγinv hγ b] at hleft
  have hunit (j : Fin (h + 1)) (hji : j ≠ i) :
      ((I j).ideal Vb).map (X.presheaf.germ V y hyV).hom = ⊤ := by
    apply s2v_l1b_divisor_ideal_germ_top X (I j) Vb y hyV
    intro H
    have Hj : (g3_proj Z (h + 1) j).left y ∈ (b.left.ker.support : Set Z.left) := by
      change y ∈ (b.left.ker.comap (g3_proj Z (h + 1) j).left).support at H
      rw [Scheme.IdealSheafData.support_comap] at H
      exact H
    rw [s2v_l1b_divisor_complex_point_kernel_support] at Hj
    have Hje : (g3_proj Z (h + 1) j).left y = b.underlying := Hj
    have Hjgen := s2v_l1b_divisor_other_coordinates_generic Z hdimZ h b i y hy hyi j hji
    exact s2v_l1b_divisor_curve_complex_ne_generic Z hdimZ b (Hje.symm.trans Hjgen)
  have hprod : (∏ j, ((I j).ideal Vb).map (X.presheaf.germ V y hyV).hom) =
      ((I i).ideal Vb).map (X.presheaf.germ V y hyV).hom := by
    apply Finset.prod_eq_single i
    · intro j _ hji
      simpa only [Ideal.one_eq_top] using hunit j hji
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  obtain ⟨C, hC, hbC, _⟩ := exists_isAffineOpen_mem_and_subset
    (show b.underlying ∈ (⊤ : Z.left.Opens) from trivial)
  let Cb : Z.left.affineOpens := ⟨C, hC⟩
  have hyC : (g3_proj Z (h + 1) i).left y ∈ C := hyi.symm ▸ hbC
  have hright := s2v_l1b_divisor_comap_ideal_germ (g3_proj Z (h + 1) i).left
    b.left.ker y Cb Vb hyC hyV
  have hpoint (q : Z.left) (he : b.underlying = q) (hq : q ∈ C) :
      (b.left.ker.ideal Cb).map (Z.left.presheaf.germ C q hq).hom =
        maximalIdeal (Z.left.presheaf.stalk q) := by
    subst q
    exact s2v_l1b_divisor_point_ideal_germ Z b Cb hq
  rw [hpoint _ hyi.symm hyC] at hright
  calc
    _ = ((∏ j, I j).ideal Vb).map (X.presheaf.germ V y hyV).hom := hleft.symm
    _ = ∏ j, ((I j).ideal Vb).map (X.presheaf.germ V y hyV).hom :=
      s2v_l1b_divisor_ideal_germ_product X I Vb y hyV
    _ = ((I i).ideal Vb).map (X.presheaf.germ V y hyV).hom := hprod
    _ = _ := hright

end HodgeLean.Foundations.Program
