import HodgeLean.Foundations.Program.SchoenCycleC1FreePointHelpers
import HodgeLean.Foundations.Program.SchoenCycleBranchOffSupport

/-! # Nonempty complements of the actual marked branch supports -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The retained stabilizer criterion and faithful action supply a curve
point whose projection avoids every marked value. -/
theorem s2e_c1_exists_curve_point_off_marks
    (S : g32p_Supplier) (Y Z : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a) (p : Y ⟶ Z)
    (T I : Type*) [MulAction (S.H ⧸ S.χ.ker) T]
    (eY : T ≃ ComplexPoint Y)
    (hpointAction : ∀ u z, Point.map (a u) (eY z) = eY (u • z))
    (marks : I → ComplexPoint Z)
    (hbranch : ∀ z : T, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
      ∃ i, Point.map p (eY z) = marks i) :
    ∃ z : ComplexPoint Y, ∀ i, Point.map p z ≠ marks i := by
  obtain ⟨z, hfree⟩ := s2e_c1_exists_free_complex_point Y (S.H ⧸ S.χ.ker) a ha1 hamul hinj
  let t := eY.symm z
  have hstab : MulAction.stabilizer (S.H ⧸ S.χ.ker) t = ⊥ := by
    apply bot_unique
    intro u hu
    change u = 1
    have hu' : u • t = t := hu
    have hact : Point.map (a u) z = z := by
      have hh := (hpointAction u t).trans (congrArg eY hu')
      simpa only [t, eY.apply_symm_apply] using hh
    apply hfree
    change Point.map (a u) z = Point.map (a 1) z
    rw [ha1, Point.map_id]
    exact hact
  refine ⟨z, ?_⟩
  intro i hi
  have hn := (hbranch t).mpr ⟨i, by simpa only [t, eY.apply_symm_apply] using hi⟩
  exact hn hstab

/-- The actual initial symmetric base has a complex point outside every
marked branch support. -/
theorem s2e_c1_exists_initial_base_point_off_branches
    (S : g32p_Supplier) (Y Z B : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a) (p : Y ⟶ Z)
    (T I : Type*) [MulAction (S.H ⧸ S.χ.ker) T]
    (eY : T ≃ ComplexPoint Y)
    (hpointAction : ∀ u z, Point.map (a u) (eY z) = eY (u • z))
    (marks : I → ComplexPoint Z)
    (hbranch : ∀ z : T, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
      ∃ i, Point.map p (eY z) = marks i)
    (n : ℕ) (γ : g3_power Z (n + 1) ⟶ B) [IsFinite γ.left]
    (hγsurj : Function.Surjective (Point.map γ))
    (hγinv : ∀ τ, s2_permute Z (n + 1) τ ≫ γ = γ)
    (hγ : ∀ (A : Over (Spec ↧ℂ)) (f : g3_power Z (n + 1) ⟶ A),
      (∀ τ, s2_permute Z (n + 1) τ ≫ f = f) → ∃! u : B ⟶ A, γ ≫ u = f) :
    ∃ b : ComplexPoint B, ∀ i, b.underlying ∉ (s2c_branchIdeal Z B n γ (marks i)).support := by
  obtain ⟨z, hz⟩ := s2e_c1_exists_curve_point_off_marks S Y Z a ha1 hamul hinj p
    T I eY hpointAction marks hbranch
  let x : ComplexPoint (g3_power Z (n + 1)) := s2_lift (n + 1) (fun _ => Point.map p z)
  haveI : Surjective γ.left := s2e_step1_surjective_of_complexPoint_surjective _ _ γ hγsurj
  refine ⟨Point.map γ x, ?_⟩
  intro i
  have hx (j : Fin (n + 1)) : Point.map (g3_proj Z (n + 1) j) x ≠ marks i := by
    rw [show Point.map (g3_proj Z (n + 1) j) x = Point.map p z from
      s2_check_lift_proj (n + 1) (fun _ => Point.map p z) j]
    exact hz i
  simpa only [Point.underlying_map] using
    s2e_branch_support_excludes_unmarked_tuple Z B n γ hγinv hγ x (marks i) hx

end HodgeLean.Foundations.Program
