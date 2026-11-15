import HodgeLean.Foundations.Program.SchoenCycleC1InitialCardHelpers

/-! # Freeness above the actual unmarked initial base locus -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Every point of the actual initial cover above the unmarked base locus
has no positive residual generator return below the covering degree. -/
theorem s2e_c1_initial_free_off_marks
    (S : g32p_Supplier) (Y Z W B : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    [IsIntegral W.left] [IsProjective W.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (p : Y ⟶ Z) (hp : ∀ u, a u ≫ p = p)
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p x = Point.map p y ↔
      ∃ u, Point.map (a u) x = y)
    (T I : Type*) [MulAction (S.H ⧸ S.χ.ker) T]
    (eY : T ≃ ComplexPoint Y)
    (hpointAction : ∀ u z, Point.map (a u) (eY z) = eY (u • z))
    (marks : I → ComplexPoint Z)
    (hbranch : ∀ z : T, MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
      ∃ i, Point.map p (eY z) = marks i)
    (h : ℕ) (hh : 0 < h + 1)
    (q : g3_power Y (h + 1) ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
      ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ q = q)
    (hq : ∀ (A : Over (Spec ↧ℂ)) (f : g3_power Y (h + 1) ⟶ A),
      (∀ (v : Fin (h + 1) → ZMod S.m) (τ : Equiv.Perm (Fin (h + 1))),
        ∑ t, v t = 0 → s2_action S Y a e (h + 1) v τ ≫ f = f) →
      ∃! u : W ⟶ A, q ≫ u = f)
    (γ : g3_power Z (h + 1) ⟶ B) [IsFinite γ.left]
    (hγinv : ∀ τ, s2_permute Z (h + 1) τ ≫ γ = γ)
    (β : W ⟶ B) (hβ : q ≫ β = s2_powerMap p (h + 1) ≫ γ)
    (d : W ⟶ W)
    (hgenerator : q ≫ d = s2_action S Y a e (h + 1) (s2_delta S (h + 1) hh 1) 1 ≫ q)
    (w : ComplexPoint W)
    (hw : ∀ i, (Point.map β w).underlying ∉
      (s2c_branchIdeal Z B h γ (marks i)).support)
    (n : ℕ) (hn : n < S.m) (hfix : (Point.map d)^[n] w = w) : n = 0 := by
  obtain ⟨x, hx⟩ := hqsurj w
  have hfree (j : Fin (h + 1)) : Function.Injective (fun u =>
      Point.map (a u) (Point.map (g3_proj Y (h + 1) j) x)) := by
    let y := Point.map (g3_proj Y (h + 1) j) x
    have hav (i : I) : Point.map p y ≠ marks i := by
      intro hi
      apply hw i
      have hcoord : Point.map (g3_proj Z (h + 1) j)
          (Point.map (s2_powerMap p (h + 1)) x) = marks i := by
        exact (s2_powerComplexPointEquiv_powerMap p (h + 1) x j).trans hi
      have hm := s2e_c1_marked_coordinate_mem_branch_support Z B h γ hγinv
        (marks i) (Point.map (s2_powerMap p (h + 1)) x) j hcoord
      have he : Point.map γ (Point.map (s2_powerMap p (h + 1)) x) = Point.map β w := by
        rw [← Point.map_comp_apply, ← hβ, Point.map_comp_apply, hx]
      simpa only [← Point.underlying_map, he] using hm
    have ht := s2e_c1_curve_orbit_injective_off_marks S Y Z a p T I eY hpointAction
      marks hbranch (eY.symm y) (by simpa only [eY.apply_symm_apply] using hav)
    simpa only [eY.apply_symm_apply] using ht
  apply s2e_c1_initial_fixed_iterate_zero S Y Z W a e ha1 hamul p hp hporbit
    (h + 1) hh q hqsurj hqinv hq d hgenerator x hfree n hn
  simpa only [hx] using hfix

end HodgeLean.Foundations.Program
