import HodgeLean.Foundations.Program.SchoenTowerL1bKummerFreePoint
import HodgeLean.Foundations.Program.SchoenTowerL1bKummerResidualPowers
import HodgeLean.Foundations.Program.SchoenTowerI1aCategoricalOrbits
import HodgeLean.Foundations.Program.SchoenSumZeroActionFinite

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A faithful finite group of scheme symmetries has a rational point with injective orbit map. -/
theorem s2v_l1b_exists_injective_point_orbit
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsSeparated X.hom]
    [LocallyOfFiniteType X.hom] (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u) (hinj : Function.Injective a) :
    ∃ x : ComplexPoint X, Function.Injective (fun u => Point.map (a u) x) := by
  obtain ⟨x, hx⟩ := s2v_l1b_exists_point_moved_by_finite_family X
    {u : G // u ≠ 1} (fun u => a u.val) (fun u h => u.property (hinj (h.trans ha1.symm)))
  refine ⟨x, ?_⟩
  intro u v huv
  change Point.map (a u) x = Point.map (a v) x at huv
  have he : Point.map (a (v⁻¹ * u)) x = x := by
    change x ≫ a (v⁻¹ * u) = x
    rw [hamul, ← Category.assoc]
    change Point.map (a u) x ≫ a v⁻¹ = x
    rw [huv]
    change (x ≫ a v) ≫ a v⁻¹ = x
    rw [Category.assoc, ← hamul, inv_mul_cancel, ha1, Category.comp_id]
  have h : v⁻¹ * u = 1 := by
    by_contra hn
    exact hx ⟨v⁻¹ * u, hn⟩ he
  exact (inv_mul_eq_one.mp h).symm

/-- The residual generator has the full cyclic order, detected on a diagonal
of a rational point with injective orbit. -/
theorem s2v_l1b_residual_order_of_orbits
    (S : g32p_Supplier) (Y W : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a) (n : ℕ) (hn : 0 < n)
    (q : g3_power Y n ⟶ W) [Epi q] (d : W ⟶ W)
    (hgen : q ≫ d = s2_action S Y a e n (s2_delta S n hn 1) 1 ≫ q)
    (horbit : ∀ x y : ComplexPoint (g3_power Y n),
      Point.map q x = Point.map q y ↔
        ∃ (v : Fin n → ZMod S.m) (τ : Equiv.Perm (Fin n)),
          (∑ j, v j = 0) ∧ Point.map (s2_action S Y a e n v τ) x = y)
    (hm : 0 < S.m) : orderOf (End.of d) = S.m := by
  obtain ⟨z, hz⟩ := s2v_l1b_exists_injective_point_orbit Y _ a ha1 hamul hinj
  let t : ComplexPoint (g3_power Y n) := s2_lift n (fun _ => z)
  have hperiod (k : ℕ) (hk : End.of d ^ k = 1) : (k : ZMod S.m) = 0 := by
    have hqk := s2v_l1b_residual_generator_powers S Y W a e ha1 hamul n hn q d hgen k
    rw [hk] at hqk
    have hqt : Point.map q t = Point.map q
        (Point.map (s2_action S Y a e n (s2_delta S n hn (k : ZMod S.m)) 1) t) := by
      change t ≫ q = (t ≫ _) ≫ q
      rw [Category.assoc, ← hqk]
      rfl
    obtain ⟨v, τ, hv, hvt⟩ := (horbit _ _).mp hqt
    have he : v = s2_delta S n hn (k : ZMod S.m) := by
      funext j
      have hc := congrArg (fun p : ComplexPoint (g3_power Y n) => p ≫ g3_proj Y n j) hvt
      simp only [Point.map, Category.assoc, s2_action, s2_check_lift_proj] at hc
      change (t ≫ g3_proj Y n (τ.symm j)) ≫ _ =
        (t ≫ g3_proj Y n ((1 : Equiv.Perm (Fin n)).symm j)) ≫ _ at hc
      dsimp only [t] at hc
      rw [s2_check_lift_proj, s2_check_lift_proj] at hc
      have hu := hz hc
      simpa only [e.apply_symm_apply, toAdd_ofAdd] using congrArg (fun u => (e u).toAdd) hu
    rw [he] at hv
    simpa [s2_delta] using hv
  apply (orderOf_eq_iff hm).mpr
  constructor
  · apply End.ext
    apply (cancel_epi q).mp
    have hp := s2v_l1b_residual_generator_powers S Y W a e ha1 hamul n hn q d hgen S.m
    have hd : s2_delta S n hn (S.m : ZMod S.m) = 0 := by
      funext j
      simp only [ZMod.natCast_self, s2_delta, ite_self, Pi.zero_apply]
    rw [hd, (s2_coordinateAction_laws S Y a e ha1 hamul n).1,
      Category.id_comp] at hp
    exact hp.trans (Category.comp_id q).symm
  · intro k hkm hkpos hk
    have hdvd := (ZMod.natCast_eq_zero_iff k S.m).mp (hperiod k hk)
    exact (Nat.not_dvd_of_pos_of_lt hkpos hkm) hdvd

end HodgeLean.Foundations.Program
