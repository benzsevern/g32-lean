import HodgeLean.Foundations.Program.SchoenCycleC1PeriodicComplexAut
import HodgeLean.Foundations.Program.SchoenCycleC1MeasuredFreeOpenEtale

/-! # Measured etaleness from the actual periodic deck generator -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The specified periodic deck morphism gives etaleness over an open on
which none of its positive iterates below the measured degree fixes a point. -/
theorem s2e_c1_cyclic_measured_etale_over_free_open
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    [IsIntegral Y.left] [Smooth Y.hom]
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (d : X ⟶ X) (hd : d ≫ q = q)
    (m : ℕ) (hm : 0 < m) (hpow : End.of d ^ m = 1)
    (hfaith : ∀ n, n < m → End.of d ^ n = 1 → n = 0)
    (hmeas : ∀ V : Y.left.Opens, (V : Set Y.left).Nonempty →
      ∃ y : ComplexPoint Y, y.underlying ∈ V ∧ Nat.card ((Point.map q) ⁻¹' {y}) = m)
    (W : Y.left.Opens)
    (hfree : ∀ x : ComplexPoint X, q.left x.underlying ∈ W →
      ∀ n, n < m → (Point.map d)^[n] x = x → n = 0) : Etale (q.left ∣_ W) := by
  classical
  obtain ⟨u, hu, ho⟩ := s2e_c1_periodic_complex_aut X d m hm hpow hfaith
  let G := Subgroup.zpowers u
  have hc : Nat.card G = m := by rw [Nat.card_zpowers, ho]
  letI : Finite G := Nat.finite_of_card_ne_zero (hc ▸ Nat.ne_of_gt hm)
  letI : Fintype G := Fintype.ofFinite G
  let a : G → (X ⟶ X) := fun g => g.val.asIso.hom
  have hf : Function.Injective a := by
    intro g h he
    apply Subtype.ext
    apply Aut.ext
    exact Iso.ext he
  have hfin : IsOfFinOrder u := by
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, ho ▸ pow_orderOf_eq_one u⟩
  have hrep : ∀ g : G, ∃ n, n < m ∧ u ^ n = g.val := by
    intro g
    have hg := hfin.mem_zpowers_iff_mem_range_orderOf.mp g.property
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hg
    exact ⟨n, ho ▸ Finset.mem_range.mp hn, he⟩
  have hp : ∀ n, (u ^ n).asIso.hom = (End.of d ^ n).asHom := by
    intro n
    let F : Aut X →* End X := {
      toFun := fun v => End.of v.asIso.hom
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have he := congrArg End.asHom (map_pow F u n)
    change (u ^ n).asIso.hom = (End.of u.asIso.hom ^ n).asHom at he
    simpa only [hu] using he
  apply s2e_c1_measured_cover_etale_over_free_open X Y G a rfl (fun _ _ => rfl) hf q
  · intro g
    obtain ⟨n, _, hn⟩ := hrep g
    change g.val.asIso.hom ≫ q = q
    rw [← hn, hp]
    exact s2e_c1_generator_power_over q d hd n
  · intro V hV
    obtain ⟨y, hy, he⟩ := hmeas V hV
    exact ⟨y, hy, he.trans hc.symm⟩
  · intro x hx g hg
    obtain ⟨n, hn, he⟩ := hrep g
    have hfix : (Point.map d)^[n] x = x := by
      rw [s2e_c1_point_map_power, ← hp, he]
      exact hg
    have hn0 := hfree x hx n hn hfix
    apply Subtype.ext
    change g.val = 1
    simpa only [hn0, pow_zero] using he.symm

end HodgeLean.Foundations.Program
