import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorStalkAction
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorStalkNorm
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorJetOrder
import HodgeLean.Foundations.Program.SchoenCycleQuotientStabilizerJets

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A stabilizer norm has a downstairs germ with the same finite order in the original stalk. -/
theorem s2v_l1b_divisor_norm_descent
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (x : ComplexPoint X) (hclosed : IsClosed ({x.underlying} : Set X.left))
    (H : Subgroup G) (hH : ∀ g, Point.map (a g) x = x ↔ g ∈ H)
    [IsDiscreteValuationRing (X.left.presheaf.stalk x.underlying)]
    (ι : X.left.presheaf.stalk x.underlying →+* PowerSeries ℂ)
    (p : X.left.presheaf.stalk x.underlying) (hp : Irreducible p)
    (hpX : ι p = PowerSeries.X) :
    ∃ c : Y.left.presheaf.stalk (q.left x.underlying),
      (ι ((q.left.stalkMap x.underlying).hom c)).order = Nat.card H := by
  letI := Fintype.ofFinite H
  let ah (g : H) := a g.val
  have hfix (g : H) : (ah g).left x.underlying = x.underlying :=
    s2e_complex_point_fixed_underlying X (a g.val) x ((hH g.val).mpr g.property)
  let ρ := s2v_l1b_divisor_stalkAction X H ah ha1
    (fun g h => hamul g.val h.val) x.underlying hfix
  obtain ⟨v, hv, hvo⟩ := s2v_l1b_divisor_stalk_norm H ρ ι ⟨p, hpX⟩ p hp
  have hinvariant (g : G) (hg : g ∈ H) :
      s2e_fixed_point_stalkPullback X.left (a g).left x.underlying
        (s2e_complex_point_fixed_underlying X (a g) x ((hH g).mpr hg)) v = v := by
    have h := hv ((⟨g, hg⟩ : H)⁻¹)
    change s2e_fixed_point_stalkPullback X.left
      (a (g⁻¹)⁻¹).left x.underlying
        (hfix (((⟨g, hg⟩ : H)⁻¹)⁻¹)) v = v at h
    simpa only [inv_inv] using h
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := q.left x.underlying) (U := ⊤) trivial
  have hx : ⊤ ≤ x.left ⁻¹ᵁ (q.left ⁻¹ᵁ U) :=
    by
      intro z _
      have hz : z = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := Spec ↧ℂ) _ _
      subst z
      exact hxU
  obtain ⟨c, hc⟩ := s2e_quotient_invariant_stalk_jet_descent X Y G a ha1 hamul q
    hinv hquot U hU H x hx hclosed hH (Fintype.card H + 1) v
    (fun g hg => by rw [hinvariant g hg, sub_self]; exact Ideal.zero_mem _)
  refine ⟨(Y.left.presheaf.germ U (q.left x.underlying) hxU).hom c, ?_⟩
  rw [Scheme.Hom.germ_stalkMap_apply]
  rw [← Nat.card_eq_fintype_card] at hvo
  apply s2v_l1b_divisor_equal_jet_order ι p hp hpX _ v (Nat.card H) hvo
  simpa only [Nat.card_eq_fintype_card] using hc

end HodgeLean.Foundations.Program
