import HodgeLean.Foundations.Program.G32Native.TowerPushedClasses

/-! # Orbit classes from the retained smooth neighbourhoods -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- Smooth neighbourhoods give the component representatives used by the source
orbit construction, without a new selection of the component or deck map.
Source: Fulton, Intersection Theory, 19.1–19.2; Bott–Tu, 5–6. -/
theorem tower_orbit_source_neighbourhoods
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left] [Smooth Q.hom]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) (δ : W ⟶ W) (k m : ℕ)
    (himm : ∀ t : Fin m, IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom).left)
    (hdisj : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of δ ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of δ ^ t.val).asHom).left))
    (hsm : ∀ t : Fin m, ∃ U : W.left.Opens,
      Set.range (ι ≫ (End.of δ ^ t.val).asHom).left ⊆ U ∧ Smooth (U.ι ≫ W.hom))
    (hcodim : ∀ t : Fin m, ∀ x ∈
      (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ).support,
      Order.coheight x = k) :
    ∃ cl : (Fin m → ℚ) →ₗ[ℚ]
        AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of (ComplexPoint W)) (2 * k),
      ∀ a : Fin m → ℚ,
        let γ := s2e_rationalOrbitCycle ι δ m a
        (∀ x ∈ γ.support, Order.coheight x = k) ∧
        ∃ cr, a3b4_IsCycleClass W.hom γ k cr ∧
          s2e_classToAbsolute W γ k cr = cl a := by
  classical
  have hex (t : Fin m) : ∃ cr, a3b4_IsCycleClass W.hom
      (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom) ℚ) k cr := by
    let := himm t
    obtain ⟨U, hU, hU_smooth⟩ := hsm t
    exact s2e_chain_component_supported_class Q W
      (ι ≫ (End.of δ ^ t.val).asHom) k U hU hU_smooth (hcodim t)
  choose c hc using hex
  obtain ⟨cl, _, _, hcl⟩ := s2e_chain_orbit_class_linear Q W ι δ k m
    himm hdisj hsm hcodim c hc
  exact ⟨cl, hcl⟩

/-- The same smooth-neighbourhood construction on actual image components gives
normalized pushed representatives with their original residue-degree weights.
Source: Fulton, Intersection Theory, 1.4 and 19.1–19.2; Bott–Tu, 5–6. -/
theorem tower_orbit_pushed_neighbourhoods
    {Q W W₀ : Over (Spec ↧ℂ)} [IsIntegral Q.left] [Smooth Q.hom]
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom] [IsSeparated W₀.hom]
    (ι : Q ⟶ W) (δ : W ⟶ W) (φ : W ⟶ W₀) [QuasiCompact φ.left]
    (k m : ℕ)
    (himm : ∀ t : Fin m,
      IsClosedImmersion (ι ≫ (End.of δ ^ t.val).asHom ≫ φ).left)
    (hdisj : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of δ ^ s.val).asHom ≫ φ).left)
      (Set.range (ι ≫ (End.of δ ^ t.val).asHom ≫ φ).left))
    (hsm : ∀ t : Fin m, ∃ U : W₀.left.Opens,
      Set.range (ι ≫ (End.of δ ^ t.val).asHom ≫ φ).left ⊆ U ∧ Smooth (U.ι ≫ W₀.hom))
    (himage : ∀ t : Fin m, Order.coheight
      (φ.left ((ι ≫ (End.of δ ^ t.val).asHom).left (genericPoint Q.left))) = k) :
    ∀ a : Fin m → ℚ,
      let γ := s2e_rationalOrbitCycle ι δ m a
      (∀ x ∈ (a1p_pushforward φ.left γ).support, Order.coheight x = k) ∧
      ∃ c₀, a3b4_IsCycleClass W₀.hom (a1p_pushforward φ.left γ) k c₀ := by
  classical
  have hex (t : Fin m) : ∃ c₀, a3b4_IsCycleClass W₀.hom
      (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom ≫ φ) ℚ) k c₀ := by
    let := himm t
    obtain ⟨U, hU, hU_smooth⟩ := hsm t
    have hcodim : ∀ x ∈
        (s2e_componentCycle (ι ≫ (End.of δ ^ t.val).asHom ≫ φ) ℚ).support,
        Order.coheight x = k := by
      intro x hx
      rw [s2e_componentCycle_support] at hx
      subst x
      exact himage t
    exact s2e_chain_component_supported_class Q W₀
      (ι ≫ (End.of δ ^ t.val).asHom ≫ φ) k U hU hU_smooth hcodim
  choose c hc using hex
  intro a
  obtain ⟨c₀, hc₀, _⟩ := tower_orbit_pushed_class ι δ φ k m himm hdisj c hc a
  exact ⟨tower_orbit_pushed_coheight ι δ φ k m himage a, c₀, hc₀⟩

end HodgeLean.Foundations.Program.G32Native
