import HodgeLean.Foundations.Program.SchoenCycleC1OrbitFieldDegree
import HodgeLean.Foundations.Program.SchoenCycleC1GenericStalkEigenbasisHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A faithful cyclic orbit projection constructs a nonzero rational
eigenfunction for the specified original generator and primitive eigenvalue,
with its exact descended Kummer coefficient. -/
theorem s2e_c1_orbit_kummer_eigenfunction
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral Y.left] [IsLocallyNoetherian Y.left]
    (G : Type) [Group G] [Finite G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a) (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (horbit : ∀ x z : ComplexPoint X, Point.map q x = Point.map q z ↔
      ∃ u, Point.map (a u) x = z)
    (g : G) (hg : orderOf g = Nat.card G)
    (ζ : Y.left.functionField) (hζ : IsPrimitiveRoot ζ (Nat.card G)) :
    let hgen := s2_dominant_genericPoint q.left
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hgen.symm) ≫
      q.left.stalkMap (genericPoint X.left)).hom
    letI := s2e_step1_action_isIso X G a ha1 hamul g
    ∃ (z : X.left.functionField) (f : Y.left.functionField),
      z ≠ 0 ∧ f ≠ 0 ∧ z ^ Nat.card G = φ f ∧
      s2e_step1_fieldPullback X.left (a g).left z = φ ζ * z := by
  let hgen := s2_dominant_genericPoint q.left
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hgen.symm) ≫
    q.left.stalkMap (genericPoint X.left)).hom
  letI := φ.toAlgebra
  letI := s2e_step1_action_isIso X G a ha1 hamul g
  have hdim : Module.finrank Y.left.functionField X.left.functionField = Nat.card G :=
    s2e_c1_orbit_projection_actual_field_degree X Y G a ha1 hamul hinj q hinv horbit
  have hm : 0 < Nat.card G := Nat.card_pos
  letI : Module.Finite Y.left.functionField X.left.functionField :=
    Module.finite_of_finrank_pos (hdim.symm ▸ hm)
  let F : G →* End X.left := {
    toFun := fun u => End.of (a u).left
    map_one' := by apply End.ext; change (a 1).left = 𝟙 X.left; rw [ha1]; rfl
    map_mul' := fun u v => by
      apply End.ext
      change (a (u * v)).left = (a v).left ≫ (a u).left
      rw [hamul]; rfl }
  have hF : Function.Injective F := by
    intro u v huv
    apply hinj
    apply Over.OverMorphism.ext
    exact congrArg End.asHom huv
  have hpow : End.of (a g).left ^ Nat.card G = 1 := by
    change F g ^ Nat.card G = 1
    rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
  have hfaith (n : ℕ) (hn : n < Nat.card G)
      (he : End.of (a g).left ^ n = 1) : n = 0 := by
    have hgn : g ^ n = 1 := hF (by rw [map_pow, map_one]; exact he)
    have hd := orderOf_dvd_of_pow_eq_one hgn
    rw [hg] at hd
    exact Nat.eq_zero_of_dvd_of_lt hd hn
  obtain ⟨u, hu⟩ := s2e_c1_periodic_deckAut q.left (a g).left
    (congrArg Over.Hom.left (hinv g)) (Nat.card G) hm.ne' hpow
  have hp : End.of u.asIso.hom.left ^ Nat.card G = 1 := by rw [hu]; exact hpow
  have hfaithU : ∀ n, n < Nat.card G → End.of u.asIso.hom.left ^ n = 1 → n = 0 := by
    simpa only [hu] using hfaith
  have hord : orderOf (s2e_c1_genericStalkDeckHom q.left hgen u) = Nat.card G :=
    s2e_c1_deck_field_order q.left φ (s2e_c1_genericStalkMap_square q.left hgen)
      u (Nat.card G) hm hp hfaithU
  have hordi : orderOf (s2e_c1_genericStalkDeckHom q.left hgen u⁻¹) = Nat.card G := by
    rw [map_inv, orderOf_inv, hord]
  obtain ⟨z, hz, heig, ⟨f, hf⟩, _⟩ := s2e_c1_kummer_eigenvector_of_full_order
    (s2e_c1_genericStalkDeckHom q.left hgen u⁻¹) (Nat.card G) hm hdim hordi ζ hζ
  refine ⟨z, f, hz, ?_, hf.symm, ?_⟩
  · intro he
    have hzero : z ^ Nat.card G = 0 := by rw [← hf, he, map_zero]
    exact pow_ne_zero _ hz hzero
  · change s2e_step1_fieldPullback X.left u.asIso.hom.left z = φ ζ * z at heig
    simpa only [hu] using heig

end HodgeLean.Foundations.Program
