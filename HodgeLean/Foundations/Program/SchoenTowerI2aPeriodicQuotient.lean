import HodgeLean.Foundations.Program.SchoenProperActionQuotient
import HodgeLean.Foundations.Program.SchoenTowerI2aDiagonalTranslations
import Mathlib.Data.ZMod.QuotientGroup

/-! # The actual quotient by a periodic residual generator
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A periodic endomorphism of an integral projective complex scheme has its actual finite categorical quotient, with iterate fibres.
Source: Schoen (1988), section 1; the checked finite-action proper quotient construction. -/
theorem s2v_i2a_periodic_deck_quotient
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (d : X ⟶ X) [IsIso d] (m : ℕ) (hm : 0 < m) (hd : (End.of d) ^ m = 1) :
    ∃ (Q : Over (Spec ↧ℂ)) (q : X ⟶ Q),
      IsIntegral Q.left ∧ IsProper Q.hom ∧ IsFinite q.left ∧
      Function.Surjective (Point.map q) ∧ d ≫ q = q ∧
      (∀ x y : ComplexPoint X, Point.map q x = Point.map q y ↔
        ∃ k : ℕ, (Point.map d)^[k] x = y) ∧
      (∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T), d ≫ f = f →
        ∃! u : Q ⟶ T, q ≫ u = f) := by
  let g : Aut X := Aut.of (asIso d)
  have hinj : Function.Injective (Aut.toEnd : Aut X →* End X) := by
    intro u v huv
    apply Aut.ext
    apply Iso.ext
    exact congrArg End.asHom huv
  have hgperiod : g ^ m = 1 := by
    apply hinj
    rw [map_pow, map_one]
    exact hd
  have hgfinite : IsOfFinOrder g := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hgperiod⟩
  let G := Subgroup.zpowers g
  haveI : Finite G := finite_zpowers.mpr hgfinite
  let ρ : G →* Aut X := G.subtype
  have hpower (k : ℕ) : (g ^ k).asIso.hom = ((End.of d) ^ k).asHom := by
    have H := congrArg End.asHom (map_pow (Aut.toEnd : Aut X →* End X) g k)
    exact H
  have hnat (u : G) : ∃ k : ℕ, g ^ k = u.val :=
    hgfinite.mem_powers_iff_mem_zpowers.mpr u.property
  have hpows {T : Over (Spec ↧ℂ)} (f : X ⟶ T) (hf : d ≫ f = f) (k : ℕ) :
      ((End.of d) ^ k).asHom ≫ f = f := by
    induction k with
    | zero => simp only [pow_zero, End.one_asHom, Category.id_comp]
    | succ k ih =>
      rw [pow_succ, End.mul_asHom, Category.assoc, ih, hf]
  obtain ⟨Q, q, hQ, hproper, hqfin, hqsurj, hqinv, hqorb, hqdesc, hQnormal⟩ :=
    s2_finiteAction_properQuotient X G ρ
  refine ⟨Q, q, hQ, hproper, hqfin, hqsurj, ?_, ?_, ?_⟩
  · exact hqinv ⟨g, Subgroup.mem_zpowers g⟩
  · intro x y
    constructor
    · intro hxy
      obtain ⟨u, hu⟩ := (hqorb x y).mp hxy
      obtain ⟨k, hk⟩ := hnat u
      refine ⟨k, ?_⟩
      change Point.map u.val.asIso.hom x = y at hu
      rw [← hk, hpower, s2v_i2a_pointMap_end_power] at hu
      exact hu
    · rintro ⟨k, hk⟩
      apply (hqorb x y).mpr
      refine ⟨⟨g ^ k, Subgroup.pow_mem G (Subgroup.mem_zpowers g) k⟩, ?_⟩
      change Point.map (g ^ k).asIso.hom x = y
      rw [hpower, s2v_i2a_pointMap_end_power]
      exact hk
  · intro T f hf
    apply hqdesc T f
    intro u
    obtain ⟨k, hk⟩ := hnat u
    change u.val.asIso.hom ≫ f = f
    rw [← hk, hpower]
    exact hpows f hf k

end HodgeLean.Foundations.Program
