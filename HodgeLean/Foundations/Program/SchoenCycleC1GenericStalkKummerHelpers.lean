import HodgeLean.Foundations.Program.SchoenCycleC1PeriodicDeckAutHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1GenericStalkActionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1DeckFieldOrderHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1FullOrderFieldHelpers

/-! # Kummer presentations over the actual generic stalk embedding -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Polynomial
namespace HodgeLean.Foundations.Program

/-- The projection's actual generic stalk extension has a Kummer power
basis when its field degree equals the faithful scheme deck period. -/
theorem s2e_c1_genericStalk_kummer_powerBasis
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsSeparated f]
    (hg : f (genericPoint X) = genericPoint Y)
    (u : Aut (Over.mk f)) (m : ℕ) (hm : 0 < m)
    (hpow : End.of u.asIso.hom.left ^ m = 1)
    (hfaith : ∀ n, n < m → End.of u.asIso.hom.left ^ n = 1 → n = 0) :
    let φ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
      f.stalkMap (genericPoint X)).hom
    letI := φ.toAlgebra
    ∀ [Module.Finite Y.functionField X.functionField],
      Module.finrank Y.functionField X.functionField = m →
      (primitiveRoots m Y.functionField).Nonempty →
      ∃ (B : PowerBasis Y.functionField X.functionField) (c : Y.functionField),
        minpoly Y.functionField B.gen = Polynomial.X ^ m - C c ∧
        B.gen ^ m = algebraMap Y.functionField X.functionField c := by
  dsimp only
  let φ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
    f.stalkMap (genericPoint X)).hom
  letI := φ.toAlgebra
  intro hfin hdim hroots
  let σ := s2e_c1_genericStalkDeckHom f hg u
  have horder : orderOf σ = Module.finrank Y.functionField X.functionField := by
    rw [hdim]
    exact s2e_c1_deck_field_order f φ (s2e_c1_genericStalkMap_square f hg)
      u m hm hpow hfaith
  obtain ⟨hG, hC⟩ := s2e_c1_galois_cyclic_of_full_order σ horder
  letI := hG
  letI := hC
  obtain ⟨B, c, hmin, hroot⟩ := s2e_c1_cyclic_kummer_powerBasis
    Y.functionField X.functionField (by simpa only [hdim] using hroots)
  exact ⟨B, c, by simpa only [hdim] using hmin, by simpa only [hdim] using hroot⟩

/-- A periodic deck endomorphism with faithful powers supplies the Kummer
presentation over the actual generic stalk embedding, without a separately
specified over-base automorphism. -/
theorem s2e_c1_genericStalk_kummer_of_periodic_deck
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsSeparated f]
    (hg : f (genericPoint X) = genericPoint Y)
    (d : X ⟶ X) (hd : d ≫ f = f) (m : ℕ) (hm : 0 < m)
    (hpow : End.of d ^ m = 1)
    (hfaith : ∀ n, n < m → End.of d ^ n = 1 → n = 0) :
    let φ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
      f.stalkMap (genericPoint X)).hom
    letI := φ.toAlgebra
    ∀ [Module.Finite Y.functionField X.functionField],
      Module.finrank Y.functionField X.functionField = m →
      (primitiveRoots m Y.functionField).Nonempty →
      ∃ (B : PowerBasis Y.functionField X.functionField) (c : Y.functionField),
        minpoly Y.functionField B.gen = Polynomial.X ^ m - C c ∧
        B.gen ^ m = algebraMap Y.functionField X.functionField c := by
  obtain ⟨u, hu⟩ := s2e_c1_periodic_deckAut f d hd m (Nat.ne_of_gt hm) hpow
  have hpowU : End.of u.asIso.hom.left ^ m = 1 := by rw [hu]; exact hpow
  have hfaithU : ∀ n, n < m → End.of u.asIso.hom.left ^ n = 1 → n = 0 := by
    simpa only [hu] using hfaith
  dsimp only
  let φ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
    f.stalkMap (genericPoint X)).hom
  letI := φ.toAlgebra
  intro hfin hdim hroots
  exact s2e_c1_genericStalk_kummer_powerBasis f hg u m hm hpowU hfaithU hdim hroots

end HodgeLean.Foundations.Program
