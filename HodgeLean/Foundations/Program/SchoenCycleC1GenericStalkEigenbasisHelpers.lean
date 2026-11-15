import HodgeLean.Foundations.Program.SchoenCycleC1GenericStalkKummerHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1SpecifiedGeneratorKummerHelpers

/-! # Eigenbases of the specified deck action over the retained generic embedding -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Polynomial
namespace HodgeLean.Foundations.Program

/-- The actual generic stalk deck representation retains a prescribed
primitive eigenvalue in its exact Kummer power basis. -/
theorem s2e_c1_genericStalk_kummer_eigenbasis
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsSeparated f]
    (hg : f (genericPoint X) = genericPoint Y) (u : Aut (Over.mk f))
    (m : ℕ) (hm : 0 < m) (hpow : End.of u.asIso.hom.left ^ m = 1)
    (hfaith : ∀ n, n < m → End.of u.asIso.hom.left ^ n = 1 → n = 0)
    (ζ : Y.functionField) (hζ : IsPrimitiveRoot ζ m) :
    let φ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
      f.stalkMap (genericPoint X)).hom
    letI := φ.toAlgebra
    ∀ [Module.Finite Y.functionField X.functionField],
      Module.finrank Y.functionField X.functionField = m →
      ∃ (B : PowerBasis Y.functionField X.functionField) (c : Y.functionField),
        minpoly Y.functionField B.gen = Polynomial.X ^ m - C c ∧
        B.gen ^ m = algebraMap Y.functionField X.functionField c ∧
        s2e_c1_genericStalkDeckHom f hg u B.gen = ζ • B.gen := by
  dsimp only
  let φ := (eqToHom (congrArg Y.presheaf.stalk hg.symm) ≫
    f.stalkMap (genericPoint X)).hom
  letI := φ.toAlgebra
  intro hfin hdim
  have horder : orderOf (s2e_c1_genericStalkDeckHom f hg u) = m :=
    s2e_c1_deck_field_order f φ (s2e_c1_genericStalkMap_square f hg) u m hm hpow hfaith
  exact s2e_c1_kummer_powerBasis_of_specified_generator
    (s2e_c1_genericStalkDeckHom f hg u) m hm hdim horder ζ hζ

end HodgeLean.Foundations.Program
