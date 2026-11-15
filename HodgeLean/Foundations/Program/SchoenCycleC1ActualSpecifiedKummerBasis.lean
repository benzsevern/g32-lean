import HodgeLean.Foundations.Program.SchoenCycleC1SpecifiedEigenvectorPowerBasis
import HodgeLean.Foundations.Program.SchoenCycleC1GenericStalkKummerHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1RationalPullbackScalars
import HodgeLean.Foundations.Program.SchoenCycleC1GenericLocalFieldSquare

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Polynomial
namespace HodgeLean.Foundations.Program

/-- An actual nonzero deck eigenfunction with its specified coefficient is
itself a Kummer power-basis generator over the original generic stalk map.
The degree and faithful period refer to the actual projection and deck map. -/
theorem s2e_c1_actual_specified_kummer_basis
    (W B : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsIntegral B.left]
    (β : W ⟶ B) [IsSeparated β.left]
    (hg : β.left (genericPoint W.left) = genericPoint B.left)
    (δ : W ⟶ W) [IsIso δ] (hδ : δ ≫ β = β)
    (m : ℕ) (hm : 0 < m)
    (hpow : End.of δ.left ^ m = 1)
    (hfaith : ∀ n, n < m → End.of δ.left ^ n = 1 → n = 0)
    (η : ℂ) (hη : IsPrimitiveRoot η m)
    (z : W.left.functionField) (hz : z ≠ 0) (c : B.left.functionField)
    (heig : s2e_step1_fieldPullback W.left δ.left z =
      HodgeLean.Foundations.Curves.stalkC (genericPoint W.left) η * z) :
    let φ := (eqToHom (congrArg B.left.presheaf.stalk hg.symm) ≫
      β.left.stalkMap (genericPoint W.left)).hom
    letI := φ.toAlgebra
    Module.finrank B.left.functionField W.left.functionField = m →
    z ^ m = φ c →
    ∃ P : PowerBasis B.left.functionField W.left.functionField,
      P.gen = z ∧ minpoly B.left.functionField P.gen = X ^ m - C c := by
  let φ := (eqToHom (congrArg B.left.presheaf.stalk hg.symm) ≫
    β.left.stalkMap (genericPoint W.left)).hom
  letI := φ.toAlgebra
  dsimp only
  intro hdim hpower
  letI : Module.Finite B.left.functionField W.left.functionField :=
    Module.finite_of_finrank_pos (hdim.symm ▸ hm)
  obtain ⟨u, hu⟩ := s2e_c1_periodic_deckAut β.left δ.left
    (congrArg Over.Hom.left hδ) m hm.ne' hpow
  have hp : End.of u.asIso.hom.left ^ m = 1 := by rw [hu]; exact hpow
  have hfaithU : ∀ n, n < m → End.of u.asIso.hom.left ^ n = 1 → n = 0 := by
    simpa only [hu] using hfaith
  have hord : orderOf (s2e_c1_genericStalkDeckHom β.left hg u) = m :=
    s2e_c1_deck_field_order β.left φ (s2e_c1_genericStalkMap_square β.left hg) u m hm hp hfaithU
  have hordi : orderOf (s2e_c1_genericStalkDeckHom β.left hg u⁻¹) = m := by
    rw [map_inv, orderOf_inv, hord]
  let ζ := HodgeLean.Foundations.Curves.stalkC (genericPoint B.left) η
  have hζ : IsPrimitiveRoot ζ m :=
    hη.map_of_injective (HodgeLean.Foundations.Curves.stalkC (genericPoint B.left)).injective
  have hscalar : φ ζ = HodgeLean.Foundations.Curves.stalkC (genericPoint W.left) η :=
    s2e_c1_rational_pullback_complex_scalars W B β φ
      (s2e_c1_generic_stalk_map_local_square β.left hg) η
  have he : s2e_c1_genericStalkDeckHom β.left hg u⁻¹ z = ζ • z := by
    change s2e_step1_fieldPullback W.left u.asIso.hom.left z = φ ζ * z
    simpa only [hu, hscalar] using heig
  exact s2e_c1_kummer_powerBasis_of_specified_eigenvector
    (s2e_c1_genericStalkDeckHom β.left hg u⁻¹) m hm hdim hordi ζ hζ z hz he c hpower

end HodgeLean.Foundations.Program
