import HodgeLean.Foundations.Program.SchoenCycleC1RestrictedSectionRankHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1AffineSectionPointHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1FibreCardTransportHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1EtaleAffineChartHelpers

/-! # Actual generic field degrees measured by complex fibres -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A fibre on an actual affine etale base chart counts the field degree
over the specified generic stalk embedding of the original projection. -/
theorem s2e_c1_actual_fieldDegree_eq_etale_chart_fibre_card
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (f : X ⟶ Y) [IsFinite f.left]
    (hg : f.left (genericPoint X.left) = genericPoint Y.left)
    (U : Y.left.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [Nonempty (f.left ⁻¹ᵁ U)] [Etale (f.left ∣_ U)]
    (y : ComplexPoint (openScheme Y U)) :
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
      f.left.stalkMap (genericPoint X.left)).hom
    letI := φ.toAlgebra
    Module.finrank Y.left.functionField X.left.functionField =
      Nat.card ((Point.map f) ⁻¹' {Point.map (openInclusion Y U) y}) := by
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
    f.left.stalkMap (genericPoint X.left)).hom
  letI := φ.toAlgebra
  letI : Algebra Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) := (f.left.app U).hom.toAlgebra
  let XU := openScheme X (f.left ⁻¹ᵁ U)
  let YU := openScheme Y U
  let fU := s2e_c11_restricted_over_morphism X Y f U
  haveI : IsAffine XU.left := hU.preimage f.left
  haveI : IsAffine YU.left := hU
  haveI : Nonempty YU.left := inferInstanceAs (Nonempty U.toScheme)
  haveI : IsIntegral YU.left := isIntegral_of_isOpenImmersion U.ι
  haveI : IsFinite fU.left := inferInstanceAs (IsFinite (f.left ∣_ U))
  haveI : Etale fU.left := inferInstanceAs (Etale (f.left ∣_ U))
  letI : Algebra Γ(YU.left, ⊤) Γ(XU.left, ⊤) := fU.left.appTop.hom.toAlgebra
  calc
    Module.finrank Y.left.functionField X.left.functionField =
        Module.finrank Γ(Y.left, U) Γ(X.left, f.left ⁻¹ᵁ U) :=
      s2e_c1_genericStalk_fieldDegree_eq_section_finrank f.left hg U hU
    _ = Module.finrank Γ(YU.left, ⊤) Γ(XU.left, ⊤) :=
      (s2e_c1_restricted_section_finrank f.left U).symm
    _ = Nat.card ((Point.map fU) ⁻¹' {y}) :=
      s2e_c1_finite_etale_affine_section_rank_eq_fibre_card XU YU fU y
    _ = Nat.card ((Point.map f) ⁻¹' {Point.map (openInclusion Y U) y}) :=
      s2e_c1_restricted_complex_fibre_card X Y f U y

/-- Measured fibres on every nonempty base open determine the exact
field degree of the retained finite complex projection. -/
theorem s2e_c1_actual_fieldDegree_of_measured_fibres
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    [IsLocallyNoetherian Y.left] (f : X ⟶ Y) [IsFinite f.left] [Surjective f.left]
    (hg : f.left (genericPoint X.left) = genericPoint Y.left) (m : ℕ)
    (hmeas : ∀ U : Y.left.Opens, (U : Set Y.left).Nonempty →
      ∃ y : ComplexPoint Y, y.underlying ∈ U ∧ Nat.card ((Point.map f) ⁻¹' {y}) = m) :
    let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
      f.left.stalkMap (genericPoint X.left)).hom
    letI := φ.toAlgebra
    Module.finrank Y.left.functionField X.left.functionField = m := by
  obtain ⟨U, hU, _, hEt⟩ := s2e_c1_complex_finite_exists_etale_base_open X Y f
  obtain ⟨y, hy, hcard⟩ := hmeas U hU
  obtain ⟨A, hA, hyA, hAU⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y.left) (x := y.underlying) (U := U) hy
  haveI : Nonempty A := ⟨⟨y.underlying, hyA⟩⟩
  haveI : Etale (f.left ∣_ U) := hEt
  haveI : Etale (f.left ∣_ A) := s2e_c1_etale_restriction_of_le f.left U A hAU
  obtain ⟨x, hx⟩ := f.left.surjective y.underlying
  haveI : Nonempty (f.left ⁻¹ᵁ A) :=
    ⟨⟨x, by change f.left x ∈ A; rwa [hx]⟩⟩
  let yA := (openHomeomorph Y A).symm ⟨y, hyA⟩
  have hyAmap : Point.map (openInclusion Y A) yA = y :=
    congrArg Subtype.val ((openHomeomorph Y A).apply_symm_apply ⟨y, hyA⟩)
  have hd := s2e_c1_actual_fieldDegree_eq_etale_chart_fibre_card X Y f hg A hA yA
  rw [hyAmap] at hd
  exact hd.trans hcard


end HodgeLean.Foundations.Program
