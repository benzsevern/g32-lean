import HodgeLean.Foundations.Program.SchoenTowerL1bKvalSpread
import HodgeLean.Foundations.Program.SchoenTowerI2aGenericCharts
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! Spreading a stalk branch equation while retaining the supplied parameters.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A weighted stalk equation spreads on an affine refinement using the restrictions of every supplied branch parameter and polynomial coordinate. -/
theorem s2v_i2a_stalk_branch_refinement
    {K : Type} [Field K] (X : Scheme.{0}) [IsIntegral X] [IsAffine X]
    (x : X) (η : Spec (.of K) ⟶ X) [IsDominant η]
    (κ : X.functionField ⟶ CommRingCat.of K)
    (hη : Spec.map κ ≫ X.fromSpecStalk (genericPoint X) = η)
    {T : Type} [Fintype T] (D : T → X.IdealSheafData)
    (z : T → Γ(X, ⊤)) (n : T → ℕ)
    (hz : ∀ t, (D t).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {z t})
    {ι : Type} (c : MvPolynomial ι ℂ →+* Γ(X, ⊤)) (hc : c.Etale)
    (v : K) (m : ℕ) (ε : (X.presheaf.stalk x)ˣ)
    (hgen : Subfield.closure (Set.range (s2v_l1b_kval_stalkMap X x κ) ∪ {v}) = ⊤)
    (hv : v ^ m = s2v_l1b_kval_stalkMap X x κ ε *
      ∏ t, s2v_l1b_kval_stalkMap X x κ (X.presheaf.germ ⊤ x (by trivial) (z t)) ^ n t) :
    ∃ (O : X.affineOpens) (hηO : ⊤ ≤ η ⁻¹ᵁ O.1) (εO : Γ(X, O)ˣ),
      x ∈ O.1 ∧
      let res := (X.presheaf.map (homOfLE (show O.1 ≤ ⊤ from le_top)).op).hom
      let ρ := (η.appLE O.1 ⊤ hηO ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
      (res.comp c).Etale ∧
      (∀ t, (D t).ideal O = Ideal.span {res (z t)}) ∧
      v ^ m = ρ (εO : Γ(X, O)) * ∏ t, ρ (res (z t)) ^ n t ∧
      Subfield.closure (Set.range ρ ∪ {v}) = ⊤ := by
  obtain ⟨U₀, hxU₀, hspread⟩ := s2v_l1b_stalk_weighted_equation_spread
    X x η κ hη ⟨⊤, isAffineOpen_top X⟩ (by trivial) D z hz n v m ε hgen hv
  obtain ⟨O', hO', hxO, hOU⟩ := exists_isAffineOpen_mem_and_subset hxU₀
  let O : X.affineOpens := ⟨O', hO'⟩
  letI : Nonempty O.1 := ⟨⟨x, hxO⟩⟩
  have hηO : ⊤ ≤ η ⁻¹ᵁ O.1 := (s2v_i2a_dominant_field_preimage η O.1).ge
  let res := (X.presheaf.map (homOfLE (show O.1 ≤ ⊤ from le_top)).op).hom
  have hD (t : T) : (D t).ideal O = Ideal.span {res (z t)} := by
    rw [← (D t).map_ideal (show O ≤ ⟨⊤, isAffineOpen_top X⟩ from (show O.1 ≤ ⊤ from le_top)), hz t,
      Ideal.map_span, Set.image_singleton]
    rfl
  obtain ⟨εO, hgenO, hvO⟩ := hspread O hOU hxO hηO (fun t => res (z t)) hD
  refine ⟨O, hηO, εO, hxO, ?_, hD, hvO, hgenO⟩
  have hres : res.Etale := by
    have H := HasRingHomProperty.appLE (P := @Etale) (𝟙 X) inferInstance
      ⟨⊤, isAffineOpen_top X⟩ O (show O.1 ≤ (𝟙 X) ⁻¹ᵁ ⊤ from le_top)
    simpa only [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] using H
  exact RingHom.Etale.stableUnderComposition c res hc hres

end HodgeLean.Foundations.Program
