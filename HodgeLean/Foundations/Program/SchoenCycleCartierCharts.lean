import HodgeLean.Foundations.Program.SchoenCycleCartierLocalization
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Compatible affine Cartier charts
Basic-open refinement preserves the ideal-module freeness test.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The Cartier freeness test persists on every basic open of its affine chart. -/
theorem s2e_cartier_free_on_basicOpen
    {X : Scheme} (I : X.IdealSheafData) (U : X.affineOpens)
    (hfree : Nonempty ((I.ideal U) ≃ₗ[Γ(X, U)] Γ(X, U))) (f : Γ(X, U)) :
    Nonempty ((I.ideal (X.affineBasicOpen f)) ≃ₗ[Γ(X, X.affineBasicOpen f)]
      Γ(X, X.affineBasicOpen f)) := by
  letI := U.2.isLocalization_basicOpen f
  rw [← I.map_ideal_basicOpen U f]
  exact s2e_free_ideal_localization (S := Γ(X, X.basicOpen f)) (Submonoid.powers f)
    (I.ideal U) hfree

/-- A free affine Cartier chart can be refined inside any prescribed open
neighborhood while retaining its ideal-module equivalence. -/
theorem s2e_cartier_affine_refinement
    {X : Scheme} (I : X.IdealSheafData) (U : X.affineOpens)
    (hfree : Nonempty ((I.ideal U) ≃ₗ[Γ(X, U)] Γ(X, U)))
    (x : X) (hxU : x ∈ U.1) (W : X.Opens) (hxW : x ∈ W) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V ≤ U ∧ V.1 ≤ W ∧
      Nonempty ((I.ideal V) ≃ₗ[Γ(X, V)] Γ(X, V)) := by
  obtain ⟨f, hfW, hxf⟩ := U.2.exists_basicOpen_le ⟨x, hxW⟩ hxU
  exact ⟨X.affineBasicOpen f, hxf, X.affineBasicOpen_le f, hfW,
    s2e_cartier_free_on_basicOpen I U hfree f⟩

/-- The freeness test on an affine open gives the same test on the
corresponding open subscheme and its restricted ideal sheaf. -/
theorem s2e_cartier_free_on_open_subscheme
    {X : Scheme} (I : X.IdealSheafData) (U : X.Opens) [IsAffine U.toScheme]
    (hfree : Nonempty ((I.ideal ⟨U, show IsAffineOpen U from ‹IsAffine U.toScheme›⟩) ≃ₗ[Γ(X, U)] Γ(X, U))) :
    Nonempty (((I.comap U.ι).ideal ⟨⊤, isAffineOpen_top U.toScheme⟩) ≃ₗ[Γ(U.toScheme, ⊤)]
      Γ(U.toScheme, ⊤)) := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.Opens.ι_appIso]
  simp only [Iso.refl_inv]
  let V : X.affineOpens := ⟨U.ι ''ᵁ ⊤,
    (isAffineOpen_top U.toScheme).image_of_isOpenImmersion U.ι⟩
  change Nonempty ((I.ideal V) ≃ₗ[Γ(X, V)] Γ(X, V))
  have hV : V = ⟨U, show IsAffineOpen U from ‹IsAffine U.toScheme›⟩ :=
    Subtype.ext U.ι_image_top
  rw [hV]
  exact hfree

/-- Local Cartier tests on a scheme and its source supply compatible affine
charts for their morphism at every source point. -/
theorem s2e_compatible_cartier_charts
    {Q X : Scheme} (u : Q ⟶ X) (K : X.IdealSheafData)
    (hambient : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty ((K.ideal U) ≃ₗ[Γ(X, U)] Γ(X, U)))
    (hslice : ∀ q : Q, ∃ V : Q.affineOpens, q ∈ V.1 ∧
      Nonempty (((K.comap u).ideal V) ≃ₗ[Γ(Q, V)] Γ(Q, V)))
    (q : Q) :
    ∃ (U : X.affineOpens) (V : Q.affineOpens),
      u q ∈ U.1 ∧ q ∈ V.1 ∧ V.1 ≤ u ⁻¹ᵁ U.1 ∧
      Nonempty ((K.ideal U) ≃ₗ[Γ(X, U)] Γ(X, U)) ∧
      Nonempty (((K.comap u).ideal V) ≃ₗ[Γ(Q, V)] Γ(Q, V)) := by
  obtain ⟨U, hqU, hfreeU⟩ := hambient (u q)
  obtain ⟨V₀, hqV₀, hfreeV₀⟩ := hslice q
  obtain ⟨V, hqV, _, hVU, hfreeV⟩ := s2e_cartier_affine_refinement
    (K.comap u) V₀ hfreeV₀ q hqV₀ (u ⁻¹ᵁ U.1) hqU
  exact ⟨U, V, hqU, hqV, hVU, hfreeU, hfreeV⟩

end HodgeLean.Foundations.Program
