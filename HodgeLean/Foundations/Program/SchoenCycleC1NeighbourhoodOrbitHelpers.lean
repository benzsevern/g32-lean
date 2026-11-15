import HodgeLean.Foundations.Program.SchoenCycleC1DeckRestrictionHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1EtaleOrbitHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1FibreCardTransportHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1FaithfulTransportHelpers

/-! # Actual deck fibres over an etale neighbourhood -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- A faithful finite-order generator and a measured fibre determine every
actual fibre orbit over a finite etale base neighbourhood. -/
theorem s2e_c1_fibre_orbits_on_etale_neighbourhood
    (m : ℕ) (hm : 0 < m) (W B : Over (Spec ↧ℂ))
    [IsIntegral W.left] [IsIntegral B.left] [Smooth B.hom] [IsSeparated B.hom]
    (β : W ⟶ B) [IsFinite β.left] [Surjective β.left]
    (d : W ⟶ W) (hd : d ≫ β = β) (horder : End.of d ^ m = 1)
    (hfaith : ∀ n, n < m → End.of d ^ n = 1 → n = 0)
    (U : B.left.Opens) [Etale (β.left ∣_ U)]
    (y₀ : ComplexPoint B) (hy₀ : y₀.underlying ∈ U)
    (hcard : Nat.card ((Point.map β) ⁻¹' {y₀}) = m) :
    ∀ y : ComplexPoint B, y.underlying ∈ U →
      ∃ z : ComplexPoint W, Point.map β z = y ∧
        Function.Injective (fun t : Fin m => Point.map (End.of d ^ t.val).asHom z) ∧
        (∀ t : Fin m, Point.map β (Point.map (End.of d ^ t.val).asHom z) = y) ∧
        (∀ v : ComplexPoint W, Point.map β v = y →
          ∃ t : Fin m, Point.map (End.of d ^ t.val).asHom z = v) := by
  let V := β.left ⁻¹ᵁ U
  let XU := openScheme W V
  let YU := openScheme B U
  let jX := openInclusion W V
  let jY := openInclusion B U
  let fU := s2e_c11_restricted_over_morphism W B β U
  have hU : (U : Set B.left).Nonempty := ⟨y₀.underlying, hy₀⟩
  obtain ⟨w₀, hw₀⟩ := β.left.surjective y₀.underlying
  have hV : (V : Set W.left).Nonempty := ⟨w₀, by change β.left w₀ ∈ U; rwa [hw₀]⟩
  haveI : Nonempty U := hU.to_subtype
  haveI : Nonempty V := hV.to_subtype
  haveI : Nonempty XU.left := inferInstanceAs (Nonempty V.toScheme)
  haveI : Nonempty YU.left := inferInstanceAs (Nonempty U.toScheme)
  haveI : IsOpenImmersion jX.left := inferInstanceAs (IsOpenImmersion V.ι)
  haveI : IsOpenImmersion jY.left := inferInstanceAs (IsOpenImmersion U.ι)
  haveI : IsIntegral XU.left := isIntegral_of_isOpenImmersion jX.left
  haveI : IsIntegral YU.left := isIntegral_of_isOpenImmersion jY.left
  haveI : Smooth YU.hom := by change Smooth (U.ι ≫ B.hom); infer_instance
  haveI : IsSeparated YU.hom := by change IsSeparated (U.ι ≫ B.hom); infer_instance
  haveI : IsSeparated W.hom := by rw [← Over.w β]; infer_instance
  haveI : IsFinite fU.left := inferInstanceAs (IsFinite (β.left ∣_ U))
  haveI : Etale fU.left := inferInstanceAs (Etale (β.left ∣_ U))
  haveI : Surjective fU.left := by
    constructor
    change Function.Surjective (β.left ∣_ U)
    intro y
    obtain ⟨w, hw⟩ := β.left.surjective y.1
    have hwU : w ∈ V := by change β.left w ∈ U; rw [hw]; exact y.property
    refine ⟨⟨w, hwU⟩, ?_⟩
    apply Subtype.ext
    exact (morphismRestrict_base_coe β.left U _).trans hw
  haveI : IsDominant jX.left := AlgebraicGeometry.Opens.isDominant_ι (V.isOpen.dense hV)
  haveI : Mono jX := Over.mono_of_mono_left jX
  haveI : Mono jY := Over.mono_of_mono_left jY
  obtain ⟨dU, hdu, hdf, ho⟩ := s2e_c1_restrict_deck_to_neighbourhood W B β d hd m horder U
  have hfaithU := s2e_c1_faithful_powers_of_dominant_equivariant jX dU d hdu m hfaith
  let y₀U := (openHomeomorph B U).symm ⟨y₀, hy₀⟩
  have hy₀U : Point.map jY y₀U = y₀ :=
    congrArg Subtype.val ((openHomeomorph B U).apply_symm_apply ⟨y₀, hy₀⟩)
  have hcardU : Nat.card ((Point.map fU) ⁻¹' {y₀U}) = m := by
    rw [s2e_c1_restricted_complex_fibre_card W B β U y₀U, hy₀U]
    exact hcard
  have horbits := s2e_c1_etale_fibre_orbit_of_faithful_powers m hm XU YU fU dU hdf ho
    hfaithU y₀U hcardU
  have hsquare : fU ≫ jY = jX ≫ β := s2e_c11_restricted_over_morphism_inclusion W B β U
  have hpower (n : ℕ) (v : ComplexPoint XU) :
      Point.map (End.of d ^ n).asHom (Point.map jX v) =
        Point.map jX (Point.map (End.of dU ^ n).asHom v) := by
    have he := s2e_c1_equivariant_generator_power jX dU d hdu n
    simpa only [Point.map_comp_apply] using
      congrArg (fun f => Point.map f v) he.symm
  intro y hy
  let yU := (openHomeomorph B U).symm ⟨y, hy⟩
  have hyU : Point.map jY yU = y :=
    congrArg Subtype.val ((openHomeomorph B U).apply_symm_apply ⟨y, hy⟩)
  obtain ⟨zU, hzU, hiU, _, heU⟩ := horbits yU
  let z := Point.map jX zU
  have hz : Point.map β z = y := by
    change Point.map β (Point.map jX zU) = y
    rw [← Point.map_comp_apply, ← hsquare, Point.map_comp_apply, hzU, hyU]
  have hi : Function.Injective (fun t : Fin m => Point.map (End.of d ^ t.val).asHom z) := by
    intro t u htu
    apply hiU
    apply map_injective_of_mono jX
    change Point.map jX (Point.map (End.of dU ^ t.val).asHom zU) =
      Point.map jX (Point.map (End.of dU ^ u.val).asHom zU)
    rw [← hpower, ← hpower]
    exact htu
  refine ⟨z, hz, hi, ?_, ?_⟩
  · intro t
    rw [← Point.map_comp_apply, s2e_c1_generator_power_over β d hd]
    exact hz
  · intro v hv
    have hvU : v ∈ Point.overOpen V := by
      apply (Point.mem_overOpen_map_iff β v U).mp
      rw [hv]
      exact hy
    let vU := (openHomeomorph W V).symm ⟨v, hvU⟩
    have hmapv : Point.map jX vU = v :=
      congrArg Subtype.val ((openHomeomorph W V).apply_symm_apply ⟨v, hvU⟩)
    have hfv : Point.map fU vU = yU := by
      apply map_injective_of_mono jY
      rw [← Point.map_comp_apply, hsquare, Point.map_comp_apply, hmapv, hyU]
      exact hv
    obtain ⟨t, ht⟩ := heU vU hfv
    refine ⟨t, ?_⟩
    change Point.map (End.of d ^ t.val).asHom (Point.map jX zU) = v
    rw [hpower]
    exact (congrArg (Point.map jX) ht).trans hmapv

end HodgeLean.Foundations.Program
