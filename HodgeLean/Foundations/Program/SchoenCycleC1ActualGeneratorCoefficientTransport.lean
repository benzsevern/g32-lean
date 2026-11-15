import HodgeLean.Foundations.Program.SchoenCycleC1SignedGeneratorUnits
import HodgeLean.Foundations.Program.SchoenCycleC1RationalSectionPullbackLE
import HodgeLean.Foundations.Program.SchoenCycleC1AffineComapSections
import HodgeLean.Foundations.Program.SchoenCycleC1DominantAffineRestriction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- An original signed branch coefficient equation transports to any actual
principal generators of the pulled-back branch ideals. The new section unit
and nonvanishing of every new generator are constructed internally. -/
theorem s2e_c1_actual_generator_coefficient_transport
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [QuasiCompact f]
    (φ : Y.functionField →+* X.functionField)
    (hφ : ∀ (p : X) (r : Y.presheaf.stalk (f p)),
      φ (algebraMap (Y.presheaf.stalk (f p)) Y.functionField r) =
        algebraMap (X.presheaf.stalk p) X.functionField ((f.stalkMap p).hom r))
    {J : Type} [Fintype J] (D : J → Y.IdealSheafData)
    (U : Y.affineOpens) (V : X.affineOpens) [Nonempty U.1] [Nonempty V.1]
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (g : J → Γ(Y, U.1)) (h : J → Γ(X, V.1))
    (hg : ∀ j, g j ≠ 0)
    (hDU : ∀ j, (D j).ideal U = Ideal.span {g j})
    (hDV : ∀ j, ((D j).comap f).ideal V = Ideal.span {h j})
    (n : J → ℤ) (u : Γ(Y, U.1)ˣ) (c : Y.functionField)
    (hc : c = Y.germToFunctionField U.1 (u : Γ(Y, U.1)) *
      ∏ j, (Y.germToFunctionField U.1 (g j)) ^ n j) :
    ∃ v : Γ(X, V.1)ˣ, (∀ j, h j ≠ 0) ∧
      φ c = X.germToFunctionField V.1 (v : Γ(X, V.1)) *
        ∏ j, (X.germToFunctionField V.1 (h j)) ^ n j := by
  let M := (f.appLE U.1 V.1 hVU).hom
  let G := (X.germToFunctionField V.1).hom
  have hM : Function.Injective M := s2e_c1_dominant_appLE_injective f U.1 V.1 hVU
  have hI (j : J) : Ideal.span {M (g j)} = Ideal.span {h j} := by
    have hi := s2e_c1_affine_comap_appLE f (D j) U V hVU
    rw [hDU j, hDV j, Ideal.map_span, Set.image_singleton] at hi
    exact hi.symm
  have hne (j : J) : h j ≠ 0 := by
    intro hz
    have hmem : M (g j) ∈ Ideal.span {h j} := (hI j) ▸ Ideal.subset_span rfl
    rw [hz, Ideal.span_singleton_zero] at hmem
    have hzero : M (g j) = 0 := hmem
    exact hg j (hM (hzero.trans (map_zero M).symm))
  obtain ⟨v, hv⟩ := s2e_c1_signed_generator_unit G (fun j => M (g j)) h n hI
  let uV := Units.map M.toMonoidHom u
  refine ⟨uV * v, hne, ?_⟩
  have hpull (s : Γ(Y, U.1)) : φ (Y.germToFunctionField U.1 s) = G (M s) :=
    s2e_c1_rational_section_pullbackLE f φ hφ U.1 V.1 hVU s
  rw [hc]
  simp only [map_mul, map_prod, map_zpow₀, hpull]
  rw [hv]
  change G (M (u : Γ(Y, U.1))) * (G (v : Γ(X, V.1)) * ∏ j, (G (h j)) ^ n j) =
    G (M (u : Γ(Y, U.1)) * (v : Γ(X, V.1))) * ∏ j, (G (h j)) ^ n j
  rw [map_mul, mul_assoc]

end HodgeLean.Foundations.Program
