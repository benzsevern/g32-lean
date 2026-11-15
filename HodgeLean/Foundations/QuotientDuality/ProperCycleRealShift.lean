import HodgeLean.Foundations.QuotientDuality.ProperCycleHalfRay
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativeMV

/-! # The local homology shift for an actual real product factor -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology.Singular Topology
namespace HodgeLean.Foundations.QuotientDuality

set_option backward.isDefEq.respectTransparency false in
/-- Reflection identifies lower half-ray relative homology with the vanishing upper half-ray model.
Source: Hatcher, Algebraic Topology, section 2.1, relative homotopy invariance.
HC no distance; AV milestone no distance. -/
lemma properCycle_lower_half_ray_homology_subsingleton
    (Y : TopCat.{0}) (S : Set Y) (a : ℝ) (n : ℕ) :
    Subsingleton (RelativeHomology ℚ
      (TopPair.ofSubset (X := TopCat.of (ℝ × Y)) {z | z.1 ≤ a ∧ z.2 ∈ S}ᶜ) n) := by
  let e : (ℝ × Y) ≃ₜ (ℝ × Y) :=
    (Homeomorph.neg ℝ).prodCongr (Homeomorph.refl Y)
  let P : TopPair.ofSubset (X := TopCat.of (ℝ × Y)) {z | z.1 ≤ a ∧ z.2 ∈ S}ᶜ ≅
      TopPair.ofSubset (X := TopCat.of (ℝ × Y)) {z | -a ≤ z.1 ∧ z.2 ∈ S}ᶜ :=
    TopPair.isoOfSubset e (by
      intro z
      change (¬ (-a ≤ -z.1 ∧ z.2 ∈ S)) ↔ ¬ (z.1 ≤ a ∧ z.2 ∈ S)
      rw [neg_le_neg_iff])
  let E := (HomologicalComplex.homologyFunctor (ModuleCat ℚ)
    (ComplexShape.down ℕ) n).mapIso ((relativeChainFunctor ℚ).mapIso P)
  exact @Function.Injective.subsingleton _ _ E.toLinearEquiv E.toLinearEquiv.injective
    (properCycle_upper_half_ray_homology_subsingleton Y S (-a) n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual local relative homology of a real product shifts the normal local degree by one.
Source: Hatcher, Algebraic Topology, section 2.2, relative Mayer–Vietoris;
Bredon, Sheaf Theory, second edition, V.9, normal product models.
HC no distance; AV milestone no distance. -/
def properCycle_real_product_local_homology_iso
    (Y : TopCat.{0}) [T1Space Y] (y : Y) (n : ℕ) :
    orientationGroup (TopCat.of (ℝ × Y)) (n + 1) (0, y) ≅
      orientationGroup Y n y := by
  let X := TopCat.of (ℝ × Y)
  let K : Set X := {z | 0 ≤ z.1 ∧ z.2 = y}
  let L : Set X := {z | z.1 ≤ 0 ∧ z.2 = y}
  have hK : IsClosed K :=
    (isClosed_le continuous_const continuous_fst).inter
      (isClosed_singleton.preimage continuous_snd)
  have hL : IsClosed L :=
    (isClosed_le continuous_fst continuous_const).inter
      (isClosed_singleton.preimage continuous_snd)
  let a : pointComplementPair (M := X) (0, y) ≅ TopPair.ofSubset (Kᶜ ∪ Lᶜ) :=
    TopPair.isoOfSubset (Homeomorph.refl X) (by
      intro z
      change (¬ (0 ≤ z.1 ∧ z.2 = y) ∨ ¬ (z.1 ≤ 0 ∧ z.2 = y)) ↔ z ≠ (0, y)
      constructor
      · intro hz he
        subst z
        rcases hz with h | h <;> exact h ⟨le_rfl, rfl⟩
      · intro hz
        by_cases hk : 0 ≤ z.1 ∧ z.2 = y
        · right
          intro hl
          exact hz (Prod.ext (le_antisymm hl.1 hk.1) hk.2)
        · exact Or.inl hk)
  let b : TopPair.ofSubset (Kᶜ ∩ Lᶜ) ≅
      TopPair.ofSubset (X := X) (Prod.snd ⁻¹' ({y} : Set Y)ᶜ) :=
    TopPair.isoOfSubset (Homeomorph.refl X) (by
      intro z
      change z.2 ≠ y ↔ (¬ (0 ≤ z.1 ∧ z.2 = y) ∧ ¬ (z.1 ≤ 0 ∧ z.2 = y))
      constructor
      · intro hz
        exact ⟨fun h => hz h.2, fun h => hz h.2⟩
      · intro hz hy
        by_cases ht : 0 ≤ z.1
        · exact hz.1 ⟨ht, hy⟩
        · exact hz.2 ⟨le_of_not_ge ht, hy⟩)
  have hzero (j : ℕ) :
      IsZero (RelativeHomology ℚ (TopPair.ofSubset Kᶜ) j) ∧
      IsZero (RelativeHomology ℚ (TopPair.ofSubset Lᶜ) j) := by
    constructor
    · apply ModuleCat.isZero_iff_subsingleton.mpr
      exact properCycle_upper_half_ray_homology_subsingleton Y {y} 0 j
    · apply ModuleCat.isZero_iff_subsingleton.mpr
      exact properCycle_lower_half_ray_homology_subsingleton Y {y} 0 j
  let H (j : ℕ) := HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) j
  exact (H (n + 1)).mapIso ((relativeChainFunctor ℚ).mapIso a) ≪≫
    ProperCycleRelativeMV.relativeMayerVietorisBoundaryIso X Kᶜ Lᶜ
      hK.isOpen_compl hL.isOpen_compl n (fun j _ => hzero j) ≪≫
    (H n).mapIso ((relativeChainFunctor ℚ).mapIso b) ≪≫
    properCycle_product_support_homology_iso ℝ Y {y} n

end HodgeLean.Foundations.QuotientDuality
