import HodgeLean.Foundations.Program.SchoenTransferC1a5RealizationSigmaHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5SigmaSimplexExcisionHelpers
import HodgeLean.Foundations.Program.SchoenTransferC1a5IsoExcisionHelpers

/-! Relative excision for literal realizations of categorical simplex coproducts.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- Realized categorical coproducts of positive-dimensional simplex pairs have singular relative excision.
Source: Hatcher §2.1, Theorem 2.20; Mathlib realization and topological coproduct isomorphisms. -/
lemma c1a5_realized_coproduct_simplex_excision (I : Type) (n : ℕ) {B D : TopCat.{0}}
    (t : SSet.toTop.obj (∐ fun _ : I ↦ (SSet.boundary.{0} (n + 1) : SSet)) ⟶ B)
    (r : B ⟶ D) (b : SSet.toTop.obj (∐ fun _ : I ↦ (Δ[n + 1] : SSet.{0})) ⟶ D)
    (sq : IsPushout t (SSet.toTop.map
      (CategoryTheory.Limits.Sigma.map (fun _ : I ↦ (SSet.boundary.{0} (n + 1)).ι))) r b) :
    QuasiIso (c1a5RelativeMap c1a5Chains
      (TopCat.toSSet.map (SSet.toTop.map
        (CategoryTheory.Limits.Sigma.map (fun _ : I ↦ (SSet.boundary.{0} (n + 1)).ι))))
      (TopCat.toSSet.map r) (TopCat.toSSet.map t) (TopCat.toSSet.map b) (by
        rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]
        exact congrArg TopCat.toSSet.map sq.w.symm)) := by
  let KA := fun _ : I ↦ (SSet.boundary.{0} (n + 1) : SSet)
  let KC := fun _ : I ↦ (Δ[n + 1] : SSet.{0})
  let l := SSet.toTop.map (CategoryTheory.Limits.Sigma.map
    (fun _ : I ↦ (SSet.boundary.{0} (n + 1)).ι))
  let l' := c1a5_sigma_map (fun _ : I ↦ SSet.toTop.map (SSet.boundary.{0} (n + 1)).ι)
  let eA := c1a5_realization_sigma_iso KA
  let eC := c1a5_realization_sigma_iso KC
  have hn : l ≫ eC.hom = eA.hom ≫ l' := c1a5_realization_sigma_iso_naturality _
  have hf : l' ≫ eC.inv = eA.inv ≫ l := by
    apply (cancel_epi eA.hom).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun z ↦ z ≫ eC.inv) hn.symm
  let t' := eA.inv ≫ t
  let b' := eC.inv ≫ b
  have sq' : IsPushout t' l' r b' := by
    apply sq.of_iso eA (Iso.refl B) eC (Iso.refl D)
    · simp only [Iso.refl_hom, t', ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
    · exact hn
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, b', ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
  apply c1a5_relative_comparison_source_iso c1a5Chains
    (TopCat.toSSet.map l) (TopCat.toSSet.map r) (TopCat.toSSet.map t) (TopCat.toSSet.map b)
    (by rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]; exact congrArg TopCat.toSSet.map sq.w.symm)
    (TopCat.toSSet.mapIso eA.symm) (TopCat.toSSet.mapIso eC.symm)
    (TopCat.toSSet.map l') (by change TopCat.toSSet.map l' ≫ TopCat.toSSet.map eC.inv = TopCat.toSSet.map eA.inv ≫ TopCat.toSSet.map l; rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]; exact congrArg TopCat.toSSet.map hf)
  have hh := c1a5_sigma_realized_simplex_excision I n t' r b' sq'
  simpa only [t', b', l', TopCat.toSSet.map_comp, Functor.mapIso_hom, Iso.symm_hom] using hh

end HodgeLean.Foundations.Program
