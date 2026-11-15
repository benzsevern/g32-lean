import HodgeLean.Foundations.QuotientDuality.ProperCycleRealSupportCoordinates

/-! # The original normal coclass in actual finite support coordinates -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal base-coordinate projection is an actual map of the normal support-complement pairs.
Source: Hatcher, Algebraic Topology, section 3.1, functorial relative cohomology.
HC no distance; AV milestone no distance. -/
def properCycle_real_support_base_pair (Y : TopCat.{0}) (S : Set Y) (n : ℕ) :
    TopPair.ofSubset (X := properCycle_real_support_space Y n) (properCycle_real_normal_support Y S n)ᶜ ⟶
      TopPair.ofSubset (X := Y) Sᶜ :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun z => (properCycle_real_support_coordinates Y n z).2,
      continuous_snd.comp (properCycle_real_support_coordinates Y n).continuous⟩)
    (fun z hz hs => hz ((Set.ext_iff.mp (properCycle_real_support_coordinates_normal Y S n) z).mp hs))

/-- Successive actual product projections compose to the literal finite-coordinate base projection on both subspaces of the pair.
Source: Hatcher, Algebraic Topology, section 3.1, functorial relative cohomology.
HC no distance; AV milestone no distance. -/
lemma properCycle_real_support_base_pair_succ (Y : TopCat.{0}) (S : Set Y) (n : ℕ) :
    TopPair.ofSubsetHom
        (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ : properCycle_real_support_space Y (n + 1) ⟶
          properCycle_real_support_space Y n)
        (show Set.MapsTo (fun z : ℝ × properCycle_real_support_space Y n => z.2)
          (properCycle_real_normal_support Y S (n + 1))ᶜ
          (properCycle_real_normal_support Y S n)ᶜ from fun _ h => h) ≫
      properCycle_real_support_base_pair Y S n = properCycle_real_support_base_pair Y S (n + 1) := by
  ext x : 2 <;> rfl

/-- The iterated original coclass is exactly pullback by the literal finite-coordinate base pair projection.
Source: Hatcher, Algebraic Topology, section 3.1, composition of relative cohomology pullbacks.
HC no distance; AV milestone no distance. -/
lemma properCycle_real_support_coclass_base_projection
    (Y : TopCat.{0}) (S : Set Y) (p : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) p) (n : ℕ) :
    properCycle_real_support_coclass Y S p a n =
      relativeCohomologyMap ℚ p (properCycle_real_support_base_pair Y S n) a := by
  induction n with
  | zero =>
    have h : properCycle_real_support_base_pair Y S 0 = 𝟙 _ := by ext x : 2 <;> rfl
    rw [h, relativeCohomologyMap_id]
    rfl
  | succ n ih =>
    change relativeCohomologyMap ℚ p
      (TopPair.ofSubsetHom
        (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ : properCycle_real_support_space Y (n + 1) ⟶
          properCycle_real_support_space Y n)
        (show Set.MapsTo (fun z : ℝ × properCycle_real_support_space Y n => z.2)
          (properCycle_real_normal_support Y S (n + 1))ᶜ
          (properCycle_real_normal_support Y S n)ᶜ from fun _ h => h))
      (properCycle_real_support_coclass Y S p a n) = _
    rw [ih, ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
      properCycle_real_support_base_pair_succ]
    rfl

/-- The actual finite coordinate homeomorphism identifies the original normal support-complement pairs.
Source: Hatcher, Algebraic Topology, section 3.1, relative cohomology of homeomorphic pairs.
HC no distance; AV milestone no distance. -/
def properCycle_real_support_normal_pair_iso (Y : TopCat.{0}) (S : Set Y) (n : ℕ) :
    TopPair.ofSubset (X := properCycle_real_support_space Y n) (properCycle_real_normal_support Y S n)ᶜ ≅
      TopPair.ofSubset (X := TopCat.of ((Fin n → ℝ) × Y)) (Prod.snd ⁻¹' Sᶜ) :=
  TopPair.isoOfSubset (properCycle_real_support_coordinates Y n)
    (fun z => not_congr (Set.ext_iff.mp (properCycle_real_support_coordinates_normal Y S n) z))

/-- The actual normal-pair coordinate isomorphism retains the literal product support projection to the original normal space.
Source: Hatcher, Algebraic Topology, section 3.1, maps of support-complement pairs.
HC no distance; AV milestone no distance. -/
lemma properCycle_real_support_normal_pair_projection (Y : TopCat.{0}) (S : Set Y) (n : ℕ) :
    (properCycle_real_support_normal_pair_iso Y S n).hom ≫
        properCycle_product_support_projection (Fin n → ℝ) Y S =
      properCycle_real_support_base_pair Y S n := by
  ext x : 2 <;> rfl

/-- In actual finite coordinates the original iterated coclass is precisely the original class pulled back along the literal product support projection.
Source: Hatcher, Algebraic Topology, section 3.1, functorial relative cohomology.
HC no distance; AV milestone no distance. -/
lemma properCycle_real_support_coclass_coordinates
    (Y : TopCat.{0}) (S : Set Y) (p : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) p) (n : ℕ) :
    relativeCohomologyMap ℚ p (properCycle_real_support_normal_pair_iso Y S n).inv
        (properCycle_real_support_coclass Y S p a n) =
      relativeCohomologyMap ℚ p (properCycle_product_support_projection (Fin n → ℝ) Y S) a := by
  rw [properCycle_real_support_coclass_base_projection,
    ← LinearMap.comp_apply, ← relativeCohomologyMap_comp,
    ← properCycle_real_support_normal_pair_projection, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

end HodgeLean.Foundations.QuotientDuality
