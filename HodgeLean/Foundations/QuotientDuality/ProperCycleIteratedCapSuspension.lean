import HodgeLean.Foundations.QuotientDuality.ProperCycleEmptyTriadCapDuality

/-! # Actual iterated real tangential support products -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual spaces obtained by successively adjoining a real tangential coordinate.
Source: Hatcher, Algebraic Topology, section 3.3, local product models.
HC no distance; AV milestone no distance. -/
def properCycle_real_support_space (Y : TopCat.{0}) : ℕ → TopCat.{0}
  | 0 => Y
  | n + 1 => TopCat.of (ℝ × properCycle_real_support_space Y n)

/-- The normal support in each actual real product is the inverse image of the preceding normal support.
Source: Hatcher, Algebraic Topology, section 3.3, local product models.
HC no distance; AV milestone no distance. -/
def properCycle_real_normal_support (Y : TopCat.{0}) (S : Set Y) :
    (n : ℕ) → Set (properCycle_real_support_space Y n)
  | 0 => S
  | n + 1 => Prod.snd ⁻¹' properCycle_real_normal_support Y S n

/-- The tangential point support is extended by the zero point in each actual real coordinate.
Source: Hatcher, Algebraic Topology, section 3.3, local product models.
HC no distance; AV milestone no distance. -/
def properCycle_real_point_support (Y : TopCat.{0}) (T : Set Y) :
    (n : ℕ) → Set (properCycle_real_support_space Y n)
  | 0 => T
  | n + 1 => {z | z.1 = 0 ∧ z.2 ∈ properCycle_real_point_support Y T n}

/-- Each actual iterated normal support is a topologically closed subspace when the original support is closed.
Source: Munkres, Topology, section 18, inverse images of closed sets.
HC no distance; AV milestone no distance. -/
lemma properCycle_real_normal_support_isClosed
    (Y : TopCat.{0}) (S : Set Y) (hS : IsClosed S) (n : ℕ) :
    IsClosed (properCycle_real_normal_support Y S n) := by
  induction n with
  | zero => exact hS
  | succ n ih => exact ih.preimage continuous_snd

/-- Each actual iterated tangential support is topologically closed when the original support is closed.
Source: Munkres, Topology, sections 18 and 19, inverse images and product subspaces.
HC no distance; AV milestone no distance. -/
lemma properCycle_real_point_support_isClosed
    (Y : TopCat.{0}) (T : Set Y) (hT : IsClosed T) (n : ℕ) :
    IsClosed (properCycle_real_point_support Y T n) := by
  induction n with
  | zero => exact hT
  | succ n ih =>
    exact (isClosed_eq continuous_fst continuous_const).inter (ih.preimage continuous_snd)

/-- The original relative cohomology class is pulled back through each literal real product projection.
Source: Hatcher, Algebraic Topology, section 3.1, functorial relative cohomology.
HC no distance; AV milestone no distance. -/
def properCycle_real_support_coclass
    (Y : TopCat.{0}) (S : Set Y) (p : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) p) :
    (n : ℕ) → RelativeCohomology ℚ
      (TopPair.ofSubset (X := properCycle_real_support_space Y n)
        (properCycle_real_normal_support Y S n)ᶜ) p
  | 0 => a
  | n + 1 => relativeCohomologyMap ℚ p
      (TopPair.ofSubsetHom
        (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ :
          properCycle_real_support_space Y (n + 1) ⟶ properCycle_real_support_space Y n)
        (show Set.MapsTo (fun z : ℝ × properCycle_real_support_space Y n => z.2)
          (properCycle_real_normal_support Y S (n + 1))ᶜ
          (properCycle_real_normal_support Y S n)ᶜ from fun _ h => h))
      (properCycle_real_support_coclass Y S p a n)

/-- The original relative cap remains bijective after any number of actual real tangential support suspensions, with the original class pulled back through the literal projections.
Source: Hatcher, Algebraic Topology, sections 2.2 and 3.3, iterated relative cap suspension.
HC no distance; AV milestone no distance. -/
lemma properCycle_iterated_product_support_cap_bijective
    (Y : TopCat.{0}) (S T : Set Y) (hS : IsClosed S) (hT : IsClosed T)
    (p q : ℕ) (hp : Even p)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) Sᶜ) p)
    (hc : Function.Bijective (triadCapCohomologyLinear ℚ Y Sᶜ Tᶜ p q a)) (n : ℕ) :
    Function.Bijective (triadCapCohomologyLinear ℚ (properCycle_real_support_space Y n)
      (properCycle_real_normal_support Y S n)ᶜ (properCycle_real_point_support Y T n)ᶜ
      p (q + n) (properCycle_real_support_coclass Y S p a n)) := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    exact properCycle_product_support_cap_suspension_bijective
      (properCycle_real_support_space Y n) (properCycle_real_normal_support Y S n)
      (properCycle_real_point_support Y T n)
      (properCycle_real_normal_support_isClosed Y S hS n)
      (properCycle_real_point_support_isClosed Y T hT n)
      p (q + n) hp (properCycle_real_support_coclass Y S p a n) ih

/-- The specified standard complex normal coclass gives bijectivity of the original cap in every actual iterated real tangential product model.
Source: Hatcher, Algebraic Topology, section 3.3, normal orientations and local cap duality.
HC no distance; AV milestone no distance. -/
lemma properCycle_standard_normal_iterated_triad_cap_bijective (d n : ℕ) :
    let Y := TopCat.of (Fin d → ℂ)
    let S : Set Y := {0}
    let a := normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
      (standardComplexLocalClass_ne_zero_for_chart d)
    Function.Bijective (triadCapCohomologyLinear ℚ (properCycle_real_support_space Y n)
      (properCycle_real_normal_support Y S n)ᶜ
      (properCycle_real_point_support Y Set.univ n)ᶜ (2 * d) n
      (properCycle_real_support_coclass Y S (2 * d) a n)) := by
  dsimp only
  have h :=
    (properCycle_iterated_product_support_cap_bijective (TopCat.of (Fin d → ℂ))
      {0} Set.univ isClosed_singleton isClosed_univ (2 * d) 0 (by exact ⟨d, by omega⟩)
      (normalizedRelativeCoclass (standardComplexLocalClass ℚ d)
        (standardComplexLocalClass_ne_zero_for_chart d))
      (by rw [Set.compl_univ]; exact properCycle_standard_normal_triad_cap_bijective d) n)
  rw [Nat.zero_add] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
