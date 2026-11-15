import HodgeConjecture.Mathlib.Topology.Category.TopPair
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance
import Mathlib.Topology.Homotopy.Contractible

/-! # Actual pair projection with a contractible factor
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal first projection preserves a pair pulled back from its first factor.
Source: Hatcher, Algebraic Topology, section 2.1, maps of pairs.
HC no distance; AV milestone no distance. -/
def properCycle_factor_projection_pair
    (E Y : TopCat.{0}) (A : Set E) :
    TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.fst ⁻¹' A) ⟶
      TopPair.ofSubset (X := E) A :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) (fun _ h => h)

/-- The original relative homology map of the literal first projection is bijective when its second factor is contractible.
Source: Hatcher, Algebraic Topology, section 2.1, relative homotopy invariance.
HC no distance; AV milestone no distance. -/
lemma properCycle_contractible_factor_projection_bijective
    (E Y : TopCat.{0}) [ContractibleSpace Y] (A : Set E) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n (properCycle_factor_projection_pair E Y A)) := by
  obtain ⟨y, ⟨H⟩⟩ := id_nullhomotopic Y
  let P := TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.fst ⁻¹' A)
  let Q := TopPair.ofSubset (X := E) A
  let f := properCycle_factor_projection_pair E Y A
  let s : Q ⟶ P := TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun x => (x, y), continuous_id.prodMk continuous_const⟩) (fun _ h => h)
  have hs : s ≫ f = 𝟙 Q := by ext z : 2 <;> rfl
  let J : TopPair.Homotopy (𝟙 P) (f ≫ s) :=
    { fst :=
        { toFun := fun tz => (tz.2.1, H (tz.1, tz.2.2))
          continuous_toFun := by
            change Continuous (fun tz : unitInterval × (E × Y) => (tz.2.1, H (tz.1, tz.2.2)))
            fun_prop
          map_zero_left := fun z => Prod.ext rfl (H.map_zero_left z.2)
          map_one_left := fun z => Prod.ext rfl (H.map_one_left z.2) }
      snd :=
        { toFun := fun tz => ⟨(tz.2.val.1, H (tz.1, tz.2.val.2)), tz.2.property⟩
          continuous_toFun := by
            apply Continuous.subtype_mk
            change Continuous (fun tz : unitInterval × (Prod.fst ⁻¹' A : Set (E × Y)) =>
              (tz.2.val.1, H (tz.1, tz.2.val.2)))
            fun_prop
          map_zero_left := fun z => Subtype.ext (Prod.ext rfl (H.map_zero_left z.val.2))
          map_one_left := fun z => Subtype.ext (Prod.ext rfl (H.map_one_left z.val.2)) }
      w := rfl }
  have hleft (v : RelativeHomology ℚ P n) :
      relativeHomologyMap ℚ n s (relativeHomologyMap ℚ n f v) = v := by
    have hh := J.relativeHomologyMap_apply_eq (R := ℚ) n v
    simpa only [relativeHomologyMap_id, LinearMap.id_apply,
      relativeHomologyMap_comp, LinearMap.comp_apply] using hh.symm
  have hright (v : RelativeHomology ℚ Q n) :
      relativeHomologyMap ℚ n f (relativeHomologyMap ℚ n s v) = v := by
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, hs,
      relativeHomologyMap_id, LinearMap.id_apply]
  exact ⟨fun u v h => (hleft u).symm.trans ((congrArg (relativeHomologyMap ℚ n s) h).trans
    (hleft v)), fun v => ⟨relativeHomologyMap ℚ n s v, hright v⟩⟩

end HodgeLean.Foundations.QuotientDuality
