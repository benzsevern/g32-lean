import HodgeLean.Adapters.CycleClassDivisorProduct4
import HodgeLean.Adapters.CycleClassSmoothCharts
import HodgeLean.RealDefs.FundamentalClass.Point

/-! # Coordinate normal classes
Actual pullbacks of the fixed complex orientation dual, with the divisor normal first.
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Adapters

/-- Zero support of a continuous normal-coordinate map.
Source: Bott–Tu, Differential Forms in Algebraic Topology, §6, normal coordinates. -/
def ccm17_zeroSupport (Y : TopCat.{0}) (c : ℕ) (f : C(Y, Fin c → ℂ)) : Closeds Y :=
  ⟨{y | f y = 0}, isClosed_singleton.preimage f.continuous⟩

/-- The normal map on complement pairs.
Source: Bott–Tu, §6, pullback of the normal orientation class. -/
def ccm17_normalPair (Y : TopCat.{0}) (c : ℕ) (f : C(Y, Fin c → ℂ)) :
    TopPair.ofSubset (ccm17_zeroSupport Y c f : Set Y)ᶜ ⟶ puncturedPair ℂ c :=
  TopPair.ofSubsetHom (TopCat.ofHom f) (fun _ h => h)

/-- The fixed normalized class pulled back by normal coordinates.
Source: `normalizedPointCoclass`; Bott–Tu, §6. -/
def ccm17_normalClass (Y : TopCat.{0}) (c : ℕ) (f : C(Y, Fin c → ℂ)) :
    RelativeCohomology ℚ (TopPair.ofSubset (ccm17_zeroSupport Y c f : Set Y)ᶜ) (2 * c) :=
  relativeCohomologyMap ℚ (2 * c) (ccm17_normalPair Y c f) (normalizedPointCoclass c)

/-- First coordinate, as a one-dimensional normal vector.
Source: Griffiths–Harris, Principles of Algebraic Geometry, chapter 0 §4. -/
def ccm17_head (q : ℕ) : C(Fin (q + 1) → ℂ, Fin 1 → ℂ) :=
  ⟨fun z _ => z 0, by fun_prop⟩

/-- Remaining q coordinates, in their original complex order.
Source: Griffiths–Harris, chapter 0 §4. -/
def ccm17_tail (q : ℕ) : C(Fin (q + 1) → ℂ, Fin q → ℂ) :=
  ⟨fun z i => z i.succ, by fun_prop⟩

/-- Identity normal map from the intersection complement to the punctured normal space.
Source: Bott–Tu, §6, direct sum of oriented normal spaces. -/
def ccm17_intersectionPair (q : ℕ) :
    TopPair.ofSubset (X := TopCat.of (Fin (q + 1) → ℂ)) ((ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q) ⊓
      ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q) : Closeds (Fin (q + 1) → ℂ)) : Set (Fin (q + 1) → ℂ))ᶜ ⟶
      puncturedPair ℂ (q + 1) :=
  TopPair.ofSubsetHom (TopCat.ofHom (ContinuousMap.id _)) (by
    intro z hz he
    apply hz
    change (fun _ : Fin 1 => z 0) = 0 ∧ (fun i : Fin q => z i.succ) = 0
    change z = 0 at he
    subst z
    exact ⟨rfl, rfl⟩)

/-- Intersection orientation, independently normalized before any product calculation.
Source: `normalizedPointCoclass`; Bott–Tu, §6, ordered complex normal orientation. -/
def ccm17_intersectionClass (q : ℕ) :
    RelativeCohomology ℚ
      (TopPair.ofSubset (X := TopCat.of (Fin (q + 1) → ℂ)) ((ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) 1 (ccm17_head q) ⊓
        ccm17_zeroSupport (TopCat.of (Fin (q + 1) → ℂ)) q (ccm17_tail q) : Closeds (Fin (q + 1) → ℂ)) : Set (Fin (q + 1) → ℂ))ᶜ)
      (2 + 2 * q) :=
  (show 2 * (q + 1) = 2 + 2 * q by omega) ▸
    relativeCohomologyMap ℚ (2 * (q + 1)) (ccm17_intersectionPair q)
      (normalizedPointCoclass (q + 1))

/-- Complement-pair pullback with the actual inverse-image support.
Source: Hatcher, Algebraic Topology, §3.2, naturality of relative products. -/
def ccm17_preimagePair (Y Z : TopCat.{0}) (f : C(Y, Z)) (S : Closeds Z) :
    TopPair.ofSubset (S.preimage f.continuous : Set Y)ᶜ ⟶
      TopPair.ofSubset (S : Set Z)ᶜ :=
  TopPair.ofSubsetHom (TopCat.ofHom f) (fun _ h => h)

example : (0 : Fin 2 → ℂ) ∈ ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_head 1) := rfl
example : (0 : Fin 2 → ℂ) ∈ ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_tail 1) := rfl
example : (ccm17_normalPair (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_head 1)).right (0 : Fin 2 → ℂ) = (0 : Fin 1 → ℂ) := rfl
example : ccm17_head 1 (fun _ => 1) 0 = 1 := rfl
example : ccm17_tail 1 (fun _ => 1) 0 = 1 := rfl
example : (ccm17_intersectionPair 1).right (0 : Fin 2 → ℂ) = (0 : Fin 2 → ℂ) := rfl
example : (ccm17_preimagePair (TopCat.of ℂ) (TopCat.of ℂ)
    (ContinuousMap.id _) ⊤).right (1 : ℂ) = (1 : ℂ) := rfl
example : RelativeCohomology ℚ
    (TopPair.ofSubset (X := TopCat.of (Fin 2 → ℂ)) (ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_head 1) : Set (Fin 2 → ℂ))ᶜ) 2 :=
  ccm17_normalClass (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_head 1)
example : RelativeCohomology ℚ
    (TopPair.ofSubset (X := TopCat.of (Fin 2 → ℂ)) ((ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_head 1) ⊓
      ccm17_zeroSupport (TopCat.of (Fin 2 → ℂ)) 1 (ccm17_tail 1) : Closeds (Fin 2 → ℂ)) : Set (Fin 2 → ℂ))ᶜ) 4 :=
  ccm17_intersectionClass 1

end HodgeLean.Adapters
