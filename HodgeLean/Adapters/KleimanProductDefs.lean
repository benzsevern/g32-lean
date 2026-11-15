import HodgeLean.Adapters.KleimanTransverse
import HodgeLean.Adapters.CycleClassDivisorMoving
import HodgeLean.Adapters.CycleClassDivisorLocalDefs

/-! # Transverse intersection products -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs

namespace HodgeLean.Adapters

/-- The map of pairs `(U, U \ S) → (ℂ^c, ℂ^c \ {0})` induced by a normal-coordinate map on an
open `U` whose zeros lie in `S`.
Source: Bott--Tu, *Differential Forms in Algebraic Topology*, §6, Thom classes in normal
coordinates. -/
def hc9k_normalCoordinatePair {M : Type} [TopologicalSpace M] (U : Opens M) (S : Set M)
    (c : ℕ) (f : C(U, Fin c → ℂ)) (hf : ∀ u : U, f u = 0 → u.1 ∈ S) :
    neighborhoodSupportComplementPair (U : Set M) S ⟶ puncturedPair ℂ c :=
  TopPair.ofSubsetHom (TopCat.ofHom f) (fun a ha h0 => ha (hf a h0))

/-- The zero map on the whole line, with support the origin, as a normal-coordinate pair.
Source: Bott--Tu, §6. -/
example : neighborhoodSupportComplementPair ((⊤ : Opens ℂ) : Set ℂ) {0} ⟶ puncturedPair ℂ 1 :=
  hc9k_normalCoordinatePair ⊤ {0} 1 ⟨fun u _ => u.1, by fun_prop⟩
    (fun u hu => by simpa using congrFun hu 0)

/-- Two normal-coordinate maps placed side by side, the first `p` coordinates first.
Source: Bott--Tu, §6, direct sums of normal bundles; Griffiths--Harris, *Principles of
Algebraic Geometry*, chapter 0 §4. -/
def hc9k_appendCoordinates {Y : Type*} [TopologicalSpace Y] {p q : ℕ}
    (f : C(Y, Fin p → ℂ)) (h : C(Y, Fin q → ℂ)) : C(Y, Fin (p + q) → ℂ) :=
  ⟨fun y => Fin.append (f y) (h y), by
    refine continuous_pi fun i => Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      exact (continuous_apply j).comp f.continuous
    · simp only [Fin.append_right]
      exact (continuous_apply j).comp h.continuous⟩

/-- The two coordinate axes of the plane, side by side, give the identity coordinates.
Source: `Fin.append`. -/
example : hc9k_appendCoordinates (⟨fun z _ => z 0, by fun_prop⟩ : C(Fin 2 → ℂ, Fin 1 → ℂ))
    (⟨fun z _ => z 1, by fun_prop⟩ : C(Fin 2 → ℂ, Fin 1 → ℂ)) (fun _ => 0) = 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact Fin.append_left _ _ j
  · exact Fin.append_right _ _ j

/-- The first `p` coordinates of `ℂ^(p+q)`, in their original order.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, chapter 0 §4. -/
def hc9k_coordinateHead (p q : ℕ) : C(Fin (p + q) → ℂ, Fin p → ℂ) :=
  ⟨fun z i => z (Fin.castAdd q i), by fun_prop⟩

/-- The last `q` coordinates of `ℂ^(p+q)`, in their original order.
Source: Griffiths--Harris, chapter 0 §4. -/
def hc9k_coordinateTail (p q : ℕ) : C(Fin (p + q) → ℂ, Fin q → ℂ) :=
  ⟨fun z i => z (Fin.natAdd p i), by fun_prop⟩

/-- The common zeros of the head and tail coordinates are exactly the origin.
Source: `Fin.addCases`. -/
theorem hc9k_coordinate_intersection_zero (p q : ℕ) (z : Fin (p + q) → ℂ) :
    z ∈ (ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) p (hc9k_coordinateHead p q) ⊓
      ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) q (hc9k_coordinateTail p q)) ↔
        z = 0 := by
  change ((fun i : Fin p => z (Fin.castAdd q i)) = 0 ∧
    (fun i : Fin q => z (Fin.natAdd p i)) = 0) ↔ z = 0
  constructor
  · rintro ⟨h, t⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact congrFun h j
    · exact congrFun t j
  · rintro rfl
    exact ⟨rfl, rfl⟩

/-- Identity normal map from the complement of the coordinate intersection to the punctured
normal space `ℂ^(p+q) \ {0}`.
Source: Bott--Tu, *Differential Forms in Algebraic Topology*, §6, direct sums of oriented
normal spaces. -/
def hc9k_coordinateIntersectionPair (p q : ℕ) :
    TopPair.ofSubset (X := TopCat.of (Fin (p + q) → ℂ))
      ((ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) p (hc9k_coordinateHead p q) ⊓
        ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) q (hc9k_coordinateTail p q) :
          Closeds (Fin (p + q) → ℂ)) : Set (Fin (p + q) → ℂ))ᶜ ⟶
      puncturedPair ℂ (p + q) :=
  TopPair.ofSubsetHom (TopCat.ofHom (ContinuousMap.id _)) (fun z hz he =>
    hz ((hc9k_coordinate_intersection_zero p q z).mpr he))

/-- The normalized class of the coordinate intersection `{0} ⊆ ℂ^(p+q)`, in the degree
`2 * p + 2 * q` of a product of a codimension-`p` and a codimension-`q` class. At `p = 1` this
is `ccm17_intersectionClass q` after reindexing `Fin (1 + q)` as `Fin (q + 1)`.
Source: `normalizedPointCoclass`; Bott--Tu, §6, ordered complex normal orientation. -/
def hc9k_coordinateIntersectionClass (p q : ℕ) :
    RelativeCohomology ℚ
      (TopPair.ofSubset (X := TopCat.of (Fin (p + q) → ℂ))
        ((ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) p (hc9k_coordinateHead p q) ⊓
          ccm17_zeroSupport (TopCat.of (Fin (p + q) → ℂ)) q (hc9k_coordinateTail p q) :
            Closeds (Fin (p + q) → ℂ)) : Set (Fin (p + q) → ℂ))ᶜ)
      (2 * p + 2 * q) :=
  (show 2 * (p + q) = 2 * p + 2 * q by omega) ▸
    relativeCohomologyMap ℚ (2 * (p + q)) (hc9k_coordinateIntersectionPair p q)
      (normalizedPointCoclass (p + q))

/-- The existing scheme-theoretic intersection cycle, with Noetherianity supplied by
projectivity over the complex field.
Source: Fulton, *Intersection Theory*, second edition, §§1.5 and 8.2. -/
def hc9k_primeIntersectionCycle (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (x y : X.left) : AlgebraicCycle X.left ℚ := by
  letI := ccm12_isNoetherian X
  exact ccm11_intersectionCycle X.left (ccm3_primeIdeal X.left x)
    (ccm3_primeIdeal X.left y)

/-- The supported class obtained by summing the generic components of a prime
scheme-theoretic intersection with their local lengths.
Source: Fulton, *Intersection Theory*, second edition, §§1.5 and 19.1. -/
def hc9k_supportedIntersectionClass (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (p q : ℕ) (x y : X.left)
    (hcodim : ∀ w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme →
      Order.coheight ((ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subschemeι w) = p + q)
    (hsupport : ∀ w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
      closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme →
      cycleComponentAnalyticClosedSupport X
          ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w) ≤
        cycleComponentAnalyticClosedSupport X x ⊓
          cycleComponentAnalyticClosedSupport X y) :
    H_[cycleComponentAnalyticClosedSupport X x ⊓
      cycleComponentAnalyticClosedSupport X y]^(2 * (p + q))(X; ℚ) := by
  classical
  exact ∑ᶠ w : (ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subscheme,
    if hw : closure ({w} : Set (ccm3_primeIdeal X.left x ⊔
        ccm3_primeIdeal X.left y).subscheme) ∈
          irreducibleComponents (ccm3_primeIdeal X.left x ⊔
            ccm3_primeIdeal X.left y).subscheme then
      ((ccm11_intersectionLength X.left (ccm3_primeIdeal X.left x)
        (ccm3_primeIdeal X.left y) w).toNat : ℚ) •
        supportEnlarge X (hsupport w hw) (2 * (p + q))
          (cycleComponentSupportedInjectiveClass X
            ((ccm3_primeIdeal X.left x ⊔ ccm3_primeIdeal X.left y).subschemeι w)
            (hcodim w hw))
    else 0

/-- Two point components on the cubic group give a rational intersection cycle.
Source: Fulton, *Intersection Theory*, second edition, §1.5. -/
example : AlgebraicCycle HodgeLean.Foundations.Curves.E.left ℚ :=
  hc9k_primeIntersectionCycle HodgeLean.Foundations.Curves.E
    HodgeLean.Foundations.Curves.cubicInfinity HodgeLean.Foundations.Curves.cubicInfinity

/-- The bilinear intersection cycle obtained by summing the scheme-theoretic intersections of
all component pairs. Under transverse translation, the local statements below identify every
generic multiplicity with one.
Source: Fulton, *Intersection Theory*, second edition, §§1.3, 1.5, and 8.2. -/
def hc9k_transverseIntersectionCycle (X : Over (Spec ↧ℂ)) [GrpObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (c d : AlgebraicCycle X.left ℚ)
    (t : ComplexPoint X) : AlgebraicCycle X.left ℚ := by
  classical
  letI := ccm12_isNoetherian X
  exact ∑ᶠ x : X.left, ∑ᶠ y : X.left,
    (hc9k_primeIntersectionCycle X x (hc9k_translatePoint X t y)).mapRange
        (c x * d y * ·) (mul_zero _)

/-- The intersection product of two point cycles on the cubic group is an actual rational cycle.
Source: Fulton, *Intersection Theory*, second edition, §8.2. -/
example (c d : AlgebraicCycle HodgeLean.Foundations.Curves.E.left ℚ)
    (t : ComplexPoint HodgeLean.Foundations.Curves.E) :
    AlgebraicCycle HodgeLean.Foundations.Curves.E.left ℚ :=
  hc9k_transverseIntersectionCycle HodgeLean.Foundations.Curves.E c d t

end HodgeLean.Adapters
