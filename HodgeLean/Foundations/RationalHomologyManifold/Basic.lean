import HodgeLean.Foundations.RationalHomologyManifold.Proofs

/-! # Rational homology manifold public gluing and cap statements

Implication from finite triangulation and coherent concentrated local rational
homology to global singular gluing and cap duality. No Euclidean charts are assumed.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Gluing the coherent orientation section produces an actual singular class.
Source: Bredon, Sheaf Theory, second edition, V.9–10 and V.16; Hatcher, Theorem 3.26 (manifold case).
HC no distance; AV milestone no distance.
-/
theorem fundamental_exists (X : TopCat.{0}) [CompactSpace X] [T2Space X] [ConnectedSpace X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X n) :
    ∃ c : Homology ℚ X n, localization X n c = o.generator :=
  fundamental_exists_aux X t n o

example := Checks.exists_falsification

/-- A single local normalization determines the top class on a connected space.
Source: Bredon, Sheaf Theory, second edition, V.9–10 and V.16; Hatcher, Theorem 3.26.
HC no distance; AV milestone no distance.
-/
theorem fundamental_unique_at_point (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    [ConnectedSpace X] (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X n)
    (c d : Homology ℚ X n) (x : X)
    (hx : localization X n c x = localization X n d x) : c = d :=
  fundamental_unique_at_point_aux X t n o c d x hx

example := Checks.uniqueness_falsification

/-- Cap with the normalized fundamental class is bijective in every complementary degree.
Source: Bredon, Sheaf Theory, second edition, V.9–10 and V.16; Hatcher, Theorem 3.30 (manifold case).
HC no distance; AV milestone no distance.
-/
theorem cap_duality (X : TopCat.{0}) [CompactSpace X] [T2Space X] [ConnectedSpace X]
    (t : FiniteTriangulation X) (p q : ℕ) (o : LocalRationalOrientation X (p + q))
    (c : Homology ℚ X (p + q)) (hc : localization X (p + q) c = o.generator) :
    Function.Bijective (localTraceCap X p q c) :=
  cap_duality_aux X t p q o c hc

example := Checks.cap_falsification

/-- A homeomorphism preserving local generators transports the fundamental class.
Source: Hatcher, section 3.3, Theorem 3.26 and naturality of relative homology.
HC no distance; AV milestone no distance.
-/
theorem homeomorph_fundamental (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    [ConnectedSpace X] (t : FiniteTriangulation X)
    (Y : TopCat.{0}) [CompactSpace Y] [T2Space Y] [ConnectedSpace Y]
    (s : FiniteTriangulation Y) (n : ℕ)
    (oX : LocalRationalOrientation X n) (oY : LocalRationalOrientation Y n)
    (c : Homology ℚ X n) (d : Homology ℚ Y n)
    (hc : localization X n c = oX.generator) (hd : localization Y n d = oY.generator)
    (H : X ≃ₜ Y)
    (hH : ∀ x, relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H x)
      (oX.generator x) = oY.generator (H x)) :
    homologyMap ℚ n (TopCat.ofHom ⟨H, H.continuous⟩) c = d :=
  homeomorph_fundamental_aux X t Y s n oX oY c d hc hd H hH

example := Checks.homeomorph_falsification

/-- Oriented homeomorphisms commute with cap, with contravariant cohomology.
Source: Hatcher, section 3.3, cap naturality and Theorem 3.30.
HC no distance; AV milestone no distance.
-/
theorem homeomorph_cap (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    [ConnectedSpace X] (t : FiniteTriangulation X)
    (Y : TopCat.{0}) [CompactSpace Y] [T2Space Y] [ConnectedSpace Y]
    (s : FiniteTriangulation Y) (p q : ℕ)
    (oX : LocalRationalOrientation X (p + q)) (oY : LocalRationalOrientation Y (p + q))
    (c : Homology ℚ X (p + q)) (d : Homology ℚ Y (p + q))
    (hc : localization X (p + q) c = oX.generator)
    (hd : localization Y (p + q) d = oY.generator)
    (H : X ≃ₜ Y)
    (hH : ∀ x, relativeHomologyMap ℚ (p + q) (pointComplementHomeomorphPairMap H x)
      (oX.generator x) = oY.generator (H x)) (a : Cohomology ℚ Y p) :
    homologyMap ℚ q (TopCat.ofHom ⟨H, H.continuous⟩)
      (localTraceCap X p q c (cohomologyMap ℚ p (TopCat.ofHom ⟨H, H.continuous⟩) a)) =
      localTraceCap Y p q d a :=
  homeomorph_cap_aux X t Y s p q oX oY c d hc hd H hH a

example := Checks.cap_naturality_falsification

end HodgeLean.Foundations.RationalHomologyManifold
