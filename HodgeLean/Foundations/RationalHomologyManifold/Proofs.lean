import HodgeLean.Foundations.RationalHomologyManifold.Checks
import HodgeLean.Foundations.RationalHomologyManifold.CapNaturality
import HodgeLean.Foundations.RationalHomologyManifold.CapLeftZero
import HodgeLean.Foundations.RationalHomologyManifold.CapLocalToGlobal
import HodgeLean.Foundations.RationalHomologyManifold.CapRightZero
import HodgeLean.Foundations.QuotientDuality.LocalOrientationNaturality
import HodgeLean.Foundations.RationalHomologyManifold.ZeroDimension
import HodgeLean.Foundations.RationalHomologyManifold.LocalCoefficients
import HodgeLean.Foundations.RationalHomologyManifold.CompactDetection
import HodgeLean.Foundations.QuotientDuality.LocalTriangulationConnectedness

/-! # Rational homology manifold gluing and cap interfaces

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
theorem fundamental_exists_aux (X : TopCat.{0}) [CompactSpace X] [T2Space X] [ConnectedSpace X]
    (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X n) :
    ∃ c : Homology ℚ X n, localization X n c = o.generator := by
  by_cases hn : n = 0
  · subst n
    letI := triangulated_pathConnected X t.ambient t.complex t.finite_faces t.realization
    letI := subsingleton_of_zero_orientation X o
    obtain ⟨c, hc, _⟩ := singleton_fundamental_class X 0 o
    exact ⟨c, funext hc⟩
  obtain ⟨c, hc, _⟩ := fundamental_class_of_compact_detection X n o
    (finiteTriangulation_compact_detection X t n o)
  exact ⟨c, funext hc⟩

example := Checks.exists_falsification

/-- A single local normalization determines the top class on a connected space.
Source: Bredon, Sheaf Theory, second edition, V.9–10 and V.16; Hatcher, Theorem 3.26.
HC no distance; AV milestone no distance.
-/
theorem fundamental_unique_at_point_aux (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    [ConnectedSpace X] (t : FiniteTriangulation X) (n : ℕ) (o : LocalRationalOrientation X n)
    (c d : Homology ℚ X n) (x : X)
    (hx : localization X n c x = localization X n d x) : c = d := by
  by_cases hn : n = 0
  · subst n
    letI := triangulated_pathConnected X t.ambient t.complex t.finite_faces t.realization
    letI := subsingleton_of_zero_orientation X o
    exact singleton_localization_injective X 0 x hx
  have hall := localization_eq_of_eq_at_point X n o c d x hx
  obtain ⟨e, he, hu⟩ := fundamental_class_of_compact_detection X n o
    (finiteTriangulation_compact_detection X t n o)
  have hw : localization X n (e + (c - d)) = o.generator := by
    rw [map_add, map_sub, hall, sub_self, add_zero]
    exact funext he
  have hz : e + (c - d) = e := hu _ (fun y => congrFun hw y)
  exact sub_eq_zero.mp (add_left_cancel (hz.trans (add_zero e).symm))

example := Checks.uniqueness_falsification

/-- Cap with the normalized fundamental class is bijective in every complementary degree.
Source: Bredon, Sheaf Theory, second edition, V.9–10 and V.16; Hatcher, Theorem 3.30 (manifold case).
HC no distance; AV milestone no distance.
-/
theorem cap_duality_aux (X : TopCat.{0}) [CompactSpace X] [T2Space X] [ConnectedSpace X]
    (t : FiniteTriangulation X) (p q : ℕ) (o : LocalRationalOrientation X (p + q))
    (c : Homology ℚ X (p + q)) (hc : localization X (p + q) c = o.generator) :
    Function.Bijective (localTraceCap X p q c) := by
  by_cases hp : p = 0
  · subst p
    exact cap_left_zero_bijective X t q o c hc
  by_cases hq : q = 0
  · subst q
    exact cap_right_zero_bijective X t p o c hc
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact cap_positive X t p q o c hc

example := Checks.cap_falsification

/-- A homeomorphism preserving local generators transports the fundamental class.
Source: Hatcher, section 3.3, Theorem 3.26 and naturality of relative homology.
HC no distance; AV milestone no distance.
-/
theorem homeomorph_fundamental_aux (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    [ConnectedSpace X] (t : FiniteTriangulation X)
    (Y : TopCat.{0}) [CompactSpace Y] [T2Space Y] [ConnectedSpace Y]
    (s : FiniteTriangulation Y) (n : ℕ)
    (oX : LocalRationalOrientation X n) (oY : LocalRationalOrientation Y n)
    (c : Homology ℚ X n) (d : Homology ℚ Y n)
    (hc : localization X n c = oX.generator) (hd : localization Y n d = oY.generator)
    (H : X ≃ₜ Y)
    (hH : ∀ x, relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H x)
      (oX.generator x) = oY.generator (H x)) :
    homologyMap ℚ n (TopCat.ofHom ⟨H, H.continuous⟩) c = d := by
  let x : X := Classical.choice inferInstance
  apply fundamental_unique_at_point_aux Y s n oY _ d (H x)
  change localOrientation Y n _ (H x) = localOrientation Y n d (H x)
  calc
    _ = relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H x)
        (localOrientation X n c x) :=
      (localOrientation_map n x (H x) (pointComplementHomeomorphPairMap H x) c).symm
    _ = oY.generator (H x) := by
      change relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H x)
        (localization X n c x) = _
      rw [congrFun hc x]
      exact hH x
    _ = localOrientation Y n d (H x) := (congrFun hd (H x)).symm

example := Checks.homeomorph_falsification

/-- Oriented homeomorphisms commute with cap, with contravariant cohomology.
Source: Hatcher, section 3.3, cap naturality and Theorem 3.30.
HC no distance; AV milestone no distance.
-/
theorem homeomorph_cap_aux (X : TopCat.{0}) [CompactSpace X] [T2Space X]
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
      localTraceCap Y p q d a := by
  rw [cap_naturality]
  rw [homeomorph_fundamental_aux X t Y s (p + q) oX oY c d hc hd H hH]

example := Checks.cap_naturality_falsification

end HodgeLean.Foundations.RationalHomologyManifold
