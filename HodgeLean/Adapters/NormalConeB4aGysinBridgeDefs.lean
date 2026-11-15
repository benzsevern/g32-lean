import HodgeLean.Adapters.NormalConeB4Defs
import Mathlib.RingTheory.Regular.RegularSequence

/-! # Bridge stage of A3-B4a: slice objects

Algebraic slices of a closed subscheme `i : K ⟶ Z` of a scheme over `ℂ`. Sections `g` of `𝒪_Z`
on an open `U`, shifted by complex constants `a`, give germs in the local ring of `K` at a point
over `U`; `a3b4a_gysin_sliceSequence` is the list of these germs and `a3b4a_gysin_sliceLength`
is the exact length of the quotient of the local ring of `K` at a complex point by them. The
length is that of the full local ring, so nilpotents of `K` contribute. These are definitions of
objects; none of them asserts a property of a slice.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry

/-- Complex constants as sections on an open of a scheme over `ℂ`, through the structure map.
Source: Mathlib, `AlgebraicGeometry.Scheme.Hom.appLE` and `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
def a3b4a_gysin_sectionConst {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    (U : Z.Opens) : ℂ →+* Γ(Z, U) :=
  (q.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

example {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (U : Z.Opens) :
    a3b4a_gysin_sectionConst q U 1 = 1 :=
  map_one _

/-- The germs at a point `w` of `K` over `U` of the sections `g_j − a_j`, pulled back along `i`,
as a list in the local ring `𝒪_{K,w}`.
Source: Matsumura, *Commutative Ring Theory*, §16 (sequences of elements of a local ring);
Mathlib, `AlgebraicGeometry.Scheme.Hom.app` and `TopCat.Presheaf.germ`. -/
def a3b4a_gysin_sliceSequence {Z K : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    (i : K ⟶ Z) (U : Z.Opens) {n : ℕ} (g : Fin n → Γ(Z, U)) (a : Fin n → ℂ) (w : K)
    (hw : i.base w ∈ U) : List (K.presheaf.stalk w) :=
  List.ofFn fun j => K.presheaf.germ (i ⁻¹ᵁ U) w hw
    (i.app U (g j - a3b4a_gysin_sectionConst q U (a j)))

example {Z K : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (i : K ⟶ Z) (U : Z.Opens)
    {n : ℕ} (g : Fin n → Γ(Z, U)) (a : Fin n → ℂ) (w : K) (hw : i.base w ∈ U) :
    (a3b4a_gysin_sliceSequence q i U g a w hw).length = n :=
  List.length_ofFn

/-- The exact length of the slice of `K` by `g = a` at a complex point `w` of `K`: the length of
`𝒪_{K,w}/(g − a)` as a module over `𝒪_{K,w}`, possibly infinite. It is defined to be `0` at
points outside `U`, where the sections are not defined.
Source: Fulton, *Intersection Theory*, second edition, §1.2 and Example 7.1.10 (lengths of local
rings of slices); Mathlib, `Module.length` and `Ideal.ofList`. -/
def a3b4a_gysin_sliceLength {Z K : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ))
    (i : K ⟶ Z) (U : Z.Opens) {n : ℕ} (g : Fin n → Γ(Z, U)) (a : Fin n → ℂ)
    (w : ComplexPoint (Over.mk (i ≫ q))) : ℕ∞ := by
  classical
  exact if hw : i.base w.underlying ∈ U then
    Module.length (K.presheaf.stalk w.underlying)
      (K.presheaf.stalk w.underlying ⧸
        Ideal.ofList (a3b4a_gysin_sliceSequence q i U g a w.underlying hw))
  else 0

example {Z K : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (i : K ⟶ Z) (U : Z.Opens)
    {n : ℕ} (g : Fin n → Γ(Z, U)) (a : Fin n → ℂ) (w : ComplexPoint (Over.mk (i ≫ q)))
    (hw : i.base w.underlying ∉ U) : a3b4a_gysin_sliceLength q i U g a w = 0 := by
  simp [a3b4a_gysin_sliceLength, hw]

end HodgeLean.Adapters
