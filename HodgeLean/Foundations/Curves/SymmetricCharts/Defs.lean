import HodgeLean.Foundations.Curves.Picard.Families.OrderedRecursivePower
import HodgeLean.Foundations.Program.SchoenSymmetricProjectiveQuotient

/-! # Global symmetric quotient charts

The quotient and its affine charts are the existing invariant-spectrum colimit.
The literal M3 ordered power maps to it through its retained recursive comparison.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.Picard.Families

namespace HodgeLean.Foundations.Curves.SymmetricCharts

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- Permutations on the underlying recursive power, using the retained action.
Source: Milne, Jacobian Varieties, §3; `s2_symmetricPowerAction`. -/
abbrev action (C : Over (Spec ↧ℂ)) (n : ℕ) :=
  ((Over.forget (Spec ↧ℂ)).mapAut (g3_power C n)).comp (s2_symmetricPowerAction C n)

example (C : Over (Spec ↧ℂ)) :
    (action C 2 (1 : Equiv.Perm (Fin 2))).asIso.hom = 𝟙 _ := by
  rw [map_one]; rfl

/-- The product open contains every ordered coordinate in the specified curve open.
Source: Milne, Jacobian Varieties, §3, symmetric-power charts. -/
def productOpen (C : Over (Spec ↧ℂ)) (n : ℕ) (U : C.left.Opens) :
    (g3_power C n).left.Opens :=
  ⨅ i : Fin n, (g3_proj C n i).left ⁻¹ᵁ U

example (C : Over (Spec ↧ℂ)) (U : C.left.Opens) : productOpen C 0 U = ⊤ := by
  simp only [productOpen, iInf_of_empty]

section
variable (C : Over (Spec ↧ℂ)) [IsIntegral C.left] [Smooth C.hom]
  [IsProjective C.hom] (n : ℕ)

private instance powerAffineDiagonal :
    IsAffineHom (pullback.diagonal (terminal.from (g3_power C n).left)) := by
  haveI : IsSeparated (terminal.from (g3_power C n).left) := by
    rw [← terminal.comp_from (g3_power C n).hom]
    infer_instance
  infer_instance

/-- The existing nonempty invariant affine index, retaining its actual open subscheme.
Source: Mumford, Abelian Varieties, §II; `s2_InvariantAffineOpen`. -/
abbrev Index := s2_InvariantAffineOpen (g3_power C n).left (Equiv.Perm (Fin n)) (action C n)

example (W : Index C 2) : IsAffine W.val.toScheme := W.property.1

private theorem cover : ∀ x : (g3_power C n).left,
    ∃ W : Index C n, x ∈ W.val :=
  s2_projective_invariantAffineIndex_cover ℂ _ (g3_power C n).hom _ (action C n)

private theorem overAction (σ : Equiv.Perm (Fin n)) :
    (action C n σ).asIso.hom ≫ (g3_power C n).hom = (g3_power C n).hom :=
  Over.w ((s2_symmetricPowerAction C n σ).asIso.hom)

/-- The actual projective permutation quotient, as the existing glued invariant spectra.
Source: Milne, Jacobian Varieties, §3; `s2_gluedQuotientOver`. -/
def symmetricPower : Over (Spec ↧ℂ) :=
  s2_gluedQuotientOver (g3_power C n) (Equiv.Perm (Fin n)) (action C n)
    (overAction C n) (cover C n)

/-- The specified projection from the retained recursive power.
Source: Milne, Jacobian Varieties, §3; `s2_gluedQuotientOverMap`. -/
def projection : g3_power C n ⟶ symmetricPower C n :=
  s2_gluedQuotientOverMap (g3_power C n) (Equiv.Perm (Fin n)) (action C n)
    (overAction C n) (cover C n)

example : g3_power C 2 ⟶ symmetricPower C 2 := projection C 2

example : g3_power C 3 ⟶ symmetricPower C 3 := projection C 3

/-- The same projection on M3's literal categorical product, without changing its type.
Source: Milne, Jacobian Varieties, §3; M3 `orderedRecursiveIso`. -/
def orderedProjection : OrderedPower C n ⟶ symmetricPower C n :=
  (orderedRecursiveIso C n).hom ≫ projection C n

example : OrderedPower C 2 ⟶ symmetricPower C 2 := orderedProjection C 2

/-- The invariant spectrum of an affine source chart.
Source: Mumford, Abelian Varieties, §II; `s2_invariantAffineQuotientObj`. -/
abbrev affineChart (W : Index C n) :=
  s2_invariantAffineQuotientObj (g3_power C n).left _ (action C n) W

/-- The actual chart inclusion into the projective quotient.
Source: Milne, Jacobian Varieties, §3; `s2_invariantAffineGluedι`. -/
abbrev chartInclusion (W : Index C n) : affineChart C n W ⟶ (symmetricPower C n).left :=
  s2_invariantAffineGluedι (g3_power C n).left _ (action C n) W

example (W : Index C 2) : IsOpenImmersion (chartInclusion C 2 W) :=
  s2_invariantAffineGluedι_openImmersion _ _ _ W

example (W : Index C 2) : affineChart C 2 W ⟶ (symmetricPower C 2).left :=
  chartInclusion C 2 W

/-- The quotient projection on the affine source chart, before global gluing.
Source: Mumford, Abelian Varieties, §II; `s2_invariantAffineProjection`. -/
abbrev affineProjection (W : Index C n) : W.val.toScheme ⟶ affineChart C n W :=
  s2_invariantAffineProjection (g3_power C n).left _ (action C n) W

example (W : Index C 2) : W.val.toScheme ⟶ affineChart C 2 W := affineProjection C 2 W

/-- The inclusion-induced comparison of two invariant affine spectra.
Source: Milne, Jacobian Varieties, §3; `s2_invariantAffineQuotientMap`. -/
abbrev chartMap (U V : Index C n) (h : U ≤ V) : affineChart C n U ⟶ affineChart C n V :=
  s2_invariantAffineQuotientMap (g3_power C n).left _ (action C n) U V h

example (U V : Index C 2) (h : U ≤ V) : IsOpenImmersion (chartMap C 2 U V h) := by
  exact s2_quotientComparison_openImmersion _ _ _ _ _

/-- The actual intersection index, with its invariant affine scheme structure.
Source: Milne, Jacobian Varieties, §3; `s2_invariantAffineOpenInf`. -/
abbrev intersection (U V : Index C n) : Index C n :=
  s2_invariantAffineOpenInf (g3_power C n).left _ (action C n) U V

example (U V : Index C 2) (x : (g3_power C 2).left) :
    x ∈ (intersection C 2 U V).val ↔ x ∈ U.val ∧ x ∈ V.val := Iff.rfl

end
end HodgeLean.Foundations.Curves.SymmetricCharts
