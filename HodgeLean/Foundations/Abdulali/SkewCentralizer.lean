import HodgeLean.Foundations.Abdulali.MatrixCentralizer
import Mathlib.Tactic.LinearCombination

noncomputable section
namespace HodgeLean.Foundations.Abdulali

/-- The alternating tensor-product form in two-copy coordinates.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.2 and §4, p. 923. -/
def multiplicityAlternatingForm {U : Type*} [AddCommGroup U] [Module ℂ U]
    (B : LinearMap.BilinForm ℂ U) : LinearMap.BilinForm ℂ (Fin 2 → U) :=
  B.compl₁₂ (LinearMap.proj 0) (LinearMap.proj 1) -
    B.compl₁₂ (LinearMap.proj 1) (LinearMap.proj 0)

example {U : Type*} [AddCommGroup U] [Module ℂ U]
    (B : LinearMap.BilinForm ℂ U) (z w : Fin 2 → U) :
    multiplicityAlternatingForm B z w = B (z 0) (w 1) - B (z 1) (w 0) := rfl

/-- In split matrix coordinates, the polarization-skew centralizer is exactly
the orthogonal Lie algebra on the multiplicity space. This is an equality of
conditions on actual operators, with a unique multiplicity operator.
The calculation works for all bilinear forms; symmetry and nondegeneracy are
retained by `polarized_multiplicity_aux` when this is used for type III.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.2 and §4, p. 923. -/
theorem split_skew_centralizer_normal_form {U : Type*} [AddCommGroup U] [Module ℂ U]
    (B : LinearMap.BilinForm ℂ U) (X : Module.End ℂ (Fin 2 → U)) :
    ((∀ (m : Matrix (Fin 2) (Fin 2) ℂ) z,
        X (twoCopyAction m z) = twoCopyAction m (X z)) ∧
      ∀ z w, multiplicityAlternatingForm B (X z) w +
        multiplicityAlternatingForm B z (X w) = 0) ↔
    ∃! T : Module.End ℂ U,
      (∀ u v, B (T u) v + B u (T v) = 0) ∧
      ∀ z i, X z i = T (z i) := by
  classical
  constructor
  · rintro ⟨hcomm, hskew⟩
    obtain ⟨T, hT, huniq⟩ := (matrix_centralizer_multiplicity X).mp hcomm
    refine ⟨T, ⟨?_, hT⟩, ?_⟩
    · intro u v
      have h := hskew (Pi.single 0 u) (Pi.single 1 v)
      simpa [multiplicityAlternatingForm, hT] using h
    · intro S hS
      exact huniq S hS.2
  · rintro ⟨T, ⟨hskew, hT⟩, _⟩
    refine ⟨(matrix_centralizer_multiplicity X).mpr ⟨T, hT, ?_⟩, ?_⟩
    · intro S hS
      ext u
      have h := (hS (Pi.single 0 u) 0).symm.trans (hT (Pi.single 0 u) 0)
      simpa using h
    · intro z w
      change (B (X z 0) (w 1) - B (X z 1) (w 0)) +
        (B (z 0) (X w 1) - B (z 1) (X w 0)) = 0
      rw [hT, hT, hT, hT]
      have h01 := hskew (z 0) (w 1)
      have h10 := hskew (z 1) (w 0)
      linear_combination h01 - h10

end HodgeLean.Foundations.Abdulali
