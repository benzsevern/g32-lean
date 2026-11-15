import HodgeLean.Foundations.Program.TorusAlgebraizationB54CoverIncidence
import HodgeLean.Foundations.Program.TorusAlgebraizationB54ThetaIncidence

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)

/-- Products of theta coordinates at two points differing by a fixed translation.
Source: Hartshorne, Algebraic Geometry, Exercise II.5.11. -/
def b54_translationCoordinates {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (b5_sections Λ F hF Q 3)) (a z : b5_V Λ F) :
    Fin (n * n) → ℂ := fun k =>
  (b (finProdFinEquiv.symm k).1).val z * (b (finProdFinEquiv.symm k).2).val (z + a)

theorem b54_translationCoordinates_differentiable {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (b5_sections Λ F hF Q 3)) (a : b5_V Λ F)
    (k : Fin (n * n)) :
    Differentiable ℂ (fun z => b54_translationCoordinates Λ F hF Q b a z k) := by
  exact (b (finProdFinEquiv.symm k).1).property.1.mul
    ((b (finProdFinEquiv.symm k).2).property.1.comp (differentiable_id.add_const a))

theorem b54_translationCoordinates_cover_eq {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (b5_sections Λ F hF Q 3)) (a z w : b5_V Λ F)
    (h : b2_torusCover Λ F z = b2_torusCover Λ F w) :
    ∃ c : ℂ, c ≠ 0 ∧ b54_translationCoordinates Λ F hF Q b a z =
      c • b54_translationCoordinates Λ F hF Q b a w := by
  have ha : b2_torusCover Λ F (z + a) = b2_torusCover Λ F (w + a) := by
    have hadd (u v : b5_V Λ F) : b2_torusCover Λ F (u + v) =
        b2_torusCover Λ F u + b2_torusCover Λ F v := by
      simp [b2_torusCover, b2_coordHomeomorph, map_add]
    rw [hadd, hadd, h]
  obtain ⟨c, hc, he⟩ := b54_sectionCoordinates_cover_eq Λ F hF Q b z w h
  obtain ⟨d, hd, he'⟩ := b54_sectionCoordinates_cover_eq Λ F hF Q b (z + a) (w + a) ha
  refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
  funext k
  have hi := congrFun he (finProdFinEquiv.symm k).1
  have hj := congrFun he' (finProdFinEquiv.symm k).2
  change (b _).val z = c * (b _).val w at hi
  change (b _).val (z + a) = d * (b _).val (w + a) at hj
  change (b _).val z * (b _).val (z + a) = (c * d) * ((b _).val w * (b _).val (w + a))
  rw [hi, hj]
  ring

theorem b54_translationCoordinates_ne_zero {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (b5_sections Λ F hF Q 3)) (a z : b5_V Λ F)
    (hbase : ∀ z, ∃ s : b5_sections Λ F hF Q 3, s.val z ≠ 0) :
    b54_translationCoordinates Λ F hF Q b a z ≠ 0 := by
  have hi := b54_sectionCoordinates_ne_zero Λ F hF Q b z (hbase z)
  have hj := b54_sectionCoordinates_ne_zero Λ F hF Q b (z + a) (hbase (z + a))
  obtain ⟨i, hi⟩ : ∃ i, (b i).val z ≠ 0 := by
    by_contra h
    exact hi (funext fun i => not_ne_iff.mp (not_exists.mp h i))
  obtain ⟨j, hj⟩ : ∃ j, (b j).val (z + a) ≠ 0 := by
    by_contra h
    exact hj (funext fun j => not_ne_iff.mp (not_exists.mp h j))
  intro he
  have hh := congrFun he (finProdFinEquiv (i, j))
  exact mul_ne_zero hi hj (by simpa [b54_translationCoordinates] using hh)

theorem b54_translation_cone_algebraic {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (b5_sections Λ F hF Q 3)) (a : b5_V Λ F)
    (hbase : ∀ z, ∃ s : b5_sections Λ F hF Q 3, s.val z ≠ 0) :
    ∃ (m : ℕ) (d : Fin m → ℕ) (P : Fin m → MvPolynomial (Fin (n * n)) ℂ),
      (∀ i, (P i).IsHomogeneous (d i)) ∧
      ∀ v, (∀ i, MvPolynomial.eval v (P i) = 0) ↔
        ∃ (z : b5_V Λ F) (c : ℂ), v = c • b54_translationCoordinates Λ F hF Q b a z := by
  obtain ⟨m, d, P, hP, he⟩ := b54_cover_cone_algebraic Λ F hF (n * n)
    (b54_translationCoordinates Λ F hF Q b a)
    (b54_translationCoordinates_differentiable Λ F hF Q b a)
    (b54_translationCoordinates_cover_eq Λ F hF Q b a)
  refine ⟨m, d, P, hP, fun v => ?_⟩
  change v ∈ {v | ∀ i, MvPolynomial.eval v (P i) = 0} ↔ _
  rw [← he]
  exact b54_cover_cone_mem_iff Λ F _
    (fun z => b54_translationCoordinates_ne_zero Λ F hF Q b a z hbase) v

end HodgeLean.Foundations.Program
