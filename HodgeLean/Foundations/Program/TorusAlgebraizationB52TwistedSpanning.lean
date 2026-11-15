import HodgeLean.Foundations.Program.TorusAlgebraizationB52TwistedSections
import HodgeLean.Foundations.Program.TorusAlgebraizationB52TracedProducts

noncomputable section
namespace HodgeLean.Foundations.Program
open scoped TensorProduct

variable (Λ : Type*) [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (Q : LinearMap.BilinForm ℤ Λ)
    (hherm : ∀ z w, star (b5_H Λ F hF Q w z) = b5_H Λ F hF Q z w)
    (himag : ∀ l m, (b5_H Λ F hF Q (b5_lattice Λ F l)
      (b5_lattice Λ F m)).im = (Q l m : ℝ))
    (hcocycle : ∀ l m z, b5_factor Λ F hF Q (l + m) z =
      b5_factor Λ F hF Q l (z + b5_lattice Λ F m) * b5_factor Λ F hF Q m z)

include hherm himag hcocycle in
theorem b52_eq_top_of_twisted_products (i j : ℕ) (hij : i + j ≠ 0)
    [Module.Finite ℂ (b5_sections Λ F hF Q ((i + j) * (i * (i + j))))]
    (t : b5_sections Λ F hF Q ((i + j) * (i * j))) (ht : t.val 0 ≠ 0)
    (W : Submodule ℂ (b5_sections Λ F hF Q (i + j)))
    (hW : ∀ (χ : AddChar Λ ℂ) (u : b52_characterSections Λ F hF Q i χ)
      (v : b52_characterSections Λ F hF Q j (-χ)),
      b52_oppositeCharacterProduct Λ F hF Q i j χ u v ∈ W) :
    W = ⊤ := by
  apply top_unique
  intro s _
  obtain ⟨r, u, v, hs⟩ := b52_section_finite_traced_products Λ F hF Q
    hherm himag hcocycle (i + j) i j hij s t ht
  rw [hs]
  apply W.sum_mem
  intro a _
  have hi : (i + j) * (i * (i + j)) = i * (i + j) ^ 2 := by ring
  have hj : (i + j) * (j * (i + j)) = j * (i + j) ^ 2 := by ring
  let u' : b5_sections Λ F hF Q (i * (i + j) ^ 2) :=
    ⟨(u a).val, by rw [← hi]; exact (u a).property⟩
  let v' : b5_sections Λ F hF Q (j * (i + j) ^ 2) :=
    ⟨(v a).val, by rw [← hj]; exact (v a).property⟩
  have he : b52_weightedDiagonalSection Λ F hF Q (i + j) i j (u a) (v a) =
      b52_pullbackProductBilinear Λ F hF Q i j (i + j) u' v' := by
    apply Subtype.ext
    rfl
  rw [he]
  exact b52_trace_product_mem_of_twisted_products Λ F hF Q hherm himag hcocycle
    i j (i + j) hij W hW u' v'

include hherm himag hcocycle in
theorem b52_cubic_eq_top_of_twisted_products
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (i j : ℕ) (hij : i + j ≠ 0)
    [Module.Finite ℂ (b5_sections Λ F hF Q
      ((3 * i + 3 * j) * ((3 * i) * (3 * i + 3 * j))))]
    (W : Submodule ℂ (b5_sections Λ F hF Q (3 * i + 3 * j)))
    (hW : ∀ (χ : AddChar Λ ℂ) (u : b52_characterSections Λ F hF Q (3 * i) χ)
      (v : b52_characterSections Λ F hF Q (3 * j) (-χ)),
      b52_oppositeCharacterProduct Λ F hF Q (3 * i) (3 * j) χ u v ∈ W) :
    W = ⊤ := by
  obtain ⟨s, hs⟩ := b52_exists_nonzero_section Λ F hF Q hherm himag hpos hcocycle
  obtain ⟨c, hc⟩ := b52_basepoint_of_nonzero_section Λ F hF Q s hs 0
  let t : b5_sections Λ F hF Q ((3 * i + 3 * j) * ((3 * i) * (3 * j))) :=
    ⟨(b52_powerSection Λ F hF Q 3 ((i + j) * ((3 * i) * (3 * j))) c).val, by
      convert (b52_powerSection Λ F hF Q 3 ((i + j) * ((3 * i) * (3 * j))) c).property
        using 1 <;> congr 1 <;> ring⟩
  apply b52_eq_top_of_twisted_products Λ F hF Q hherm himag hcocycle
    (3 * i) (3 * j) (by omega) t (pow_ne_zero _ hc) W hW

include hherm himag hcocycle in
theorem b52_multiplication_surjective_of_twisted_products
    (hpos : ∀ x : b5_V Λ F, x ≠ 0 → 0 < (b5_H Λ F hF Q x x).re)
    (i j : ℕ) (hij : i + j ≠ 0)
    [Module.Finite ℂ (b5_sections Λ F hF Q
      ((3 * i + 3 * j) * ((3 * i) * (3 * i + 3 * j))))]
    (hproducts : ∀ (χ : AddChar Λ ℂ)
      (u : b52_characterSections Λ F hF Q (3 * i) χ)
      (v : b52_characterSections Λ F hF Q (3 * j) (-χ)),
      ∃ w : b5_sections Λ F hF Q (3 * i) ⊗[ℂ] b5_sections Λ F hF Q (3 * j),
        ∀ z, (b52_sectionMultiplication Λ F hF Q i j w).val z = u.val z * v.val z) :
    Function.Surjective (b52_sectionMultiplication Λ F hF Q i j) := by
  let M := b52_sectionMultiplication Λ F hF Q i j
  let L : b5_sections Λ F hF Q (3 * i) ⊗[ℂ] b5_sections Λ F hF Q (3 * j) →ₗ[ℂ]
      b5_sections Λ F hF Q (3 * i + 3 * j) :=
    { toFun w := ⟨(M w).val, by simpa only [Nat.mul_add] using (M w).property⟩
      map_add' w v := by
        apply Subtype.ext
        exact congrArg (fun t : b5_sections Λ F hF Q (3 * (i + j)) ↦ t.val)
          (M.map_add w v)
      map_smul' c w := by
        apply Subtype.ext
        exact congrArg (fun t : b5_sections Λ F hF Q (3 * (i + j)) ↦ t.val)
          (M.map_smul c w) }
  have hL : LinearMap.range L = ⊤ := by
    apply b52_cubic_eq_top_of_twisted_products Λ F hF Q hherm himag hcocycle
      hpos i j hij
    intro χ u v
    obtain ⟨w, hw⟩ := hproducts χ u v
    refine ⟨w, ?_⟩
    apply Subtype.ext
    funext z
    exact hw z
  intro s
  let s' : b5_sections Λ F hF Q (3 * i + 3 * j) :=
    ⟨s.val, by simpa only [Nat.mul_add] using s.property⟩
  obtain ⟨w, hw⟩ := LinearMap.range_eq_top.mp hL s'
  refine ⟨w, ?_⟩
  apply Subtype.ext
  have he := congrArg (fun t : b5_sections Λ F hF Q (3 * i + 3 * j) ↦ t.val) hw
  exact he

end HodgeLean.Foundations.Program
