import HodgeLean.Foundations.Program.SchoenCycleC1OffMarksEtaleSource
import HodgeLean.Foundations.Program.SchoenCycleC1ComplexFibreEtaleBase
import HodgeLean.Foundations.Program.SchoenCycleC1ComplexEtaleOpenDetection

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Empty selected branch indices give etaleness of the retained curve map. -/
theorem g32w09_curve_etale
    (S : g32p_Supplier) (Y Z : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdimY : TopologicalSpace.dim Y.left = 1)
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (hinj : Function.Injective a)
    (p₀ : Y ⟶ Z) [IsFinite p₀.left]
    (hp₀ : ∀ u, a u ≫ p₀ = p₀)
    (hpsurj : Function.Surjective (Point.map p₀))
    (hporbit : ∀ x y : ComplexPoint Y, Point.map p₀ x = Point.map p₀ y ↔
      ∃ u, Point.map (a u) x = y)
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y))
    (y : Fin (g32p_exponents S).length → rsq_Quot S.χ.ker C)
    (hbranch : ∀ z : rsq_Quot S.χ.ker C,
      MulAction.stabilizer (S.H ⧸ S.χ.ker) z ≠ ⊥ ↔
        ∃ t, Point.map p₀ (eY z) = Point.map p₀ (eY (y t)))
    (hempty : g32p_exponents S = []) : Etale p₀.left := by
  classical
  have hi : IsEmpty (Fin (g32p_exponents S).length) := by
    rw [hempty]
    change IsEmpty (Fin 0)
    infer_instance
  haveI : Etale (p₀.left ∣_ ⊤) := by
    apply s2e_c1_etale_restriction_of_complex_neighbourhoods Y.left Z p₀.left ⊤
    intro z _
    apply s2e_c1_etale_base_of_complex_fibre_neighbourhoods Y Z p₀ z
    intro x _
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := Z.left) (x := (Point.map p₀ x).underlying) (U := ⊤) (by trivial)
    have hx : (eY (eY.symm x)).underlying ∈ p₀.left ⁻¹ᵁ U := by
      change p₀.left (eY (eY.symm x)).underlying ∈ U
      simpa only [eY.apply_symm_apply, Point.underlying_map] using hxU
    obtain ⟨V, hv, _, _, het⟩ := s2e_c1_curve_etale_source_off_marks
      Y Z hdimY (S.H ⧸ S.χ.ker) a ha1 hamul hinj p₀ hpsurj hp₀ hporbit
      (rsq_Quot S.χ.ker C) (Fin (g32p_exponents S).length) eY.toEquiv
      hpointAction (fun t => Point.map p₀ (eY (y t))) hbranch
      (eY.symm x) (fun i => isEmptyElim i) U hU hx
    change (eY (eY.symm x)).underlying ∈ V at hv
    exact ⟨V, by simpa only [eY.apply_symm_apply] using hv, het⟩
  let j := (p₀.left ⁻¹ᵁ (⊤ : Z.left.Opens)).ι
  haveI : IsIso j := isIso_of_isOpenImmersion_of_opensRange_eq_top j (by
    dsimp only [j]
    rw [Scheme.Opens.opensRange_ι, Scheme.Hom.preimage_top])
  haveI : Etale (j ≫ p₀.left) := by
    dsimp only [j]
    rw [← morphismRestrict_ι]
    infer_instance
  have heq : p₀.left = inv j ≫ (j ≫ p₀.left) := by
    simp only [IsIso.inv_hom_id_assoc]
  rw [heq]
  infer_instance

#print axioms g32w09_curve_etale
end HodgeLean.Foundations.Program
