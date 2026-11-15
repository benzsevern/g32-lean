import HodgeLean.Foundations.Program.SchoenCycleC1ActualGeneratorCoefficientTransport
import HodgeLean.Foundations.Program.SchoenCycleC1MarkedProductExtension

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- The selected tuple's actual marked coefficient equation transports to
all original branch labels, using one for each absent branch. -/
theorem s2e_c1_actual_marked_coefficient_transport
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [QuasiCompact f]
    (φ : Y.functionField →+* X.functionField)
    (hφ : ∀ (p : X) (r : Y.presheaf.stalk (f p)),
      φ (algebraMap (Y.presheaf.stalk (f p)) Y.functionField r) =
        algebraMap (X.presheaf.stalk p) X.functionField ((f.stalkMap p).hom r))
    {I P : Type} [Fintype I] [DecidableEq P]
    (marks : I → P) (hinj : Function.Injective marks) (A : Finset P)
    (D : I → Y.IdealSheafData)
    (U : Y.affineOpens) (V : X.affineOpens) [Nonempty U.1] [Nonempty V.1]
    (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (b : A → Γ(Y, U.1)) (g : I → Γ(X, V.1))
    (hb : ∀ j, b j ≠ 0)
    (hDU : ∀ i (hi : marks i ∈ A), (D i).ideal U = Ideal.span {b ⟨marks i, hi⟩})
    (habsent : ∀ i, marks i ∉ A → (D i).ideal U = ⊤)
    (hDV : ∀ i, ((D i).comap f).ideal V = Ideal.span {g i})
    (n : P → ℤ) (u : Γ(Y, U.1)ˣ) (c : Y.functionField)
    (hc : c = Y.germToFunctionField U.1 (u : Γ(Y, U.1)) *
      ∏ j ∈ Finset.univ.filter (fun j : A => ∃ i, j.val = marks i),
        (Y.germToFunctionField U.1 (b j)) ^ n j.val) :
    ∃ v : Γ(X, V.1)ˣ, (∀ i, g i ≠ 0) ∧
      φ c = X.germToFunctionField V.1 (v : Γ(X, V.1)) *
        ∏ i, (X.germToFunctionField V.1 (g i)) ^ n (marks i) := by
  classical
  obtain ⟨bI, hbI, hbone, hprod⟩ := s2e_c1_marked_product_extension marks hinj A b
    (Y.germToFunctionField U.1).hom.toMonoidHom n
  have hne (i : I) : bI i ≠ 0 := by
    by_cases hi : marks i ∈ A
    · rw [hbI i hi]
      exact hb _
    · rw [hbone i hi]
      exact one_ne_zero
  have hDI (i : I) : (D i).ideal U = Ideal.span {bI i} := by
    by_cases hi : marks i ∈ A
    · rw [hbI i hi]
      exact hDU i hi
    · rw [hbone i hi, habsent i hi, Ideal.span_singleton_one]
  refine s2e_c1_actual_generator_coefficient_transport f φ hφ (J := I) D U V hVU bI g hne hDI hDV
    (fun i => n (marks i)) u c ?_
  exact hc.trans (congrArg (fun a => Y.germToFunctionField U.1 (u : Γ(Y, U.1)) * a) hprod)

end HodgeLean.Foundations.Program
