import HodgeLean.Foundations.Program.G32Native.PELIsometryGroup
import HodgeLean.Foundations.HodgeGroupAlgebraic

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations MvPolynomial

/-- Rational isometry and commutator equations define a rational algebraic group.
Source: Borel, Linear Algebraic Groups, second edition, §§1.6–1.7. -/
theorem pelIsometryGroup_isRatAlg {n : ℕ}
    (Ω : Matrix (Fin n) (Fin n) ℚ) (S : Set (Matrix (Fin n) (Fin n) ℚ)) :
    g2_IsRatAlgSubgroup
      ((pelIsometryGroup (Ω.map (algebraMap ℚ ℂ))
        ((fun T => T.map (algebraMap ℚ ℂ)) '' S)).carrier : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) := by
  let G := pelIsometryGroup (Ω.map (algebraMap ℚ ℂ))
    ((fun T => T.map (algebraMap ℚ ℂ)) '' S)
  refine ⟨⟨{f | ∃ i j : Fin n, f = g1_isometryEquations Ω i j} ∪
    {f | ∃ T ∈ S, ∃ i j : Fin n, f = g2_commEquations T i j}, ?_⟩,
    G.carrier.one_mem, fun _ hx _ hy => G.carrier.mul_mem hx hy,
    fun _ hx => G.carrier.inv_mem hx⟩
  ext g
  change ((g : Matrix (Fin n) (Fin n) ℂ).transpose * Ω.map (algebraMap ℚ ℂ) * g = Ω.map (algebraMap ℚ ℂ) ∧
    ∀ T ∈ ((fun T => T.map (algebraMap ℚ ℂ)) '' S), (g : Matrix (Fin n) (Fin n) ℂ) * T = T * g) ↔
    ∀ f ∈ _, aeval (g1_coords g) f = 0
  constructor
  · rintro ⟨hg, hc⟩ f (⟨i, j, rfl⟩ | ⟨T, hT, i, j, rfl⟩)
    · rw [g2k_aeval_isometryEquations, g2k_mat_coords, hg, sub_self]; rfl
    · rw [g2k_aeval_commEquations, g2k_mat_coords]
      rw [hc _ ⟨T, hT, rfl⟩, sub_self]; rfl
  · intro h
    constructor
    · apply sub_eq_zero.mp
      ext i j
      have he := h _ (Or.inl ⟨i, j, rfl⟩)
      rw [g2k_aeval_isometryEquations, g2k_mat_coords] at he
      exact he
    · rintro _ ⟨T, hT, rfl⟩
      apply sub_eq_zero.mp
      ext i j
      have he := h _ (Or.inr ⟨T, hT, i, j, rfl⟩)
      rw [g2k_aeval_commEquations, g2k_mat_coords] at he
      exact he

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)

/-- An operator preserving each Hodge summand commutes with the entire Hodge circle.
Source: Abdulali, Annals of Mathematics 155 (2002), §2.1, p. 917. -/
theorem circleAction_commutes_of_preserves
    (T : Module.End ℂ (ℂ ⊗[ℚ] V))
    (hT : ∀ pq x, x ∈ H pq → T x ∈ H pq) (z : Circle) :
    g2_circleAction H hH z * T = T * g2_circleAction H hH z := by
  apply linearMap_ext_of_isInternal hH
  rintro ⟨p, q⟩ x hx
  change g2_circleAction H hH z (T x) = T (g2_circleAction H hH z x)
  rw [g2_circleAction_apply_of_mem H hH z (hT _ _ hx),
    g2_circleAction_apply_of_mem H hH z hx, map_smul]

/-- Connectedness places the Hodge group in the identity component of any
rational PEL isometry group containing its circle.
Source: Abdulali, Annals of Mathematics 155 (2002), §§2.1, 3.2. -/
theorem hodgeGroup_subset_pelGenericGroup {n : ℕ}
    (b : Module.Basis (Fin n) ℚ V)
    (Ω : Matrix (Fin n) (Fin n) ℚ) (S : Set (Matrix (Fin n) (Fin n) ℚ))
    (hc : g2_circleImage H hH b ⊆
      (pelIsometryGroup (Ω.map (algebraMap ℚ ℂ))
        ((fun T => T.map (algebraMap ℚ ℂ)) '' S)).carrier) :
    g2_hodgeGroup H hH b ⊆ pelGenericGroup (Ω.map (algebraMap ℚ ℂ))
      ((fun T => T.map (algebraMap ℚ ℂ)) '' S) := by
  have hs : g2_hodgeGroup H hH b ⊆
      (pelIsometryGroup (Ω.map (algebraMap ℚ ℂ))
        ((fun T => T.map (algebraMap ℚ ℂ)) '' S)).carrier :=
    Set.sInter_subset_of_mem ⟨pelIsometryGroup_isRatAlg Ω S, hc⟩
  exact @IsPreconnected.subset_connectedComponentIn _ (g1_zariski ℂ n)
    _ _ _ (@IsConnected.isPreconnected _ (g1_zariski ℂ n) _
      (g2_hodgeGroup_isConnected H hH b))
    (g2_isRatAlgSubgroup_hodgeGroup H hH b).2.1 hs

#print axioms pelIsometryGroup_isRatAlg
#print axioms circleAction_commutes_of_preserves
#print axioms hodgeGroup_subset_pelGenericGroup
end HodgeLean.Foundations.Program.GeneralTypeIII
