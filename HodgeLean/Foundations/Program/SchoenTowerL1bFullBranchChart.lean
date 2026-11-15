import HodgeLean.Foundations.Program.SchoenTowerL1bSuccessorBranchEquations
import HodgeLean.Foundations.Program.SchoenTowerL1bWeightedCoordinatePullback

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An injective branch atlas retains every branch index except the branch absent on this chart. -/
theorem s2v_l1b_full_branch_chart
    {X Y : Scheme} (f : X ⟶ Y) {J σ : Type} [DecidableEq J] [DecidableEq σ]
    (D : J → Y.IdealSheafData) (K : Y.IdealSheafData)
    (U : Y.affineOpens) (V : X.affineOpens) (hV : V.1 ≤ f ⁻¹ᵁ U.1)
    {k : Type} [CommRing k] [IsDomain k]
    (c : k →+* Γ(X, V)) (z : σ → Γ(Y, U)) (w : σ → Γ(X, V))
    (het : (MvPolynomial.eval₂Hom c w).Etale)
    (A : Set J) (g : A ↪ σ)
    (hD : ∀ j : A, (D j).ideal U = Ideal.span {z (g j)})
    (hunit : ∀ j, j ∉ A → (D j).ideal U = ⊤)
    (p q : J) (hpq : p ≠ q) (hp : p ∈ A) (hq : q ∈ A)
    (hK : K.ideal U = Ideal.span {z (g ⟨p, hp⟩), z (g ⟨q, hq⟩)})
    (hcoords : ∀ t, (f.appLE U.1 V.1 hV).hom (z t) =
      if t = g ⟨p, hp⟩ then w (g ⟨p, hp⟩) * w (g ⟨q, hq⟩) else w t) :
    ∃ g' : {j : J // j ∈ A ∧ j ≠ q} ↪ σ,
      (∀ j, (s2c_strictTransform f (D j.val) K).ideal V = Ideal.span {w (g' j)}) ∧
      (∀ j, ¬ (j ∈ A ∧ j ≠ q) → (s2c_strictTransform f (D j) K).ideal V = ⊤) := by
  classical
  have hab : g ⟨p, hp⟩ ≠ g ⟨q, hq⟩ := by
    intro H
    exact hpq (congrArg (fun t : A => t.val) (g.injective H))
  have hrest (j : J) (hjp : j ≠ p) (hjq : j ≠ q) :
      (D j).ideal U = ⊤ ∨ ∃ t, t ≠ g ⟨p, hp⟩ ∧ t ≠ g ⟨q, hq⟩ ∧
        (D j).ideal U = Ideal.span {z t} := by
    by_cases hj : j ∈ A
    · refine Or.inr ⟨g ⟨j, hj⟩, ?_, ?_, hD ⟨j, hj⟩⟩
      · intro H; exact hjp (congrArg (fun t : A => t.val) (g.injective H))
      · intro H; exact hjq (congrArg (fun t : A => t.val) (g.injective H))
    · exact Or.inl (hunit j hj)
  obtain ⟨hP, hQ, hR⟩ := s2v_l1b_successor_branch_equations f D K U V hV c z w het
    (g ⟨p, hp⟩) (g ⟨q, hq⟩) hab p q hcoords (hD ⟨p, hp⟩) (hD ⟨q, hq⟩) hK hrest
  let g' : {j : J // j ∈ A ∧ j ≠ q} ↪ σ :=
    ⟨fun j => g ⟨j.val, j.property.1⟩, fun j l H =>
      Subtype.ext (congrArg (fun t : A => t.val) (g.injective H))⟩
  refine ⟨g', ?_, ?_⟩
  · intro j
    by_cases hjp : j.val = p
    · subst p
      exact hP
    · have hjq := j.property.2
      have ht : (D j.val).ideal U = Ideal.span {z (g ⟨j.val, j.property.1⟩)} := hD ⟨j.val, j.property.1⟩
      apply s2v_l1b_etale_chart_branch_step f (D j.val) K U V hV c z w het
        (g ⟨p, hp⟩) (g ⟨q, hq⟩) (g ⟨j.val, j.property.1⟩) hab
      · intro H; exact hjp (congrArg (fun t : A => t.val) (g.injective H))
      · intro H; exact hjq (congrArg (fun t : A => t.val) (g.injective H))
      · exact hcoords
      · exact ht
      · rw [hK]; exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · intro j hj
    by_cases hjq : j = q
    · subst j; exact hQ
    · have hnot : j ∉ A := fun h => hj ⟨h, hjq⟩
      apply s2v_l1b_strictTransform_unit_chart
      rw [s2v_l1b_comap_ideal_affine_charts f (D j) U V hV, hunit j hnot, Ideal.map_top]

end HodgeLean.Foundations.Program
