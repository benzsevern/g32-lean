import HodgeLean.Foundations.Program.SchoenTowerI1aOrbitIntersections

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_neighborhood_from_finite_set_affines
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    [IsProjective X.hom]
    (N : X.left.Opens) (hN : ∀ g, N ≤ (a g).left ⁻¹ᵁ N)
    (hfinite : ∀ s : Finset X.left, (∀ x ∈ s, x ∈ N) →
      ∃ A : X.left.Opens, IsAffineOpen A ∧ A ≤ N ∧ ∀ x ∈ s, x ∈ A)
    (x : X.left) (hx : x ∈ N) :
    ∃ U : X.left.Opens, IsAffineOpen U ∧ U ≤ N ∧
      (∀ g, U ≤ (a g).left ⁻¹ᵁ U) ∧ ∀ g, (a g).left x ∈ U := by
  classical
  letI := Fintype.ofFinite G
  let s := Finset.univ.image (fun g : G => (a g).left x)
  have hs : ∀ y ∈ s, y ∈ N := by
    intro y hy
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hy
    exact hN g hx
  obtain ⟨A, hA, hAN, hsA⟩ := hfinite s hs
  have horbit : ∀ g, (a g).left x ∈ A := by
    intro g
    exact hsA _ (Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩)
  exact ⟨_, s2v_i1ahi_orbit_intersection X G a ha1 hamul N A hA hAN x horbit⟩

lemma s2v_i1ahi_cover_from_finite_set_affines
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    [IsProjective X.hom]
    (hfinite : ∀ (N : X.left.Opens) (s : Finset X.left), (∀ x ∈ s, x ∈ N) →
      ∃ A : X.left.Opens, IsAffineOpen A ∧ A ≤ N ∧ ∀ x ∈ s, x ∈ A) :
    (⨆ U : {U : X.left.affineOpens // ∀ g, U.1 ≤ (a g).left ⁻¹ᵁ U.1}, U.1.1) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨U, hU, _, hi, hx⟩ := s2v_i1ahi_neighborhood_from_finite_set_affines X G a ha1 hamul
    ⊤ (fun _ _ _ => trivial) (hfinite ⊤) x trivial
  have hxU : x ∈ U := by
    have h := hx 1
    rw [ha1] at h
    exact h
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hi⟩, hxU⟩

end HodgeLean.Foundations.Program
