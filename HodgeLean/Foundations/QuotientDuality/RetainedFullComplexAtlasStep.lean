import HodgeLean.Foundations.QuotientDuality.RetainedFullBranchNeighborhood
import HodgeLean.Foundations.Program.SchoenTowerL1bFullAtlasStep

/-! Persistence of the full branch atlas over the actual complex base. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- A full injective branch atlas persists through the retained blowup and gives its weighted identity. -/
theorem retained_full_complex_atlas_step
    (B X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (f : X ⟶ B) {J σ : Type} [Fintype J] [DecidableEq J] [DecidableEq σ]
    (D : J → B.left.IdealSheafData) (p q : J) (hpq : p ≠ q)
    (hcartier : ∀ x : X.left, ∃ V : X.left.affineOpens, x ∈ V.1 ∧
      Nonempty (((((D p ⊔ D q).comap f.left)).ideal V) ≃ₗ[Γ(X.left, V)] Γ(X.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (g : T ⟶ B),
      (∀ x : T.left, ∃ V : T.left.affineOpens, x ∈ V.1 ∧
        Nonempty (((((D p ⊔ D q).comap g.left)).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! k : T ⟶ X, k ≫ f = g)
    (hcoords : ∀ x : ComplexPoint B,
      ∃ (U : B.left.affineOpens)
        (z : σ → Γ(B.left, U)) (A : Set J) (g : A ↪ σ),
        x.underlying ∈ U.1 ∧ (MvPolynomial.eval₂Hom (complexAffineCoefficient B U) z).Etale ∧
        (∀ j : A, (D j).ideal U = Ideal.span {z (g j)}) ∧
        (∀ j, j ∉ A → (D j).ideal U = ⊤))
    (n : J → ℕ) (m : ℕ) (hn : n p + n q = m) :
    (∏ j, ((D j).comap f.left) ^ n j) =
      (∏ j, (s2c_strictTransform f.left (D j) (D p ⊔ D q)) ^ n j) *
        ((D p ⊔ D q).comap f.left) ^ m ∧
    ∀ x : ComplexPoint X,
      ∃ (V : X.left.affineOpens)
        (z : σ → Γ(X.left, V)) (A : Set J) (g : A ↪ σ),
        x.underlying ∈ V.1 ∧ (MvPolynomial.eval₂Hom (complexAffineCoefficient X V) z).Etale ∧
        (∀ j : A, (s2c_strictTransform f.left (D j) (D p ⊔ D q)).ideal V = Ideal.span {z (g j)}) ∧
        (∀ j, j ∉ A → (s2c_strictTransform f.left (D j) (D p ⊔ D q)).ideal V = ⊤) := by
  classical
  let K := D p ⊔ D q
  have hlocal (x : ComplexPoint X) :
      ∃ (V : X.left.affineOpens)
        (z : σ → Γ(X.left, V)) (A : Set J) (g : A ↪ σ),
        x.underlying ∈ V.1 ∧ (MvPolynomial.eval₂Hom (complexAffineCoefficient X V) z).Etale ∧
        (∀ j : A, (s2c_strictTransform f.left (D j) K).ideal V = Ideal.span {z (g j)}) ∧
        (∀ j, j ∉ A → (s2c_strictTransform f.left (D j) K).ideal V = ⊤) ∧
        (∏ j, ((D j).comap f.left) ^ n j).ideal V =
          ((∏ j, (s2c_strictTransform f.left (D j) K) ^ n j) *
            (K.comap f.left) ^ m).ideal V := by
    obtain ⟨U, z, A, g, hxU, het, hD, ht⟩ := hcoords (Point.map f x)
    have hx : f.left x.underlying ∈ U.1 := by
      simpa only [Point.underlying_map] using hxU
    by_cases hpqA : p ∈ A ∧ q ∈ A
    · have hK : K.ideal U = Ideal.span {z (g ⟨p, hpqA.1⟩), z (g ⟨q, hpqA.2⟩)} := by
        change (D p).ideal U ⊔ (D q).ideal U = _
        rw [hD ⟨p, hpqA.1⟩, hD ⟨q, hpqA.2⟩, ← Ideal.span_union, Set.singleton_union]
      exact retained_full_branch_neighborhood B X f D K hcartier hblowup U z het
        A g hD ht p q hpq hpqA.1 hpqA.2 hK n m hn x.underlying hx
    · have hK : K.ideal U = ⊤ := by
        change (D p).ideal U ⊔ (D q).ideal U = _
        by_cases hp : p ∈ A
        · rw [ht q (fun hq => hpqA ⟨hp, hq⟩), sup_top_eq]
        · rw [ht p hp, top_sup_eq]
      haveI : IsIso (f.left ∣_ U.1) :=
        s2v_l1b_blowup_isIso_on_unit_affine B X f K hcartier hblowup U hK
      obtain ⟨V, hV, w, hw, hKV, hred, htr, hz⟩ :=
        s2v_l1b_off_centre_coordinates f.left D K U (complexAffineCoefficient B U) z het hK (fun j => by
          by_cases hj : j ∈ A
          · exact Or.inr ⟨g ⟨j, hj⟩, hD ⟨j, hj⟩⟩
          · exact Or.inl (ht j hj))
      have hw_actual : (MvPolynomial.eval₂Hom (complexAffineCoefficient X V) w).Etale := by
        rw [← complexAffineCoefficient_pullback B X f U V (le_of_eq hV)]
        exact hw
      refine ⟨V, w, A, g, ?_, hw_actual, ?_, ?_, ?_⟩
      · rw [hV]; exact hx
      · intro j
        rw [htr, s2v_l1b_comap_ideal_affine_charts f.left (D j) U V (le_of_eq hV),
          hD j, Ideal.map_span, Set.image_singleton, hz]
      · intro j hj
        rw [htr, s2v_l1b_comap_ideal_affine_charts f.left (D j) U V (le_of_eq hV),
          ht j hj, Ideal.map_top]
      · exact s2v_l1b_weighted_transform_off_centre f.left D K V hKV hred n m
  choose V z A g hx het hD ht hEq using hlocal
  refine ⟨?_, fun x => ⟨V x, z x, A x, g x, hx x, het x, hD x, ht x⟩⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V _ hEq
  exact s2v_l1b_complex_open_cover X (fun x => (V x).1) (fun x => ⟨x, hx x⟩)

#print axioms retained_full_complex_atlas_step
end HodgeLean.Foundations.QuotientDuality
