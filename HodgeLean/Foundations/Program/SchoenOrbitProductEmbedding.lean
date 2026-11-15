import HodgeLean.Foundations.Program.SchoenCoordinateActionLaws

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- The actual product of translates of a morphism, with the group elements retained as coordinate indices. -/
def s2_orbitProductMap {X P : Over (Spec ↧ℂ)} {G : Type} [Group G]
    (ρ : G →* Aut X) {n : ℕ} (e : Fin n ≃ G) (j : X ⟶ P) :
    X ⟶ g3_power P n :=
  s2_lift n (fun i => (ρ (e i)⁻¹).asIso.hom ≫ j)

/-- The product of translates intertwines the source action with the actual regular permutation of its factors. -/
theorem s2_orbitProductMap_equivariant {X P : Over (Spec ↧ℂ)} {G : Type} [Group G]
    (ρ : G →* Aut X) {n : ℕ} (e : Fin n ≃ G) (j : X ⟶ P) (g : G) :
    let σ : Equiv.Perm (Fin n) := e.trans ((Equiv.mulLeft g).trans e.symm)
    (ρ g).asIso.hom ≫ s2_orbitProductMap ρ e j =
      s2_orbitProductMap ρ e j ≫ s2_permute P n σ := by
  apply s2_product_hom_ext n
  intro i
  simp only [Category.assoc, s2_orbitProductMap, s2_permute, s2_check_lift_proj]
  have hi : e ((e.trans ((Equiv.mulLeft g).trans e.symm)).symm i) = g⁻¹ * e i := by
    simp
  rw [hi, mul_inv_rev, inv_inv, ← Category.assoc]
  exact (congrArg (fun f : Aut X => f.asIso.hom ≫ j) (ρ.map_mul ((e i)⁻¹) g)).symm

/-- A product of translates of a closed embedding is an actual closed embedding into the projective product. -/
theorem s2_orbitProductMap_isClosedImmersion {X P : Over (Spec ↧ℂ)} {G : Type} [Group G]
    [IsProjective P.hom] (ρ : G →* Aut X) {n : ℕ} (e : Fin n ≃ G)
    (j : X ⟶ P) [IsClosedImmersion j.left] :
    IsClosedImmersion (s2_orbitProductMap ρ e j).left := by
  let i : Fin n := e.symm 1
  have hfac : s2_orbitProductMap ρ e j ≫ g3_proj P n i = j := by
    rw [s2_orbitProductMap, s2_check_lift_proj]
    simp only [i, Equiv.apply_symm_apply, inv_one, map_one]
    exact Category.id_comp j
  haveI : IsClosedImmersion ((s2_orbitProductMap ρ e j).left ≫ (g3_proj P n i).left) := by
    rw [← Over.comp_left, hfac]
    infer_instance
  haveI : IsSeparated ((g3_proj P n i).left ≫ P.hom) := by
    rw [Over.w]
    infer_instance
  haveI : IsSeparated (g3_proj P n i).left := IsSeparated.of_comp _ P.hom
  exact IsClosedImmersion.of_comp _ (g3_proj P n i).left

/-- Every finite action on a projective complex scheme has an actual equivariant closed embedding into a regularly permuted projective-space product. -/
theorem s2_projective_equivariantProductEmbedding (X : Over (Spec ↧ℂ))
    [IsProjective X.hom] (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) :
    ∃ (d n : ℕ) (e : Fin n ≃ G),
      let P := Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ))
      ∃ j : X ⟶ g3_power P n, IsClosedImmersion j.left ∧
        ∀ g : G, (ρ g).asIso.hom ≫ j = j ≫ s2_permute P n
          (e.trans ((Equiv.mulLeft g).trans e.symm)) := by
  obtain ⟨Q⟩ := IsProjective.nonempty_presentation (f := X.hom)
  let P := Over.mk (ProjectiveSpace.toBase (Fin (Q.ambientDimension + 1)) (Spec ↧ℂ))
  let j : X ⟶ P := Over.homMk Q.immersion Q.immersion_toBase
  haveI : IsClosedImmersion j.left := Q.isClosedImmersion
  haveI : IsProjective P.hom :=
    ⟨⟨{ ambientDimension := Q.ambientDimension,
          immersion := 𝟙 _,
          immersion_toBase := Category.id_comp _ }⟩⟩
  letI := Fintype.ofFinite G
  let e : Fin (Fintype.card G) ≃ G := (Fintype.equivFin G).symm
  refine ⟨Q.ambientDimension, Fintype.card G, e, s2_orbitProductMap ρ e j,
    s2_orbitProductMap_isClosedImmersion ρ e j, ?_⟩
  exact s2_orbitProductMap_equivariant ρ e j

end HodgeLean.Foundations.Program
