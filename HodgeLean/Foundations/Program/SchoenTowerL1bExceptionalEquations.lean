import HodgeLean.Foundations.Program.SchoenTowerL1bCartierPullback
import HodgeLean.Foundations.Program.SchoenTowerL1bEarlierMaps
import HodgeLean.Foundations.Program.SchoenTowerL1bGenericEquations

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Earlier centre total pullbacks have simultaneous nonzero equations on the final base. -/
theorem s2v_l1b_earlier_centre_equations
    {n : ℕ} (B : Fin (n + 1) → Scheme)
    [∀ j, IsIntegral (B j)]
    (b : ∀ j : Fin n, B j.succ ⟶ B j.castSucc)
    (c : ∀ j, B (Fin.last n) ⟶ B j)
    [∀ j, IsDominant (c j)] [∀ j, QuasiCompact (c j)]
    (hb : ∀ j : Fin n, c j.succ ≫ b j = c j.castSucc)
    (I : ∀ j : Fin n, (B j.castSucc).IdealSheafData)
    (hcartier : ∀ (j : Fin n) (y : B j.succ),
      ∃ W : (B j.succ).affineOpens, y ∈ W.1 ∧
        Nonempty (((I j).comap (b j)).ideal W ≃ₗ[Γ(B j.succ, W)] Γ(B j.succ, W)))
    (x : B (Fin.last n)) (V : (B (Fin.last n)).Opens) (hxV : x ∈ V) :
    ∃ U : (B (Fin.last n)).affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧
      ∃ eE : Fin n → Γ(B (Fin.last n), U),
        ∀ j, ((I j).comap (c j.castSucc)).ideal U = Ideal.span {eE j} ∧ eE j ≠ 0 := by
  apply s2v_l1b_simultaneous_nonzero_principal_neighborhood
    (B (Fin.last n)) (fun j => (I j).comap (c j.castSucc)) x V hxV
  intro j
  obtain ⟨U, hxU, g, hg, hgn⟩ := s2v_l1b_cartier_pullback_equation
    (c j.succ) ((I j).comap (b j)) x (hcartier j (c j.succ x))
  refine ⟨U, hxU, g, ?_, hgn⟩
  rwa [← Scheme.IdealSheafData.comap_comp, hb j] at hg

/-- The retained proper tower supplies earlier centre equations with nonzero generic product. -/
theorem s2v_l1b_proper_tower_exceptional_equations
    {n : ℕ} (B : Fin (n + 1) → Over (Spec ↧ℂ))
    [∀ j, IsIntegral (B j).left] [∀ j, IsProjective (B j).hom]
    (b : ∀ j : Fin n, B j.succ ⟶ B j.castSucc)
    (I : ∀ j : Fin n, (B j.castSucc).left.IdealSheafData)
    (hcartier : ∀ (j : Fin n) (y : (B j.succ).left),
      ∃ W : (B j.succ).left.affineOpens, y ∈ W.1 ∧
        Nonempty (((I j).comap (b j).left).ideal W ≃ₗ[Γ((B j.succ).left, W)]
          Γ((B j.succ).left, W)))
    {K : Type} [Field K] (η : ∀ j, Spec (.of K) ⟶ (B j).left)
    [∀ j, IsDominant (η j)]
    (hη : ∀ j : Fin n, η j.succ ≫ (b j).left = η j.castSucc)
    (x : (B (Fin.last n)).left) (V : (B (Fin.last n)).left.Opens) (hxV : x ∈ V) :
    ∃ (c : ∀ j, B (Fin.last n) ⟶ B j)
      (U : (B (Fin.last n)).left.affineOpens)
      (hηU : ⊤ ≤ η (Fin.last n) ⁻¹ᵁ U.1)
      (eE : Fin n → Γ((B (Fin.last n)).left, U)),
      c (Fin.last n) = 𝟙 _ ∧
      (∀ j : Fin n, c j.succ ≫ b j = c j.castSucc) ∧
      x ∈ U.1 ∧ U.1 ≤ V ∧
      (∀ j, ((I j).comap (c j.castSucc).left).ideal U = Ideal.span {eE j}) ∧
      ((η (Fin.last n)).appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
        (∏ j, eE j) ≠ 0 := by
  obtain ⟨c, hc, hb⟩ := s2v_l1b_earlier_maps n B b
  have hgen := s2v_l1b_earlier_maps_generic (fun j => (B j).left)
    (fun j => (b j).left) (fun j => (c j).left)
    (congrArg Over.Hom.left hc) (fun j => congrArg Over.Hom.left (hb j))
    (Spec (.of K)) η hη
  letI : ∀ j, IsDominant (c j).left := fun j => by
    have : IsDominant (η (Fin.last n) ≫ (c j).left) := by
      rw [hgen j]
      infer_instance
    exact IsDominant.of_comp (η (Fin.last n)) (c j).left
  letI : ∀ j, IsProper (c j).left := fun j => by
    have : IsProper ((c j).left ≫ (B j).hom) := by
      rw [Over.w]
      infer_instance
    exact IsProper.of_comp (c j).left (B j).hom
  obtain ⟨U, hxU, hUV, eE, hE⟩ := s2v_l1b_earlier_centre_equations
    (fun j => (B j).left) (fun j => (b j).left) (fun j => (c j).left)
    (fun j => congrArg Over.Hom.left (hb j)) I hcartier x V hxV
  let : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  have hηU : ⊤ ≤ η (Fin.last n) ⁻¹ᵁ U.1 := by
    intro z _
    change η (Fin.last n) z ∈ U.1
    rw [Subsingleton.elim z (genericPoint (Spec (.of K))),
      s2_dominant_genericPoint (η (Fin.last n))]
    exact ((genericPoint_spec (B (Fin.last n)).left).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using (show Nonempty U.1 from inferInstance))
  refine ⟨c, U, hηU, eE, hc, hb, hxU, hUV, fun j => (hE j).1, ?_⟩
  intro hz
  have hprod : (∏ j, eE j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => (hE j).2
  apply hprod
  exact s2v_l1b_dominant_section_map_injective (B (Fin.last n)).left
    (η (Fin.last n)) U.1 hηU (hz.trans (map_zero _).symm)

end HodgeLean.Foundations.Program
