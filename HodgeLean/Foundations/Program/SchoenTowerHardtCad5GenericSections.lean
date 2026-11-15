import HodgeLean.Foundations.Program.SchoenTowerHardtCad5GenericNeighborhoods
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5FiniteSections

/-! Local finite-section membership at generic Boolean parameter points. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_generic_finite_sections_mem
    {n : ℕ} {ι Y : Type*} [Fintype ι] [TopologicalSpace Y] [T2Space Y]
    (K : Subfield ℝ) (C : s2v_t11b_Formula n) (M : ι → s2v_t11b_Formula n)
    (hCcoeff : ∀ p ∈ C.atoms, ∃ q : MvPolynomial (Fin n) K, MvPolynomial.map K.subtype q = p)
    (hMcoeff : ∀ i p, p ∈ (M i).atoms → ∃ q : MvPolynomial (Fin n) K,
      MvPolynomial.map K.subtype q = p)
    (f : ι → C.realize → Y) (hf : ∀ i, Continuous (f i))
    (S : Set (Y × EuclideanSpace ℝ (Fin n)))
    (hCover : ∀ y (a : C.realize), (y, a.val) ∈ S → ∃ i, y = f i a)
    (hM : ∀ i (a : C.realize), a.val ∈ (M i).realize ↔ (f i a, a.val) ∈ S)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ C.realize)
    (hgen : AlgebraicIndependent K (fun i => a i)) (y : Y)
    (hcl : (y, a) ∈ closure S) : (y, a) ∈ S := by
  classical
  have hCN : ∀ᶠ b in nhds a, b ∈ C.realize := mem_interior_iff_mem_nhds.mp
    (s2v_hardt_cad5_generic_mem_interior K C hCcoeff a hgen ha)
  have hMN : ∀ᶠ b in nhds a, ∀ i, (b ∈ (M i).realize ↔ a ∈ (M i).realize) :=
    Filter.eventually_all.mpr (fun i =>
      s2v_hardt_cad5_generic_membership_eventually K (M i) (hMcoeff i) a hgen)
  obtain ⟨V, hVsub, hVopen, haV⟩ := mem_nhds_iff.mp (hCN.and hMN)
  have hVC : V ⊆ C.realize := fun _ h => (hVsub h).1
  let I := {i : ι // a ∈ (M i).realize}
  let g : I → V → Y := fun i b => f i.val ⟨b.val, hVC b.property⟩
  have hinc : Continuous (fun b : V => (⟨b.val, hVC b.property⟩ : C.realize)) :=
    continuous_subtype_val.subtype_mk _
  have hg : ∀ i, Continuous (g i) := fun i => (hf i.val).comp hinc
  apply s2v_hardt_cad5_mem_of_closure_finite_sections V hVopen g hg S ?_ y a haV hcl
  intro z b hb
  let bC : C.realize := ⟨b, hVC hb⟩
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := hCover z bC hz
    have hbM : b ∈ (M i).realize := (hM i bC).mpr (by simpa only [hi] using hz)
    have haM : a ∈ (M i).realize := ((hVsub hb).2 i).mp hbM
    exact ⟨⟨i, haM⟩, hi⟩
  · rintro ⟨i, hi⟩
    have hbM : b ∈ (M i.val).realize := ((hVsub hb).2 i.val).mpr i.property
    have hz := (hM i.val bC).mp hbM
    simpa only [hi] using hz

end HodgeLean.Foundations.Program
