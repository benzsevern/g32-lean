import HodgeLean.Foundations.AnalyticDivisorAlgebraic15Defs

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic15

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic8
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14

/-- Source: Griffiths--Harris, Ch. 1 §1; reflexivity of association of germs. -/
theorem spec_equivalentLocalDivisorData_refl_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) : EquivalentLocalDivisorData V f V f := by
  exact hD.2.2.2.2

private theorem areAssociatedAt_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f g : E → ℂ} {x : E} (h : AreAssociatedAt f g x) :
    AreAssociatedAt g f x := by
  obtain ⟨u, hu, hu0, hfg⟩ := h
  refine ⟨fun y ↦ (u y)⁻¹, hu.inv hu0, inv_ne_zero hu0, ?_⟩
  filter_upwards [hfg, hu.continuousAt.eventually_ne hu0] with y hy huy
  rw [hy, ← mul_assoc, inv_mul_cancel₀ huy, one_mul]

/-- Source: Griffiths--Harris, Ch. 1 §1; symmetry of association of germs. -/
theorem spec_equivalentLocalDivisorData_symm_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι κ : Type*} {V : ι → Set E} {f : ι → E → ℂ}
    {W : κ → Set E} {g : κ → E → ℂ} (h : EquivalentLocalDivisorData V f W g) :
    EquivalentLocalDivisorData W g V f := by
  intro j i x hx
  exact areAssociatedAt_symm (h i j x ⟨hx.2, hx.1⟩)

private theorem areAssociatedAt_trans {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f g q : E → ℂ} {x : E} (hfg : AreAssociatedAt f g x)
    (hgq : AreAssociatedAt g q x) : AreAssociatedAt f q x := by
  obtain ⟨u, hu, hu0, hfg'⟩ := hfg
  obtain ⟨v, hv, hv0, hgq'⟩ := hgq
  refine ⟨fun y ↦ u y * v y, hu.mul hv, mul_ne_zero hu0 hv0, ?_⟩
  filter_upwards [hfg', hgq'] with y hy hz
  rw [hy, hz, mul_assoc]

/-- Source: Griffiths--Harris, Ch. 1 §1; transitivity for valid endpoint and middle families. -/
theorem spec_equivalentLocalDivisorData_trans_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι κ μ : Type*} {U : Set E}
    {V : ι → Set E} {f : ι → E → ℂ} {W : κ → Set E} {g : κ → E → ℂ}
    {R : μ → Set E} {q : μ → E → ℂ} (hF : IsLocalDivisorData U V f)
    (hG : IsLocalDivisorData U W g) (hQ : IsLocalDivisorData U R q)
    (hfg : EquivalentLocalDivisorData V f W g)
    (hgq : EquivalentLocalDivisorData W g R q) : EquivalentLocalDivisorData V f R q := by
  intro i k x hx
  have hxU : x ∈ U := by
    rw [← hF.2.1]
    exact Set.mem_iUnion_of_mem i hx.1
  rw [← hG.2.1] at hxU
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxU
  exact areAssociatedAt_trans (hfg i j x ⟨hx.1, hj⟩) (hgq j k x ⟨hj, hx.2⟩)

private theorem zero_iff_of_areAssociatedAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f g : E → ℂ} {x : E} (h : AreAssociatedAt f g x) :
    f x = 0 ↔ g x = 0 := by
  obtain ⟨u, _, hu0, hfg⟩ := h
  rw [hfg.self_of_nhds]
  simp only [mul_eq_zero, hu0, false_or]

/-- Source: Griffiths--Harris, Ch. 1 §1; equivalent local equations have the same support. -/
theorem spec_equivalentLocalDivisorData_support_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι κ : Type*} {U : Set E}
    {V : ι → Set E} {f : ι → E → ℂ} {W : κ → Set E} {g : κ → E → ℂ}
    (hD : IsLocalDivisorData U V f) (hG : IsLocalDivisorData U W g)
    (h : EquivalentLocalDivisorData V f W g) :
    localDivisorSupport V f = localDivisorSupport W g := by
  ext x
  constructor
  · rintro ⟨i, hi, hfi⟩
    have hxU : x ∈ U := by
      rw [← hD.2.1]
      exact Set.mem_iUnion_of_mem i hi
    rw [← hG.2.1] at hxU
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxU
    exact ⟨j, hj, (zero_iff_of_areAssociatedAt (h i j x ⟨hi, hj⟩)).mp hfi⟩
  · rintro ⟨j, hj, hgj⟩
    have hxU : x ∈ U := by
      rw [← hG.2.1]
      exact Set.mem_iUnion_of_mem j hj
    rw [← hD.2.1] at hxU
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
    exact ⟨i, hi, (zero_iff_of_areAssociatedAt (h i j x ⟨hi, hj⟩)).mpr hgj⟩

/-- Source: Gunning--Rossi, II.B, Definition 1; invariance under a unit germ. -/
private theorem productAnalyticGermOf_isUnit_at_origin {n : ℕ}
    {f : (Fin n → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 ≠ 0) :
    IsUnit (productAnalyticGermOf f hf) := by
  let q : ProductAnalyticGerm n := productAnalyticGermOf (fun z ↦ (f z)⁻¹) (hf.inv hf0)
  apply isUnit_iff_exists_inv.mpr
  refine ⟨q, ?_⟩
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hf.continuousAt.eventually_ne hf0] with z hz
  exact mul_inv_cancel₀ hz

theorem spec_equivalentLocalDivisorData_localDivisorAt_aux {n : ℕ} {ι κ : Type*}
    {V : ι → Set ((Fin n → ℂ) × ℂ)} {f : ι → (Fin n → ℂ) × ℂ → ℂ}
    {W : κ → Set ((Fin n → ℂ) × ℂ)} {g : κ → (Fin n → ℂ) × ℂ → ℂ}
    (h : EquivalentLocalDivisorData V f W g) (i : ι) (j : κ)
    (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) (hj : p ∈ W j)
    (hf : AnalyticAt ℂ (f i) p) (hg : AnalyticAt ℂ (g j) p) :
    localDivisorAt n (f i) p = localDivisorAt n (g j) p := by
  obtain ⟨u, hu, hu0, hfg⟩ := h i j p ⟨hi, hj⟩
  have htr : AnalyticAt ℂ (fun z ↦ p + z) 0 := analyticAt_const.add analyticAt_id
  have hft : AnalyticAt ℂ (fun z ↦ f i (p + z)) 0 := by
    have hf' : AnalyticAt ℂ (f i) (p + 0) := by simpa only [add_zero] using hf
    exact hf'.comp htr
  have hgt : AnalyticAt ℂ (fun z ↦ g j (p + z)) 0 := by
    have hg' : AnalyticAt ℂ (g j) (p + 0) := by simpa only [add_zero] using hg
    exact hg'.comp htr
  have hut : AnalyticAt ℂ (fun z ↦ u (p + z)) 0 := by
    have hu' : AnalyticAt ℂ u (p + 0) := by simpa only [add_zero] using hu
    exact hu'.comp htr
  let F : ProductAnalyticGerm n := productAnalyticGermOf (fun z ↦ f i (p + z)) hft
  let G : ProductAnalyticGerm n := productAnalyticGermOf (fun z ↦ g j (p + z)) hgt
  let A : ProductAnalyticGerm n := productAnalyticGermOf (fun z ↦ u (p + z)) hut
  have hA : IsUnit A := productAnalyticGermOf_isUnit_at_origin hut (by simpa using hu0)
  have heq : F = A * G := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    have hmap : Tendsto (fun z ↦ p + z) (𝓝 0) (𝓝 p) := by
      have hmap' : Tendsto (fun z ↦ p + z) (𝓝 0) (𝓝 (p + 0)) := htr.continuousAt
      simpa only [add_zero] using hmap'
    change (fun z ↦ f i (p + z)) =ᶠ[𝓝 0] fun z ↦ u (p + z) * g j (p + z)
    exact hfg.comp_tendsto hmap
  have hassoc : Associated F G := by
    rw [heq, mul_comm]
    simpa only [mul_one] using Associated.mul_left G ((associated_one_iff_isUnit.mpr hA))
  simp only [localDivisorAt, hft, hgt, ↓reduceDIte]
  exact spec_localDivisor_associated n F G hassoc

/-- Source: Griffiths--Harris, Ch. 1 §1; intersections of two equivalent covers give a common
refinement. -/
theorem spec_equivalentLocalDivisorData_commonRefinement_aux {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {ι κ : Type*} {U : Set E}
    {V : ι → Set E} {f : ι → E → ℂ} {W : κ → Set E} {g : κ → E → ℂ}
    (hD : IsLocalDivisorData U V f) (hG : IsLocalDivisorData U W g)
    (h : EquivalentLocalDivisorData V f W g) :
    IsLocalDivisorData U (fun ij : ι × κ ↦ V ij.1 ∩ W ij.2) (fun ij ↦ f ij.1) ∧
      (∀ ij : ι × κ, V ij.1 ∩ W ij.2 ⊆ V ij.1) ∧
      (∀ ij : ι × κ, V ij.1 ∩ W ij.2 ⊆ W ij.2) := by
  have hCover : (⋃ ij : ι × κ, V ij.1 ∩ W ij.2) = U := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨ij, hx⟩ := Set.mem_iUnion.mp hx
      rw [← hD.2.1]
      exact Set.mem_iUnion_of_mem ij.1 hx.1
    · intro x hx
      have hxV : x ∈ ⋃ i, V i := by simpa only [hD.2.1] using hx
      have hxW : x ∈ ⋃ j, W j := by simpa only [hG.2.1] using hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxV
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxW
      exact Set.mem_iUnion_of_mem (i, j) ⟨hi, hj⟩
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, hCover, ?_, ?_, ?_⟩
    · intro ij
      exact (hD.1 ij.1).inter (hG.1 ij.2)
    · intro ij
      exact (hD.2.2.1 ij.1).mono fun _ hx ↦ hx.1
    · intro ij x hx
      exact hD.2.2.2.1 ij.1 x hx.1
    · intro ij kl x hx
      exact hD.2.2.2.2 ij.1 kl.1 x ⟨hx.1.1, hx.2.1⟩
  · intro ij
    exact fun _ hx ↦ hx.1
  · intro ij x hx
    exact hx.2

/-- Source: Gunning--Rossi, II.B, Theorems 3--6; Chirka §2.3, on the support after translation. -/
private theorem isIrreducibleAt_translate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {P : E → ℂ} {p : E} (hirr : IsIrreducibleAt P p) :
    IsIrreducibleAt (fun z ↦ P (p + z)) 0 := by
  refine ⟨by simpa using hirr.1, ?_⟩
  intro g h hg hh hfac
  have hsubA : AnalyticAt ℂ (fun y : E ↦ y - p) p := analyticAt_id.sub analyticAt_const
  have hsub : Tendsto (fun y : E ↦ y - p) (nhds p) (nhds (0 : E)) := by
    have hc := hsubA.continuousAt
    change Tendsto (fun y : E ↦ y - p) (nhds p) (nhds (p - p)) at hc
    simpa using hc
  have hg' : AnalyticAt ℂ (fun y ↦ g (y - p)) p := hg.comp_of_eq hsubA (by simp)
  have hh' : AnalyticAt ℂ (fun y ↦ h (y - p)) p := hh.comp_of_eq hsubA (by simp)
  have hfac' : P =ᶠ[nhds p] fun y ↦ g (y - p) * h (y - p) := by
    have := hfac.comp_tendsto hsub
    simpa [Function.comp_def, add_comm] using this
  rcases hirr.2 _ _ hg' hh' hfac' with hg0 | hh0
  · left
    simpa using hg0
  · right
    simpa using hh0

private theorem isCoprimeAt_translate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {P Q : E → ℂ} {p : E} (hcop : IsCoprimeAt P Q p) :
    IsCoprimeAt (fun z ↦ P (p + z)) (fun z ↦ Q (p + z)) 0 := by
  rintro ⟨q, r, s, hq, hr, hs, hq0, hPr, hQs⟩
  apply hcop
  have hsubA : AnalyticAt ℂ (fun y : E ↦ y - p) p := analyticAt_id.sub analyticAt_const
  have hsub : Tendsto (fun y : E ↦ y - p) (nhds p) (nhds (0 : E)) := by
    have hc := hsubA.continuousAt
    change Tendsto (fun y : E ↦ y - p) (nhds p) (nhds (p - p)) at hc
    simpa using hc
  refine ⟨fun y ↦ q (y - p), fun y ↦ r (y - p), fun y ↦ s (y - p),
    hq.comp_of_eq hsubA (by simp), hr.comp_of_eq hsubA (by simp),
    hs.comp_of_eq hsubA (by simp), ?_, ?_, ?_⟩
  · simpa using hq0
  · have := hPr.comp_tendsto hsub
    simpa [Function.comp_def, add_comm] using this
  · have := hQs.comp_tendsto hsub
    simpa [Function.comp_def, add_comm] using this

theorem spec_localDivisorAt_multiplicity_eq_transverseOrder_aux {n k : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ} {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    {m : Fin k → ℕ} {p : (Fin n → ℂ) × ℂ} (hf : AnalyticAt ℂ f p) (hf0 : f p = 0)
    (hu : AnalyticAt ℂ u p) (hu0 : u p ≠ 0)
    (hP : ∀ i, AnalyticAt ℂ (P i) p ∧ IsIrreducibleAt (P i) p ∧ 0 < m i)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) p))
    (hfac : f =ᶠ[nhds p] fun y ↦ u y * ∏ i, (P i y) ^ (m i))
    (hPt : ∀ i, AnalyticAt ℂ (fun z ↦ P i (p + z)) 0) :
    ∀ᶠ y in nhds p, ∀ i, P i y = 0 → (∀ j, j ≠ i → P j y ≠ 0) →
      ∀ a : (Fin n → ℂ) × ℂ, fderiv ℂ (P i) y a ≠ 0 →
        analyticOrderAt (fun t : ℂ ↦ f (y + t • a)) 0 =
          localDivisorAt n f p
            (Associates.mk (productAnalyticGermOf (fun z ↦ P i (p + z)) (hPt i))) := by
  let F := fun z ↦ f (p + z)
  let U := fun z ↦ u (p + z)
  let Q := fun i z ↦ P i (p + z)
  have hF : AnalyticAt ℂ F 0 := hf.comp_of_eq (by fun_prop) (by simp [F])
  have hU : AnalyticAt ℂ U 0 := hu.comp_of_eq (by fun_prop) (by simp [U])
  have hU0 : U 0 ≠ 0 := by simpa [U] using hu0
  have hQ : ∀ i, AnalyticAt ℂ (Q i) 0 ∧ IsIrreducibleAt (Q i) 0 ∧ 0 < m i := by
    intro i
    exact ⟨hPt i, isIrreducibleAt_translate (hP i).2.1, (hP i).2.2⟩
  have hcQ : Pairwise (fun i j ↦ IsCoprimeAt (Q i) (Q j) 0) := by
    intro i j hij
    exact isCoprimeAt_translate (hcP hij)
  have hfacQ : F =ᶠ[nhds 0] fun z ↦ U z * ∏ i, (Q i z) ^ (m i) := by
    have hadd : Tendsto (fun z ↦ p + z) (nhds 0) (nhds p) := by
      have hc : ContinuousAt (fun z ↦ p + z) 0 := continuousAt_const.add continuousAt_id
      change Tendsto (fun z ↦ p + z) (nhds 0) (nhds (p + 0)) at hc
      simpa using hc
    have := hfac.comp_tendsto hadd
    simpa [F, U, Q, Function.comp_def] using this
  have horder := spec_localDivisor_multiplicity_eq_transverseOrder hF hU hU0 hQ hcQ hfacQ
  have hsub : Tendsto (fun y ↦ y - p) (nhds p) (nhds 0) := by
    have hc : ContinuousAt (fun y ↦ y - p) p := continuousAt_id.sub continuousAt_const
    change Tendsto (fun y ↦ y - p) (nhds p) (nhds (p - p)) at hc
    simpa using hc
  have hpull := hsub.eventually horder
  filter_upwards [hpull] with y hy
  intro i hPiy hother a hder
  have hy' := hy i (by simpa [Q] using hPiy)
    (fun j hji ↦ by simpa [Q] using hother j hji) a
  have hder' : fderiv ℂ (Q i) (y - p) a ≠ 0 := by
    rw [show Q i = fun z ↦ P i (p + z) by rfl, fderiv_comp_add_left]
    simpa [add_comm] using hder
  have := hy' hder'
  have hFt : AnalyticAt ℂ (fun z ↦ f (p + z)) 0 := by simpa [F] using hF
  have hdiv : localDivisorAt n f p = localDivisor n (productAnalyticGermOf F hF) := by
    simp only [localDivisorAt, hFt, ↓reduceDIte]
    congr 2
  change analyticOrderAt (fun t : ℂ ↦ f (y + t • a)) 0 =
    localDivisorAt n f p
      (Associates.mk (productAnalyticGermOf (fun z ↦ P i (p + z)) (hPt i)))
  rw [hdiv]
  change analyticOrderAt (fun t : ℂ ↦ f (y + t • a)) 0 =
    (localDivisor n (productAnalyticGermOf F hF))
      (Associates.mk (productAnalyticGermOf (Q i) (hQ i).1))
  rw [← this]
  congr 2
  funext t
  simp only [F]
  congr 1
  abel

private theorem localDivisorAt_mul {n : ℕ} {f g : (Fin n → ℂ) × ℂ → ℂ}
    {p : (Fin n → ℂ) × ℂ} (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hfn : ¬ ∀ᶠ y in 𝓝 p, f y = 0) (hgn : ¬ ∀ᶠ y in 𝓝 p, g y = 0) :
    localDivisorAt n (fun y ↦ f y * g y) p =
      localDivisorAt n f p + localDivisorAt n g p := by
  have hs : Tendsto (fun y : (Fin n → ℂ) × ℂ ↦ y - p) (𝓝 p) (𝓝 0) := by
    have hc : Continuous (fun y : (Fin n → ℂ) × ℂ ↦ y - p) := by fun_prop
    simpa using (hc.continuousAt (x := p)).tendsto
  have hadd : AnalyticAt ℂ (fun y : (Fin n → ℂ) × ℂ ↦ p + y) 0 := by fun_prop
  have hft : AnalyticAt ℂ (fun y ↦ f (p + y)) 0 := by
    simpa [Function.comp_def] using hf.comp_of_eq hadd (by simp)
  have hgt : AnalyticAt ℂ (fun y ↦ g (p + y)) 0 := by
    simpa [Function.comp_def] using hg.comp_of_eq hadd (by simp)
  have hfn' : productAnalyticGermOf (fun y ↦ f (p + y)) hft ≠ 0 := by
    intro hz
    have he : ∀ᶠ y in 𝓝 (0 : (Fin n → ℂ) × ℂ), f (p + y) = 0 := by
      change (fun y ↦ f (p + y)) =ᶠ[𝓝 0] (fun _ ↦ 0)
      have hz' := congrArg Subtype.val hz
      let ft : (Fin n → ℂ) × ℂ → ℂ := fun y ↦ f (p + y)
      change (ft : Filter.Germ (𝓝 (0 : (Fin n → ℂ) × ℂ)) ℂ) = 0 at hz'
      exact Germ.coe_eq.mp hz'
    exact hfn (by simpa using hs.eventually he)
  have hgn' : productAnalyticGermOf (fun y ↦ g (p + y)) hgt ≠ 0 := by
    intro hz
    have he : ∀ᶠ y in 𝓝 (0 : (Fin n → ℂ) × ℂ), g (p + y) = 0 := by
      change (fun y ↦ g (p + y)) =ᶠ[𝓝 0] (fun _ ↦ 0)
      have hz' := congrArg Subtype.val hz
      let gt : (Fin n → ℂ) × ℂ → ℂ := fun y ↦ g (p + y)
      change (gt : Filter.Germ (𝓝 (0 : (Fin n → ℂ) × ℂ)) ℂ) = 0 at hz'
      exact Germ.coe_eq.mp hz'
    exact hgn (by simpa using hs.eventually he)
  have hmul : AnalyticAt ℂ (fun y ↦ f (p + y) * g (p + y)) 0 := hft.mul hgt
  simp only [localDivisorAt, dif_pos hft, dif_pos hgt, dif_pos hmul]
  rw [show productAnalyticGermOf (fun y ↦ f (p + y) * g (p + y)) hmul =
      productAnalyticGermOf (fun y ↦ f (p + y)) hft *
        productAnalyticGermOf (fun y ↦ g (p + y)) hgt by rfl]
  exact spec_localDivisor_mul n _ _ hfn' hgn'

/-- Source: Griffiths--Harris, Ch. 1 §1; equivalent valid fractions have equal multiplicities. -/
theorem spec_localMeromorphicDivisorAt_eq_aux {n : ℕ} {ι κ : Type*}
    {V : ι → Set ((Fin n → ℂ) × ℂ)} {g h : ι → (Fin n → ℂ) × ℂ → ℂ}
    {W : κ → Set ((Fin n → ℂ) × ℂ)} {a b : κ → (Fin n → ℂ) × ℂ → ℂ}
    {U : Set ((Fin n → ℂ) × ℂ)}
    (hD : IsLocalMeromorphicDivisorData U V g h)
    (hA : IsLocalMeromorphicDivisorData U W a b)
    (heq : EquivalentLocalMeromorphicDivisorData V g h W a b) (i : ι) (j : κ)
    (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) (hj : p ∈ W j)
    (hg : AnalyticAt ℂ (g i) p) (hh : AnalyticAt ℂ (h i) p)
    (ha : AnalyticAt ℂ (a j) p) (hb : AnalyticAt ℂ (b j) p) :
    localMeromorphicDivisorAt n (g i) (h i) p =
      localMeromorphicDivisorAt n (a j) (b j) p := by
  have hgb := localDivisorAt_mul hg hb (hD.2.2.2.2.1 i p hi) (hA.2.2.2.2.2.1 j p hj)
  have hah := localDivisorAt_mul ha hh (hA.2.2.2.2.1 j p hj) (hD.2.2.2.2.2.1 i p hi)
  have hcross := spec_localDivisorAt_eq_of_areAssociatedAt (hg.mul hb) (ha.mul hh)
    (heq i j p ⟨hi, hj⟩)
  change localDivisorAt n (fun y ↦ g i y * b j y) p =
    localDivisorAt n (fun y ↦ a j y * h i y) p at hcross
  rw [hgb, hah] at hcross
  ext c
  have hc := congrArg (fun D ↦ D c) hcross
  simp only [localMeromorphicDivisorAt, Finsupp.sub_apply, Finsupp.mapRange_apply,
    Finsupp.add_apply] at hc ⊢
  omega

/-- Source: Griffiths--Harris, Ch. 1 §1; a unit denominator contributes zero. -/
theorem spec_localMeromorphicDivisorAt_unit_denominator_aux {n : ℕ}
    {g h : (Fin n → ℂ) × ℂ → ℂ} {p : (Fin n → ℂ) × ℂ}
    (hh : AnalyticAt ℂ h p) (hh0 : h p ≠ 0) :
    localMeromorphicDivisorAt n g h p =
      (localDivisorAt n g p).mapRange Nat.cast (by simp) := by
  rw [localMeromorphicDivisorAt,
    spec_localDivisorAt_eq_zero_of_ne_zero hh hh0]
  simp

/-- Source: Griffiths--Harris, Ch. 1 §1; identical numerator and denominator give zero. -/
theorem spec_localMeromorphicDivisorAt_self_aux {n : ℕ}
    (g : (Fin n → ℂ) × ℂ → ℂ) (p : (Fin n → ℂ) × ℂ) :
    localMeromorphicDivisorAt n g g p = 0 := by
  exact sub_self _

/-- Source: the zero cross-product degeneration excluded by validity of meromorphic data. -/
theorem spec_zeroCrossProduct_counterexample_aux :
    EquivalentLocalMeromorphicDivisorData
        (fun _ : Unit ↦ (univ : Set ((Fin 0 → ℂ) × ℂ)))
        (fun _ _ ↦ 0) (fun _ _ ↦ 0)
        (fun _ : Unit ↦ univ) (fun _ z ↦ z.2) (fun _ _ ↦ 1) ∧
      localMeromorphicDivisorAt 0 (fun _ ↦ 0) (fun _ ↦ 0) 0 ≠
        localMeromorphicDivisorAt 0 (fun z ↦ z.2) (fun _ ↦ 1) 0 := by
  constructor
  · intro i j x hx
    refine ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, ?_⟩
    exact Eventually.of_forall fun y ↦ by simp
  · rw [spec_localMeromorphicDivisorAt_self_aux,
      spec_localMeromorphicDivisorAt_unit_denominator_aux analyticAt_const one_ne_zero]
    intro hz
    let W := productAnalyticGermOf (fun y : (Fin 0 → ℂ) × ℂ ↦ y.2) analyticAt_snd
    have hd : localDivisorAt 0 (fun y : (Fin 0 → ℂ) × ℂ ↦ y.2) 0 = 0 := by
      ext c
      have hc := congrArg (fun D ↦ D c) hz
      simp only [Finsupp.zero_apply, Finsupp.mapRange_apply] at hc
      exact_mod_cast hc.symm
    have hW : localDivisor 0 W = 0 := by
      have ht : AnalyticAt ℂ (fun y : (Fin 0 → ℂ) × ℂ ↦ (0 + y).2) 0 := by
        simpa using analyticAt_snd
      simp only [localDivisorAt, dif_pos ht] at hd
      simpa [W] using hd
    have hpow := spec_localDivisor_pow 0 W 3
    rw [hW, smul_zero] at hpow
    have hexp := spec_localDivisor_zero_base_w_pow
    rw [show productAnalyticGermOf (fun y : (Fin 0 → ℂ) × ℂ ↦ y.2 ^ 3)
        (analyticAt_snd.pow 3) = W ^ 3 by rfl, hpow] at hexp
    have hc := congrArg (fun D ↦ D (Associates.mk W)) hexp
    dsimp [W] at hc
    simp at hc

end HodgeLean.Foundations.AnalyticDivisorAlgebraic15
