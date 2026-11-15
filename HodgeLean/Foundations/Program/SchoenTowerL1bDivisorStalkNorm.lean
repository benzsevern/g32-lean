import HodgeLean.Foundations.Program.SchoenTowerL1bTransportDvrOrder

noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The norm of a uniformizer is invariant and has order equal to the acting group's size. -/
theorem s2v_l1b_divisor_stalk_norm
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    (G : Type*) [Group G] [Fintype G] (ρ : G →* (R ≃+* R))
    (ι : R →+* PowerSeries K) (hX : ∃ t : R, ι t = PowerSeries.X)
    (p : R) (hp : Irreducible p) :
    ∃ v : R, (∀ g, ρ g v = v) ∧ (ι v).order = Fintype.card G := by
  classical
  refine ⟨∏ g : G, ρ g p, ?_, ?_⟩
  · intro g
    simp only [map_prod]
    have H := Equiv.prod_comp (Equiv.mulLeft g) (fun h : G => ρ h p)
    change (∏ h : G, ρ (g * h) p) = _ at H
    calc
      _ = ∏ h : G, ρ (g * h) p := by
        apply Finset.prod_congr rfl
        intro h _
        rw [map_mul]
        rfl
      _ = _ := H
  · rw [map_prod, PowerSeries.order_prod]
    have ho (g : G) : (ι (ρ g p)).order = 1 :=
      s2v_l1b_transport_uniformizer_order ι hX (hp.map (ρ g).toMulEquiv)
    simp only [ho, Finset.sum_const, Finset.card_univ, nsmul_one]

end HodgeLean.Foundations.Program
