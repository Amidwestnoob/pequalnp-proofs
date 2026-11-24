import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1646 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (U : Finset (Sym2 (Fin n))), (∀ e ∈ U, e ∈ G.edgeSet) → ∀ (x : Fin n) (Y : Finset (Fin n)), (∀ y ∈ Y, s(x, y) ∈ U) → ∀ (R : Finset (Fin n)) (π : Finset (Finset (Fin n))), (∀ B ∈ π, B ⊆ R ∧ (B.card = 1 ∨ (2 ≤ B.card ∧ ∃ c : Fin n, (∀ b ∈ B, G.Adj c b) ∧ ∀ b' ∈ B, s(c, b') ∉ U))) → (∀ r ∈ R, ∃ B' ∈ π, r ∈ B') → (R ∩ Y).card ≤ π.card ∧ ((∀ v ∈ R, G.Adj x v) → ¬ R ⊆ Y → (R ∩ Y).card + 1 ≤ π.card) := by
  classical
  intro n G _ hG U hU x Y hY R π hblocks hcover
  have hxy : ∀ y ∈ Y, G.Adj x y := by
    intro y hy
    exact (SimpleGraph.mem_edgeSet G).mp (hU _ (hY y hy))
  have hcommon : ∀ c : Fin n, x ≠ c → ∀ a b : Fin n,
      G.Adj x a → G.Adj c a → G.Adj x b → G.Adj c b → a = b := by
    intro c hxc a b hxa hca hxb hcb
    exact Finset.card_le_one.mp (hG x c hxc) a
      (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hxa, hca⟩)
      b (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hxb, hcb⟩)
  have hblock_unique : ∀ B ∈ π, ∀ a ∈ B, ∀ b ∈ B,
      a ∈ Y → b ∈ Y → a = b := by
    intro B hB a ha b hb hay hby
    rcases (hblocks B hB).2 with hs | ⟨_, c, hc, hoff⟩
    · exact Finset.card_le_one.mp (by omega) a ha b hb
    · have hxc : x ≠ c := by
        intro heq
        exact hoff a ha (by rw [← heq]; exact hY a hay)
      exact hcommon c hxc a b (hxy a hay) (hc a ha) (hxy b hby) (hc b hb)
  let f : Fin n → Finset (Fin n) := fun r =>
    if hr : r ∈ R then Classical.choose (hcover r hr) else ∅
  have hf : ∀ r ∈ R, f r ∈ π ∧ r ∈ f r := by
    intro r hr
    dsimp only [f]
    rw [dite_eq_left hr]
    exact Classical.choose_spec (hcover r hr)
  have hinj : Set.InjOn f (↑(R ∩ Y) : Set (Fin n)) := by
    intro a ha b hb heq
    rcases Finset.mem_inter.mp ha with ⟨haR, haY⟩
    rcases Finset.mem_inter.mp hb with ⟨hbR, hbY⟩
    exact hblock_unique (f a) (hf a haR).1 a (hf a haR).2 b
      (by rw [heq]; exact (hf b hbR).2) haY hbY
  constructor
  · exact Finset.card_le_card_of_injOn f
      (fun r hr => (hf r (Finset.mem_inter.mp hr).1).1) hinj
  · intro hR hnot
    have hex : ∃ r ∈ R, r ∉ Y := by
      by_contra h
      apply hnot
      intro r hr
      by_contra hry
      exact h ⟨r, hr, hry⟩
    obtain ⟨r, hr, hry⟩ := hex
    obtain ⟨B, hB, hrB⟩ := hcover r hr
    have hBY : ∀ y ∈ B, y ∉ Y := by
      intro y hy hyY
      rcases (hblocks B hB).2 with hs | ⟨hsize, c, hc, hoff⟩
      · have hEq : r = y := Finset.card_le_one.mp (by omega) r hrB y hy
        exact hry (hEq ▸ hyY)
      · have hxc : x ≠ c := by
          intro heq
          exact hoff y hy (by rw [← heq]; exact hY y hyY)
        have hsmall : B.card ≤ 1 := Finset.card_le_one.mpr (by
          intro a ha b hb
          exact hcommon c hxc a b (hR a ((hblocks B hB).1 ha)) (hc a ha)
            (hR b ((hblocks B hB).1 hb)) (hc b hb))
        omega
    have hcard : (R ∩ Y).card ≤ (π.erase B).card := by
      apply Finset.card_le_card_of_injOn f _ hinj
      intro y hy
      rcases Finset.mem_inter.mp hy with ⟨hyR, hyY⟩
      apply Finset.mem_erase.mpr
      refine ⟨?_, (hf y hyR).1⟩
      intro heq
      exact hBY y (by rw [← heq]; exact (hf y hyR).2) hyY
    have herase := Finset.card_erase_add_one hB
    omega
