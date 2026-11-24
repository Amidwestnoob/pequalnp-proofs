import Mathlib
import PEqualNP.Defs

-- Support argument adapted from willakone, checked L-meta-2074, PR4298.
namespace PEqualNP.Outside.L_meta_4596

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover


def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma dep (n : ℕ) (C : Circuit) (hR : ∀ j < C.gates.length, (gateAt C j).inputs.length = 2) :
    ∀ k, k ≤ C.gates.length → ∀ W : Finset ℕ, (∀ w ∈ W, w < n + k) →
      ∃ T : Finset (Fin n), T.card ≤ k + W.card ∧
        ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
          ∀ w ∈ W, val C (List.ofFn x) w = val C (List.ofFn y) w := by
  intro k
  induction k with
  | zero =>
    intro _ W hW
    refine ⟨Finset.univ.filter (fun i : Fin n => (i : ℕ) ∈ W), ?_, ?_⟩
    · rw [Nat.zero_add, ← Finset.card_image_of_injective _ Fin.val_injective]
      apply Finset.card_le_card
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
      exact (Finset.mem_filter.1 hi).2
    · intro x y h w hw
      have hw' : w < n := by simpa using hW w hw
      have e : ∀ z : Fin n → Bool, (List.ofFn z).getD w false = z ⟨w, hw'⟩ := by
        intro z; simp [List.getD_eq_getElem?_getD, hw']
      rw [val_input (by simp) hw', val_input (by simp) hw', e, e]
      exact h ⟨w, hw'⟩ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw⟩)
  | succ k ih =>
    intro hk W hW
    by_cases hmem : n + k ∈ W
    · obtain ⟨W2, hW2⟩ : ∃ W2 : Finset ℕ, W2 = W.erase (n + k) ∪
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset := ⟨_, rfl⟩
      have hlt2 : ∀ w ∈ W2, w < n + k := by
        intro w hw
        rw [hW2] at hw
        rcases Finset.mem_union.1 hw with h | h
        · have h1 := hW w (Finset.mem_of_mem_erase h)
          have h2 := Finset.ne_of_mem_erase h
          omega
        · simp at h; exact h.2
      have hs1 : ∀ w ∈ W, w ≠ n + k → w ∈ W2 := by
        intro w hw hne
        rw [hW2]
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hne, hw⟩)
      have hs2 : ∀ i ∈ (gateAt C k).inputs, i < n + k → i ∈ W2 := by
        intro i hi hlt
        rw [hW2]
        exact Finset.mem_union_right _ (by simp [hi, hlt])
      have hc : W2.card + 1 ≤ W.card + 2 := by
        rw [hW2]
        have h1 := Finset.card_union_le (W.erase (n + k))
          ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset
        have h2 : ((gateAt C k).inputs.filter (fun i => i < n + k)).toFinset.card ≤ 2 :=
          (List.toFinset_card_le _).trans
            ((List.length_filter_le _ _).trans (hR k (by omega)).le)
        have h3 := Finset.card_erase_of_mem hmem
        have h4 : 0 < W.card := Finset.card_pos.2 ⟨_, hmem⟩
        omega
      obtain ⟨T, hT, hdep⟩ := ih (by omega) W2 hlt2
      refine ⟨T, by omega, ?_⟩
      intro x y h w hw
      by_cases hwk : w = n + k
      · rw [hwk, val_gate (by simp) (by omega), val_gate (by simp) (by omega)]
        congr 1
        apply List.map_congr_left
        intro i hi
        by_cases hlt : i < n + k
        · simp only [ite_eq_left hlt]
          exact hdep x y h i (hs2 i hi hlt)
        · simp only [ite_eq_right hlt]
      · exact hdep x y h w (hs1 w hw hwk)
    · obtain ⟨T, hT, hdep⟩ := ih (by omega) W (by
        intro w hw
        have h1 := hW w hw
        have h2 : w ≠ n + k := fun h => hmem (h ▸ hw)
        omega)
      exact ⟨T, by omega, hdep⟩


lemma support (n : ℕ) (C : Circuit) (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) :
    ∃ T : Finset (Fin n), T.card ≤ C.size + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ T, x i = y i) →
        PEqualNP.MetaComplexity.circuitFun n C x = PEqualNP.MetaComplexity.circuitFun n C y := by
  by_cases ho : C.output < n + C.gates.length
  · obtain ⟨T, hT, hdep⟩ := dep n C (fun j hj => h2 _ (gateAt_mem hj)) C.gates.length le_rfl
      {C.output} (by simpa using ho)
    exact ⟨T, by simpa [Circuit.size] using hT, fun x y h => hdep x y h _ (by simp)⟩
  · exact ⟨∅, by simp, fun x y _ => by
      change val C (List.ofFn x) C.output = val C (List.ofFn y) C.output
      rw [val_ge (n := n) (by simp) (by omega), val_ge (n := n) (by simp) (by omega)]⟩

lemma endpoints (q N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (E : Finset (Fin N × Fin N)) (hq : 1 ≤ q)
    (h2 : PEqualNP.TopForm.IsAO2 (N+N) C)
    (hs : ∀ z : Fin (N+N) → Bool,
      Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      PEqualNP.MetaComplexity.circuitFun (N+N) C z = false)
    (he : ∀ e ∈ E, I e.1 e.2 ∧
      PEqualNP.MetaComplexity.circuitFun (N+N) C
        (fun k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2)) = true) :
    (E.image Prod.fst).card + (E.image Prod.snd).card ≤ C.size + 1 := by
  classical
  obtain ⟨T, hT, hdep⟩ := support (N+N) C h2.2.2
  have disj (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro h; have := congrArg Fin.val h; simp at this; omega
  have singleP (p : Fin N) : PEqualNP.MetaComplexity.circuitFun (N+N) C
      (fun k => decide (k = Fin.castAdd N p)) = false := by
    apply hs
    · have hz : Fintype.card {l : Fin N // decide (Fin.natAdd N l = Fin.castAdd N p) = true} = 0 := by
        letI : IsEmpty {l : Fin N // decide (Fin.natAdd N l = Fin.castAdd N p) = true} :=
          ⟨fun x => disj p x.1 (of_decide_eq_true x.2).symm⟩
        exact Fintype.card_eq_zero
      rw [hz]; omega
    · rintro ⟨a,b,_,_,hb⟩
      exact disj p b (of_decide_eq_true hb).symm
  have singleL (l : Fin N) : PEqualNP.MetaComplexity.circuitFun (N+N) C
      (fun k => decide (k = Fin.natAdd N l)) = false := by
    apply hs
    · have hz : Fintype.card {b : Fin N // decide (Fin.natAdd N b = Fin.natAdd N l) = true} ≤ 1 := by
        apply Fintype.card_le_one_iff.mpr
        intro a b
        apply Subtype.ext
        have ha := of_decide_eq_true a.2
        have hb := of_decide_eq_true b.2
        exact Fin.natAdd_injective N N (ha.trans hb.symm)
      omega
    · rintro ⟨a,b,_,ha,_⟩
      exact disj a l (of_decide_eq_true ha)
  have hp : ∀ e ∈ E, Fin.castAdd N e.1 ∈ T := by
    intro e heE
    by_contra hn
    have h := hdep (fun k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2))
      (fun k => decide (k = Fin.natAdd N e.2)) (by
        intro i hi
        have hne : i ≠ Fin.castAdd N e.1 := fun eq => hn (eq ▸ hi)
        simp only [hne, false_or])
    rw [(he e heE).2, singleL e.2] at h
    cases h
  have hl : ∀ e ∈ E, Fin.natAdd N e.2 ∈ T := by
    intro e heE
    by_contra hn
    have h := hdep (fun k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2))
      (fun k => decide (k = Fin.castAdd N e.1)) (by
        intro i hi
        have hne : i ≠ Fin.natAdd N e.2 := fun eq => hn (eq ▸ hi)
        simp only [hne, or_false])
    rw [(he e heE).2, singleP e.1] at h
    cases h
  let A := (E.image Prod.fst).image (Fin.castAdd N)
  let B := (E.image Prod.snd).image (Fin.natAdd N)
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨l,_,eq⟩ := Finset.mem_image.mp hj
    exact disj p l eq.symm
  have hsub : A ∪ B ⊆ T := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨p,hpE,rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨e,heE,rfl⟩ := Finset.mem_image.mp hpE
      exact hp e heE
    · obtain ⟨l,hlE,rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨e,heE,rfl⟩ := Finset.mem_image.mp hlE
      exact hl e heE
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hAB] at hc
  have hA : A.card = (E.image Prod.fst).card := Finset.card_image_of_injective _ (Fin.castAdd_injective N N)
  have hB : B.card = (E.image Prod.snd).card := Finset.card_image_of_injective _ (Fin.natAdd_injective N N)
  omega

open Finset


lemma directional_bound {N : Nat} (E : Finset (Fin N × Fin N))
    (hrect : ∀ a b l m, a ≠ b → (a,l) ∈ E → (b,l) ∈ E →
      (a,m) ∈ E → (b,m) ∈ E → l = m) :
    E.card ^ 2 ≤ (E.image Prod.snd).card * ((E.image Prod.fst).card ^ 2 + E.card) := by
  classical
  let P := E.image Prod.fst
  let L := E.image Prod.snd
  let F := fun b => P.filter (fun a => (a,b) ∈ E)
  have hsum : ∑ b ∈ L, (F b).card = E.card := by
    rw [← Finset.card_sigma]
    apply Finset.card_bij (fun x _ => (x.2, x.1))
    · intro x hx
      exact (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2
    · rintro ⟨b,a⟩ _ ⟨d,c⟩ _ h
      simpa only [Prod.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, and_comm] using h
    · rintro ⟨a,b⟩ hab
      refine ⟨⟨b,a⟩, ?_, rfl⟩
      simp only [Finset.mem_sigma, F, Finset.mem_filter]
      exact ⟨Finset.mem_image.mpr ⟨(a,b), hab, rfl⟩,
        Finset.mem_image.mpr ⟨(a,b), hab, rfl⟩, hab⟩
  have hsq : ∑ b ∈ L, (F b).card ^ 2 ≤ P.card ^ 2 + E.card := by
    let T := L.sigma (fun b => (F b) ×ˢ (F b))
    let f : (Σ _ : Fin N, Fin N × Fin N) → (Fin N × Fin N) ⊕ (Fin N × Fin N) :=
      fun x => if x.2.1 = x.2.2 then Sum.inr (x.2.1, x.1) else Sum.inl x.2
    have hmap : Set.MapsTo f T ((P ×ˢ P).disjSum E) := by
      rintro ⟨b,a,c⟩ hx
      obtain ⟨_, hpair⟩ := Finset.mem_sigma.mp hx
      obtain ⟨ha, hc⟩ := Finset.mem_product.mp hpair
      obtain ⟨haP, haE⟩ := Finset.mem_filter.mp ha
      obtain ⟨hcP, hcE⟩ := Finset.mem_filter.mp hc
      by_cases hac : a = c
      · simpa [f, hac] using haE
      · simpa [f, hac] using And.intro haP hcP
    have hinj : (T : Set (Σ _ : Fin N, Fin N × Fin N)).InjOn f := by
      rintro ⟨l,a,b⟩ hx ⟨m,c,d⟩ hy heq
      obtain ⟨_, hxpair⟩ := Finset.mem_sigma.mp hx
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hxpair
      obtain ⟨_, hypair⟩ := Finset.mem_sigma.mp hy
      obtain ⟨hc, hd⟩ := Finset.mem_product.mp hypair
      have haE := (Finset.mem_filter.mp ha).2
      have hbE := (Finset.mem_filter.mp hb).2
      have hcE := (Finset.mem_filter.mp hc).2
      have hdE := (Finset.mem_filter.mp hd).2
      by_cases hab : a = b <;> by_cases hcd : c = d
      · simp only [f, hab, hcd, ite_true, Sum.inr.injEq, Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        simp_all
      · simp [f, hab, hcd] at heq
      · simp [f, hab, hcd] at heq
      · simp only [f, hab, hcd, ite_false, Sum.inl.injEq, Prod.mk.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        have hlm := hrect a b l m hab haE hbE hcE hdE
        subst m; rfl
    have hcard := Finset.card_le_card_of_injOn f hmap hinj
    simpa [T, Finset.card_sigma, Finset.card_product, Finset.card_disjSum, pow_two] using hcard
  have hcs := sq_sum_le_card_mul_sum_sq (s := L) (f := fun b => (F b).card)
  rw [hsum] at hcs
  exact hcs.trans (Nat.mul_le_mul_left _ hsq)


lemma reverse_directional_bound {N : Nat} (E : Finset (Fin N × Fin N))
    (hrect : ∀ a b l m, a ≠ b → (a,l) ∈ E → (b,l) ∈ E →
      (a,m) ∈ E → (b,m) ∈ E → l = m) :
    E.card ^ 2 ≤ (E.image Prod.fst).card * ((E.image Prod.snd).card ^ 2 + E.card) := by
  classical
  have hs : ∀ a b, (a,b) ∈ E.image Prod.swap ↔ (b,a) ∈ E := by
    intro a b
    simp only [Finset.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
    aesop
  have hr : ∀ a b l m, a ≠ b → (a,l) ∈ E.image Prod.swap →
      (b,l) ∈ E.image Prod.swap → (a,m) ∈ E.image Prod.swap →
      (b,m) ∈ E.image Prod.swap → l = m := by
    intro a b l m hab hal hbl ham hbm
    by_contra hlm
    exact hab (hrect l m a b hlm (hs a l |>.mp hal) (hs a m |>.mp ham)
      (hs b l |>.mp hbl) (hs b m |>.mp hbm))
  have h := directional_bound (E.image Prod.swap) hr
  have hc : (E.image Prod.swap).card = E.card :=
    Finset.card_image_of_injective E Prod.swap_injective
  simpa only [hc, Finset.image_image, Function.comp_def, Prod.fst_swap, Prod.snd_swap] using h

lemma cubic_of_directional {p l e : ℝ} (hp : 0 ≤ p) (hl : 0 ≤ l) (he : 0 ≤ e)
    (hpl : p ≤ l) (h : e^2 ≤ l * (p^2 + e)) :
    8*e^2 ≤ 8*(p+l)*e + (p+l)^3 := by
  have hv : 0 ≤ p+l := by positivity
  have hfour : 4*p*l ≤ (p+l)^2 := by nlinarith [sq_nonneg (p-l)]
  have htwo : 2*p ≤ p+l := by linarith
  have hA := mul_le_mul_of_nonneg_right hfour hv
  have hB := mul_le_mul_of_nonneg_right htwo (show 0 ≤ 4*p*l by positivity)
  have hc : 8*p^2*l ≤ (p+l)^3 := by nlinarith
  nlinarith [mul_nonneg hp he]


lemma numerical_bound {p l e s : ℝ}
    (hp : 0 ≤ p) (hl : 0 ≤ l) (he : 0 ≤ e)
    (hs : 1 ≤ s) (hsmax : s ≤ 4400) (hv : p+l ≤ s+1)
    (hprod : e ≤ p*l)
    (hfirst : e^2 ≤ l*(p^2+e)) (hsecond : e^2 ≤ p*(l^2+e)) :
    e ≤ 24*s := by
  have hv0 : 0 ≤ p+l := by positivity
  have hfour : 4*p*l ≤ (p+l)^2 := by nlinarith [sq_nonneg (p-l)]
  have hvsq : (p+l)^2 ≤ (s+1)^2 := pow_le_pow_left₀ hv0 hv 2
  by_cases hsmall : s ≤ 16
  · have hmul := mul_nonneg (show 0 ≤ s+1 by linarith) (show 0 ≤ 17-(s+1) by linarith)
    nlinarith
  have hs16 : 16 < s := lt_of_not_ge hsmall
  have hcubic : 8*e^2 ≤ 8*(p+l)*e + (p+l)^3 := by
    rcases le_total p l with hpl | hlp
    · exact cubic_of_directional hp hl he hpl hfirst
    · simpa [add_comm] using cubic_of_directional hl hp he hlp hsecond
  have hvcube : (p+l)^3 ≤ (s+1)^3 := pow_le_pow_left₀ hv0 hv 3
  have hve := mul_le_mul_of_nonneg_right hv he
  have hpoly : 8*e^2 ≤ 8*(s+1)*e + (s+1)^3 := by nlinarith
  by_contra hbad
  have het : 24*s ≤ e := le_of_lt (lt_of_not_ge hbad)
  have hmon := mul_nonneg (sub_nonneg.mpr het)
    (show 0 ≤ e+24*s-(s+1) by linarith)
  have htop := mul_nonneg (sub_nonneg.mpr hsmax) (sq_nonneg s)
  have hlow := mul_nonneg (show 0 ≤ s-16 by linarith) (show 0 ≤ s by linarith)
  nlinarith


lemma counting_bound {N : Nat} (E : Finset (Fin N × Fin N)) (s : Nat)
    (hsupport : (E.image Prod.fst).card + (E.image Prod.snd).card ≤ s+1)
    (hsmax : s ≤ 4400)
    (hrect : ∀ a b l m, a ≠ b → (a,l) ∈ E → (b,l) ∈ E →
      (a,m) ∈ E → (b,m) ∈ E → l = m) : E.card ≤ 24*s := by
  classical
  have hprod : E.card ≤ (E.image Prod.fst).card * (E.image Prod.snd).card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
  by_cases hs : s = 0
  · subst s
    have : (E.image Prod.fst).card = 0 ∨ (E.image Prod.snd).card = 0 := by omega
    rcases this with h | h <;> simp_all
  have hspos : 1 ≤ s := by omega
  have hfirst := directional_bound E hrect
  have hsecond := reverse_directional_bound E hrect
  have hreal := numerical_bound
    (p := ((E.image Prod.fst).card : ℝ)) (l := ((E.image Prod.snd).card : ℝ))
    (e := (E.card : ℝ)) (s := (s : ℝ))
    (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast hspos) (by exact_mod_cast hsmax) (by exact_mod_cast hsupport)
    (by exact_mod_cast hprod) (by exact_mod_cast hfirst) (by exact_mod_cast hsecond)
  exact_mod_cast hreal


end PEqualNP.Outside.L_meta_4596

theorem PEqualNP.Outside.L_meta_4596 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset (Fin x2 × Fin x2)), (1 : ℕ) ≤ x1 → (∀ (x7 x8 : Fin x2), x7 ≠ x8 → ∃! x10 : Fin x2, x3 x7 x10 ∧ x3 x8 x10) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → (∀ (x9 : Fin (x2 + x2) → Bool), Fintype.card { x10 : Fin x2 // x9 (Fin.natAdd x2 x10) = Bool.true } ≤ x1 → (¬∃ (x11 : Fin x2) (x12 : Fin x2), x3 x11 x12 ∧ x9 (Fin.castAdd x2 x11) = Bool.true ∧ x9 (Fin.natAdd x2 x12) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x4 x9 = Bool.false) → (∀ x10 ∈ x5, x3 x10.1 x10.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x4 fun (x12 : Fin (x2 + x2)) => Decidable.decide (x12 = Fin.castAdd x2 x10.1 ∨ x12 = Fin.natAdd x2 x10.2)) = Bool.true) → x4.size ≤ (4400 : ℕ) → x5.card ≤ (24 : ℕ) * x4.size := by
  intro q N I C E hq hI hC hs he hsize
  apply PEqualNP.Outside.L_meta_4596.counting_bound E C.size
    (PEqualNP.Outside.L_meta_4596.endpoints q N I C E hq hC hs he) hsize
  intro a b l m hab hal hbl ham hbm
  obtain ⟨k, hk, hu⟩ := hI a b hab
  exact (hu l ⟨(he (a,l) hal).1, (he (b,l) hbl).1⟩).trans
    (hu m ⟨(he (a,m) ham).1, (he (b,m) hbm).1⟩).symm
