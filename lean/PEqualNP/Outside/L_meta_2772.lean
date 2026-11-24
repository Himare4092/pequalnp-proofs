import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2772

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

private def wstep (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

private theorem wires_eq (C : Circuit) (xs : List Bool) :
    C.wires xs = C.gates.foldl wstep xs := rfl

private theorem foldl_wstep_length (gs : List Gate) (ws : List Bool) :
    (gs.foldl wstep ws).length = ws.length + gs.length := by
  induction gs generalizing ws with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [wstep]
    omega

private theorem foldl_wstep_getD_lt (gs : List Gate) (ws : List Bool) (i : ℕ) (hi : i < ws.length) :
    (gs.foldl wstep ws).getD i false = ws.getD i false := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [wstep]; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem val_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  rw [wires_eq, foldl_wstep_getD_lt _ _ _ (by simp [hi])]
  simp [List.getD_eq_getElem?_getD, hi]

private theorem val_oob (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ)
    (hi : n + C.gates.length ≤ i) :
    (C.wires (List.ofFn x)).getD i false = false := by
  rw [wires_eq]
  apply List.getD_eq_default
  rw [foldl_wstep_length, List.length_ofFn]
  exact hi

private theorem val_gate (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (x : Fin n → Bool)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    simp [List.take_append_drop]
  let front := (C.gates.take j).foldl wstep (List.ofFn x)
  have hflen : front.length = n + j := by
    simp [front, foldl_wstep_length, List.length_take, Nat.min_eq_left hj.le]
  have hfold : C.wires (List.ofFn x) =
      (C.gates.drop (j + 1)).foldl wstep (wstep front C.gates[j]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  have hself : (C.wires (List.ofFn x)).getD (n + j) false =
      (wstep front C.gates[j]).getD (n + j) false := by
    rw [hfold, foldl_wstep_getD_lt]
    simp [wstep, hflen]
  have hprev : ∀ i < n + j, (C.wires (List.ofFn x)).getD i false = front.getD i false := by
    intro i hi
    rw [hfold, foldl_wstep_getD_lt _ _ _ (by simp [wstep, hflen]; omega)]
    exact List.getD_append _ _ _ _ (by omega)
  rw [hself]
  simp only [wstep]
  rw [List.getD_append_right _ _ _ _ (by omega), hflen, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hgd : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hi' : i ∈ (gateAt C j).inputs := by simpa only [hgd] using hi
  exact (hprev i (hRB j hj i hi')).symm

private def modC (C : Circuit) (g b w' : ℕ) : Circuit :=
  ⟨C.gates.set g ⟨(gateAt C g).op, (gateAt C g).inputs.set b w'⟩, C.output⟩

private theorem modC_getElem_ne (C : Circuit) (g b w' j : ℕ) (hne : j ≠ g)
    (hj' : j < (modC C g b w').gates.length) (hj : j < C.gates.length) :
    (modC C g b w').gates[j]'hj' = C.gates[j]'hj :=
  List.getElem_set_ne (Ne.symm hne) hj'

private theorem modC_isAO2 (n : ℕ) (C : Circuit) (g b w' : ℕ)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hw' : w' < n + g) :
    IsAO2 n (modC C g b w') := by
  have hgd : gateAt C g = C.gates[g] := List.getD_eq_getElem _ _ hg
  have hmem : gateAt C g ∈ C.gates := by rw [hgd]; exact List.getElem_mem hg
  refine ⟨?_, ?_, ?_⟩
  · intro h hh
    rcases List.mem_or_eq_of_mem_set hh with hh' | hh'
    · exact hAO.1 h hh'
    · rw [hh']
      exact hAO.1 (gateAt C g) hmem
  · intro j hj i hi
    have hj' : j < C.gates.length := by simpa [modC] using hj
    have hg'_eq : gateAt (modC C g b w') j = (modC C g b w').gates[j] :=
      List.getD_eq_getElem _ _ hj
    rw [hg'_eq] at hi
    by_cases hjg : j = g
    · subst hjg
      have hset : (modC C j b w').gates[j] = ⟨(gateAt C j).op, (gateAt C j).inputs.set b w'⟩ := by
        simp [modC]
      rw [hset] at hi
      rcases List.mem_or_eq_of_mem_set hi with hi' | hi'
      · exact hAO.2.1 j hg i hi'
      · rw [hi']; exact hw'
    · have hne : (modC C g b w').gates[j] = C.gates[j] :=
        modC_getElem_ne C g b w' j hjg hj hj'
      rw [hne] at hi
      have hgdj : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj'
      exact hAO.2.1 j hj' i (hgdj.symm ▸ hi)
  · intro h hh
    rcases List.mem_or_eq_of_mem_set hh with hh' | hh'
    · exact hAO.2.2 h hh'
    · rw [hh']; simp [hAO.2.2 _ hmem]

private theorem val_modC_lt (n : ℕ) (C : Circuit) (g b w' : ℕ)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hw' : w' < n + g)
    (x : Fin n → Bool) :
    ∀ k < n + g,
      ((modC C g b w').wires (List.ofFn x)).getD k false = (C.wires (List.ofFn x)).getD k false := by
  have hAO' := modC_isAO2 n C g b w' hAO hg hw'
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk
    by_cases hkn : k < n
    · rw [val_input n (modC C g b w') x k hkn, val_input n C x k hkn]
    · obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
      have hjg : j < g := by omega
      have hj : j < C.gates.length := hjg.trans hg
      have hj' : j < (modC C g b w').gates.length := by simpa [modC] using hj
      rw [val_gate n (modC C g b w') hAO'.2.1 x j hj', val_gate n C hAO.2.1 x j hj]
      have heq : (modC C g b w').gates[j] = C.gates[j] :=
        modC_getElem_ne C g b w' j (Nat.ne_of_lt hjg) hj' hj
      rw [heq]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hgdj : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
      have hi_lt : i < n + j := hAO.2.1 j hj i (hgdj.symm ▸ hi)
      exact ih i hi_lt (by omega)

private theorem val_modC_eq_of_false (n : ℕ) (C : Circuit) (g b w w' : ℕ)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hb : b < 2)
    (hget : (gateAt C g).inputs.getD b 0 = w) (hw' : w' < n + g) (x : Fin n → Bool)
    (hfw : (C.wires (List.ofFn x)).getD w false = false)
    (hfw' : (C.wires (List.ofFn x)).getD w' false = false) :
    ∀ k, ((modC C g b w').wires (List.ofFn x)).getD k false = (C.wires (List.ofFn x)).getD k false := by
  have hAO' := modC_isAO2 n C g b w' hAO hg hw'
  have hgd : gateAt C g = C.gates[g] := List.getD_eq_getElem _ _ hg
  have hmem : gateAt C g ∈ C.gates := by rw [hgd]; exact List.getElem_mem hg
  obtain ⟨a0, a1, ha⟩ := List.length_eq_two.mp (hAO.2.2 _ hmem)
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases hklt : k < n + g
    · exact val_modC_lt n C g b w' hAO hg hw' x k hklt
    · by_cases hkoob : n + C.gates.length ≤ k
      · have hkoob' : n + (modC C g b w').gates.length ≤ k := by simpa [modC] using hkoob
        rw [val_oob n (modC C g b w') x k hkoob', val_oob n C x k hkoob]
      · obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
        have hj : j < C.gates.length := by omega
        have hj' : j < (modC C g b w').gates.length := by simpa [modC] using hj
        rw [val_gate n (modC C g b w') hAO'.2.1 x j hj', val_gate n C hAO.2.1 x j hj]
        by_cases hjg : j = g
        · subst hjg
          have hset : (modC C j b w').gates[j] = ⟨(gateAt C j).op, (gateAt C j).inputs.set b w'⟩ := by
            simp [modC]
          rw [hset, ← hgd]
          have hw'_mod : ((modC C j b w').wires (List.ofFn x)).getD w' false = false := by
            rw [val_modC_lt n C j b w' hAO hg hw' x w' hw', hfw']
          have ha0_lt : a0 < n + j := hAO.2.1 j hg a0 (by rw [ha]; simp)
          have ha1_lt : a1 < n + j := hAO.2.1 j hg a1 (by rw [ha]; simp)
          have ha0_eq : ((modC C j b w').wires (List.ofFn x)).getD a0 false =
              (C.wires (List.ofFn x)).getD a0 false :=
            val_modC_lt n C j b w' hAO hg hw' x a0 ha0_lt
          have ha1_eq : ((modC C j b w').wires (List.ofFn x)).getD a1 false =
              (C.wires (List.ofFn x)).getD a1 false :=
            val_modC_lt n C j b w' hAO hg hw' x a1 ha1_lt
          have hb01 : b = 0 ∨ b = 1 := by omega
          rcases hb01 with rfl | rfl
          · have rfl_a0 : a0 = w := by simpa [ha] using hget
            subst a0
            simp only [ha, List.set_cons_zero, List.map_cons, List.map_nil]
            rw [hw'_mod, hfw, ha1_eq]
          · have rfl_a1 : a1 = w := by simpa [ha] using hget
            subst a1
            simp only [ha, List.set_cons_succ, List.set_cons_zero, List.map_cons, List.map_nil]
            rw [hw'_mod, hfw, ha0_eq]
        · have heq : (modC C g b w').gates[j] = C.gates[j] :=
            modC_getElem_ne C g b w' j hjg hj' hj
          rw [heq]
          congr 1
          apply List.map_congr_left
          intro i hi
          have hgdj : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
          exact ih i (hAO.2.1 j hj i (hgdj.symm ▸ hi))

private theorem eval_two_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    {u0 u1 v0 v1 : Bool} (h0 : u0 = true → v0 = true) (h1 : u1 = true → v1 = true) :
    op.eval [u0, u1] = true → op.eval [v0, v1] = true := by
  rcases hop with rfl | rfl <;> cases u0 <;> cases u1 <;> simp_all [GateOp.eval]

private theorem val_modC_mono (n : ℕ) (C : Circuit) (g b w w' : ℕ)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hb : b < 2)
    (hget : (gateAt C g).inputs.getD b 0 = w) (hw' : w' < n + g) (x : Fin n → Bool)
    (hup : (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn x)).getD w' false = true) :
    ∀ k, (C.wires (List.ofFn x)).getD k false = true →
      ((modC C g b w').wires (List.ofFn x)).getD k false = true := by
  have hAO' := modC_isAO2 n C g b w' hAO hg hw'
  have hgd : gateAt C g = C.gates[g] := List.getD_eq_getElem _ _ hg
  have hmem : gateAt C g ∈ C.gates := by rw [hgd]; exact List.getElem_mem hg
  obtain ⟨a0, a1, ha⟩ := List.length_eq_two.mp (hAO.2.2 _ hmem)
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro htrue
    by_cases hkn : k < n
    · rw [val_input n C x k hkn] at htrue
      rw [val_input n (modC C g b w') x k hkn]
      exact htrue
    · by_cases hkoob : n + C.gates.length ≤ k
      · rw [val_oob n C x k hkoob] at htrue
        simp at htrue
      · obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
        have hj : j < C.gates.length := by omega
        have hj' : j < (modC C g b w').gates.length := by simpa [modC] using hj
        rw [val_gate n C hAO.2.1 x j hj] at htrue
        rw [val_gate n (modC C g b w') hAO'.2.1 x j hj']
        by_cases hjg : j = g
        · subst hjg
          have hset : (modC C j b w').gates[j] = ⟨(gateAt C j).op, (gateAt C j).inputs.set b w'⟩ := by
            simp [modC]
          rw [hset]
          rw [← hgd] at htrue
          have hw'_eq : ((modC C j b w').wires (List.ofFn x)).getD w' false =
              (C.wires (List.ofFn x)).getD w' false :=
            val_modC_lt n C j b w' hAO hg hw' x w' hw'
          have hup' : (C.wires (List.ofFn x)).getD w false = true →
              ((modC C j b w').wires (List.ofFn x)).getD w' false = true := fun hw =>
            hw'_eq ▸ hup hw
          have ha0_lt : a0 < n + j := hAO.2.1 j hg a0 (by rw [ha]; simp)
          have ha1_lt : a1 < n + j := hAO.2.1 j hg a1 (by rw [ha]; simp)
          have ha0_eq : ((modC C j b w').wires (List.ofFn x)).getD a0 false =
              (C.wires (List.ofFn x)).getD a0 false :=
            val_modC_lt n C j b w' hAO hg hw' x a0 ha0_lt
          have ha1_eq : ((modC C j b w').wires (List.ofFn x)).getD a1 false =
              (C.wires (List.ofFn x)).getD a1 false :=
            val_modC_lt n C j b w' hAO hg hw' x a1 ha1_lt
          have hb01 : b = 0 ∨ b = 1 := by omega
          rcases hb01 with rfl | rfl
          · have rfl_a0 : a0 = w := by simpa [ha] using hget
            subst a0
            simp only [ha, List.set_cons_zero, List.map_cons, List.map_nil] at htrue ⊢
            exact eval_two_mono _ (hAO.1 _ hmem) hup' (fun h => ha1_eq ▸ h) htrue
          · have rfl_a1 : a1 = w := by simpa [ha] using hget
            subst a1
            simp only [ha, List.set_cons_succ, List.set_cons_zero, List.map_cons, List.map_nil] at htrue ⊢
            exact eval_two_mono _ (hAO.1 _ hmem) (fun h => ha0_eq ▸ h) hup' htrue
        · have heq : (modC C g b w').gates[j] = C.gates[j] :=
            modC_getElem_ne C g b w' j hjg hj' hj
          have hgdj : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
          have hjmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
          obtain ⟨c0, c1, hc⟩ := List.length_eq_two.mp (hAO.2.2 _ hjmem)
          have hc0_lt : c0 < n + j := hAO.2.1 j hj c0 (by rw [hgdj, hc]; simp)
          have hc1_lt : c1 < n + j := hAO.2.1 j hj c1 (by rw [hgdj, hc]; simp)
          rw [heq, hc]
          rw [hc] at htrue
          simp only [List.map_cons, List.map_nil] at htrue ⊢
          exact eval_two_mono _ (hAO.1 _ hjmem) (ih c0 hc0_lt) (ih c1 hc1_lt) htrue

private theorem main_thm (n : ℕ) (C : Circuit) (g b w w' : ℕ)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hb : b < 2)
    (hget : (gateAt C g).inputs.getD b 0 = w) (hw' : w' < n + g)
    (hsub : ∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = true →
      Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true)
    (hbelow : ∀ x : Fin n → Bool, Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true →
      circuitFun n C x = true) :
    IsAO2 n (modC C g b w') ∧
      circuitFun n (modC C g b w') = circuitFun n C ∧
      (modC C g b w').size = C.size := by
  refine ⟨modC_isAO2 n C g b w' hAO hg hw', ?_, ?_⟩
  · funext x
    cases hfx : circuitFun n C x
    · have hfw' : (C.wires (List.ofFn x)).getD w' false = false := by
        cases h : (C.wires (List.ofFn x)).getD w' false with
        | false => rfl
        | true =>
          have ht := hbelow x h
          rw [hfx] at ht
          cases ht
      have hfw : (C.wires (List.ofFn x)).getD w false = false := by
        cases h : (C.wires (List.ofFn x)).getD w false with
        | false => rfl
        | true =>
          have ht := hsub x h
          change (C.wires (List.ofFn x)).getD w' false = true at ht
          rw [hfw'] at ht
          cases ht
      change ((modC C g b w').wires (List.ofFn x)).getD C.output false = false
      rw [val_modC_eq_of_false n C g b w w' hAO hg hb hget hw' x hfw hfw']
      exact hfx
    · exact val_modC_mono n C g b w w' hAO hg hb hget hw' x (hsub x) C.output hfx
  · simp [modC, Circuit.size]

end PEqualNP.Outside.L_meta_2772

theorem PEqualNP.Outside.L_meta_2772 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b w w' : ℕ),
  (PEqualNP.TopForm.IsAO2 n C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧
  (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = w ∧ w' < n + g ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = true →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true) ∧
  (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true →
    PEqualNP.MetaComplexity.circuitFun n C x = true)) →
  PEqualNP.TopForm.IsAO2 n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) ∧
  PEqualNP.MetaComplexity.circuitFun n (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit) = PEqualNP.MetaComplexity.circuitFun n C ∧
  (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = C.size := by
  intro n C g b w w' h
  exact PEqualNP.Outside.L_meta_2772.main_thm n C g b w w' h.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1
    h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2
