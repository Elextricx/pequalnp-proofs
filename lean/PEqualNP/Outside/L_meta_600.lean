import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_600_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) :=
  List.foldl_append

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    change (wiresFrom gs (w ++ [_])).length = _
    rw [ih]
    simp
    omega

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wiresFrom gs (w ++ [_])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp [List.getD, List.getElem?_append_left hi]

private lemma wires_getD_prefix (C : Circuit) (x : List Bool) (j i : ℕ)
    (hi : i < x.length + (C.gates.take j).length) :
    (wiresFrom (C.gates.take j) x).getD i false = (C.wires x).getD i false := by
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  have hcw : C.wires x = wiresFrom (C.gates.drop j) (wiresFrom (C.gates.take j) x) := by
    change wiresFrom C.gates x = _
    conv_lhs => rw [hsplit, wiresFrom_append]
  rw [hcw, wiresFrom_getD_lt (C.gates.drop j) (wiresFrom (C.gates.take j) x) i]
  rw [wiresFrom_length]
  exact hi

private lemma wires_getD_gate (C : Circuit) (x : List Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires x).getD (x.length + j) false =
      g.op.eval (g.inputs.map fun i => (wiresFrom (C.gates.take j) x).getD i false) := by
  have hlt : j < C.gates.length := (List.getElem?_eq_some_iff.1 hj).1
  have hge : C.gates[j] = g := by
    rw [List.getElem?_eq_getElem hlt] at hj
    exact Option.some.inj hj
  have hsplit : C.gates = C.gates.take j ++ g :: C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.drop_eq_getElem_cons hlt, hge]
  have hcw : C.wires x =
      wiresFrom (C.gates.drop (j + 1))
        (wiresFrom (C.gates.take j) x ++
          [g.op.eval (g.inputs.map fun i => (wiresFrom (C.gates.take j) x).getD i false)]) := by
    change wiresFrom C.gates x = _
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  have hlen : (wiresFrom (C.gates.take j) x).length = x.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
  rw [hcw, wiresFrom_getD_lt _ _ _ (by simp [hlen]), ← hlen]
  simp [List.getD]

private lemma wires_getD_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  change (wiresFrom C.gates (List.ofFn x)).getD w false = _
  rw [wiresFrom_getD_lt _ _ _ (by simp [hw])]
  simp [List.getD, hw]

private lemma main_aux (n : ℕ) (C : Circuit) (v : Fin n) (hmono : Monotone2 C)
    (hdep : ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = false ∧
      C.eval (List.ofFn (Function.update x v true)) = true)
    (hnotle : ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true) :
    ∃ (j : ℕ) (g : Gate) (i : ℕ),
      C.gates[j]? = some g ∧ g.op = GateOp.or ∧ i ∈ g.inputs ∧ i < n + j ∧
      ∀ x : Fin n → Bool, x v = false → (C.wires (List.ofFn x)).getD i false = false := by
  by_contra hno
  have hno' : ∀ (j : ℕ) (g : Gate) (i : ℕ),
      C.gates[j]? = some g → g.op = GateOp.or → i ∈ g.inputs → i < n + j →
      ¬ ∀ x : Fin n → Bool, x v = false → (C.wires (List.ofFn x)).getD i false = false := by
    intro j g i hj hop hi hlt hz
    exact hno ⟨j, g, i, hj, hop, hi, hlt, hz⟩
  have hinv : ∀ w : ℕ,
      (∀ x : Fin n → Bool, x v = false → (C.wires (List.ofFn x)).getD w false = false) ∨
      (∀ x : Fin n → Bool, x v = false →
        (C.wires (List.ofFn (Function.update x v true))).getD w false =
        (C.wires (List.ofFn x)).getD w false) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases hwn : w < n
      · by_cases hveq : (⟨w, hwn⟩ : Fin n) = v
        · left
          intro x hxv
          rw [wires_getD_input C x w hwn, hveq, hxv]
        · right
          intro x _
          rw [wires_getD_input C _ w hwn, wires_getD_input C x w hwn,
            Function.update_of_ne hveq]
      · by_cases hwb : w < n + C.gates.length
        · let j : ℕ := w - n
          have hjlt : j < C.gates.length := by omega
          have hwj : w = n + j := by omega
          let g : Gate := C.gates[j]
          have hgj : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
          have htake_len : (C.gates.take j).length = j := by
            rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hjlt)]
          have hpre_eq : ∀ (x : Fin n → Bool) (i : ℕ), i < n + j →
              (wiresFrom (C.gates.take j) (List.ofFn x)).getD i false =
              (C.wires (List.ofFn x)).getD i false := by
            intro x i hi
            exact wires_getD_prefix C (List.ofFn x) j i (by simp [htake_len, hi])
          have hpre_ge : ∀ (x : Fin n → Bool) (i : ℕ), n + j ≤ i →
              (wiresFrom (C.gates.take j) (List.ofFn x)).getD i false = false := by
            intro x i hi
            exact List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp [htake_len]; omega)
          have hgate_eval : ∀ x : Fin n → Bool,
              (C.wires (List.ofFn x)).getD w false =
                g.op.eval (g.inputs.map fun i =>
                  (wiresFrom (C.gates.take j) (List.ofFn x)).getD i false) := by
            intro x
            have := wires_getD_gate C (List.ofFn x) j g hgj
            simpa [List.length_ofFn, hwj] using this
          have hgop := (hmono g (List.getElem_mem hjlt)).1
          rcases hgop with hand | hor
          · by_cases hz : ∃ i ∈ g.inputs, n + j ≤ i ∨
                ∀ x : Fin n → Bool, x v = false → (C.wires (List.ofFn x)).getD i false = false
            · left
              intro x hxv
              rw [hgate_eval x, hand]
              obtain ⟨i, hi_mem, hi_case⟩ := hz
              have hval_false : (wiresFrom (C.gates.take j) (List.ofFn x)).getD i false = false := by
                rcases hi_case with hge | hzero
                · exact hpre_ge x i hge
                · by_cases hlt : i < n + j
                  · rw [hpre_eq x i hlt, hzero x hxv]
                  · exact hpre_ge x i (by omega)
              have hmem_false : false ∈ g.inputs.map (fun i =>
                  (wiresFrom (C.gates.take j) (List.ofFn x)).getD i false) :=
                List.mem_map.2 ⟨i, hi_mem, hval_false⟩
              simp only [GateOp.eval, Bool.eq_false_iff, ne_eq, List.all_eq_true, id_eq, not_forall]
              exact ⟨false, hmem_false, by decide⟩
            · right
              intro x hxv
              rw [hgate_eval _, hgate_eval _]
              congr 1
              apply List.map_congr_left
              intro i hi_mem
              have hilt : i < n + j := by
                by_contra hge
                exact hz ⟨i, hi_mem, Or.inl (by omega)⟩
              have hnz : ¬ ∀ y : Fin n → Bool, y v = false →
                  (C.wires (List.ofFn y)).getD i false = false :=
                fun hzero => hz ⟨i, hi_mem, Or.inr hzero⟩
              rw [hpre_eq _ i hilt, hpre_eq _ i hilt]
              rcases ih i (by omega) with h0 | hind
              · exact absurd h0 hnz
              · exact hind x hxv
          · right
            intro x hxv
            rw [hgate_eval _, hgate_eval _]
            congr 1
            apply List.map_congr_left
            intro i hi_mem
            by_cases hilt : i < n + j
            · rw [hpre_eq _ i hilt, hpre_eq _ i hilt]
              rcases ih i (by omega) with h0 | hind
              · exact absurd h0 (hno' j g i hgj hor hi_mem hilt)
              · exact hind x hxv
            · rw [hpre_ge _ i (by omega), hpre_ge _ i (by omega)]
        · left
          intro x _
          change (wiresFrom C.gates (List.ofFn x)).getD w false = false
          exact List.getD_eq_default _ _ (by rw [wiresFrom_length]; simp; omega)
  rcases hinv C.output with hzero | hind
  · obtain ⟨x, hxv, hxt⟩ := hnotle
    have hxf : C.eval (List.ofFn x) = false := hzero x hxv
    rw [hxt] at hxf
    cases hxf
  · obtain ⟨x, hxv, hxf, hxt⟩ := hdep
    have heq : C.eval (List.ofFn (Function.update x v true)) = C.eval (List.ofFn x) := hind x hxv
    rw [hxt, hxf] at heq
    cases heq

end PEqualNP.Outside.L_meta_600_aux

theorem PEqualNP.Outside.L_meta_600 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n), PEqualNP.MetaComplexity.Monotone2 C → (∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = false ∧ C.eval (List.ofFn (Function.update x v true)) = true) → (∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true) → ∃ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) (i : ℕ), C.gates[j]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ i ∈ g.inputs ∧ i < n + j ∧ ∀ x : Fin n → Bool, x v = false → (C.wires (List.ofFn x)).getD i false = false :=
  PEqualNP.Outside.L_meta_600_aux.main_aux
