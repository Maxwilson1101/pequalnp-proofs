import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3245

def Cert (p n B : ℕ) (gs : List Gate) (P L : Finset ℕ) : Prop :=
  (∀ w ∈ P, w < p ∨ ∃ (j : ℕ) (hj : j < gs.length), w = B + j ∧ gs[j].op = GateOp.or ∧ ∀ u ∈ gs[j].inputs, u ∈ P) ∧
  (∀ w ∈ L, (p ≤ w ∧ w < n) ∨ ∃ (j : ℕ) (hj : j < gs.length), w = B + j ∧ gs[j].op = GateOp.or ∧ ∀ u ∈ gs[j].inputs, u ∈ L) ∧
  ∀ (j : ℕ) (hj : j < gs.length),
    (gs[j].op = GateOp.and ∨ gs[j].op = GateOp.or) ∧
    gs[j].inputs.length = 2 ∧ (∀ u ∈ gs[j].inputs, u < B + j) ∧
    (gs[j].op = GateOp.and → ∃ a b, gs[j].inputs = [a,b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)))

def Tagged (p n : ℕ) (t : ℕ) (vs : List ℕ) : Prop :=
  (t < p ∧ ∀ u ∈ vs, p ≤ u ∧ u < n) ∨ (p ≤ t ∧ t < n ∧ ∀ u ∈ vs, u < p)

lemma cert_append {p n B : ℕ} {gs hs : List Gate} {P L P' L' : Finset ℕ}
    (hg : Cert p n B gs P L) (hh : Cert p n (B + gs.length) hs P' L') :
    Cert p n B (gs ++ hs) (P ∪ P') (L ∪ L') := by
  have pureUnion (base : ℕ → Prop) (S T : Finset ℕ)
      (hS : ∀ w ∈ S, base w ∨ ∃ (j : ℕ) (hj : j < gs.length),
        w = B + j ∧ gs[j].op = GateOp.or ∧ ∀ u ∈ gs[j].inputs, u ∈ S)
      (hT : ∀ w ∈ T, base w ∨ ∃ (j : ℕ) (hj : j < hs.length),
        w = B + gs.length + j ∧ hs[j].op = GateOp.or ∧ ∀ u ∈ hs[j].inputs, u ∈ T) :
      ∀ w ∈ S ∪ T, base w ∨ ∃ (j : ℕ) (hj : j < (gs ++ hs).length),
        w = B + j ∧ (gs ++ hs)[j].op = GateOp.or ∧ ∀ u ∈ (gs ++ hs)[j].inputs, u ∈ S ∪ T := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · rcases hS w hw with hb | ⟨j, hj, he, ho, hu⟩
      · exact Or.inl hb
      · refine Or.inr ⟨j, by simp only [List.length_append]; omega, he, ?_⟩
        simp only [List.getElem_append_left hj]
        exact ⟨ho, fun u h => Finset.mem_union.mpr (Or.inl (hu u h))⟩
    · rcases hT w hw with hb | ⟨j, hj, he, ho, hu⟩
      · exact Or.inl hb
      · refine Or.inr ⟨j + gs.length, by simp only [List.length_append]; omega, by omega, ?_⟩
        rw [← List.getElem_append_right' gs hj]
        exact ⟨ho, fun u h => Finset.mem_union.mpr (Or.inr (hu u h))⟩
  refine ⟨pureUnion (fun w => w < p) P P' hg.1 hh.1,
    pureUnion (fun w => p ≤ w ∧ w < n) L L' hg.2.1 hh.2.1, ?_⟩
  intro j hj
  by_cases h : j < gs.length
  · simp only [List.getElem_append_left h]
    obtain ⟨ho, hl, hu, ha⟩ := hg.2.2 j h
    refine ⟨ho, hl, hu, ?_⟩
    intro hand
    obtain ⟨a, b, hab, hsign⟩ := ha hand
    refine ⟨a, b, hab, ?_⟩
    exact hsign.imp (fun ⟨x, y⟩ => ⟨Finset.mem_union.mpr (.inl x), Finset.mem_union.mpr (.inl y)⟩)
      (fun ⟨x, y⟩ => ⟨Finset.mem_union.mpr (.inl x), Finset.mem_union.mpr (.inl y)⟩)
  · have hle : gs.length ≤ j := by omega
    have hbound : j < gs.length + hs.length := by simpa only [List.length_append] using hj
    have hi : j - gs.length < hs.length := by omega
    simp only [List.getElem_append_right hle]
    obtain ⟨ho, hl, hu, ha⟩ := hh.2.2 (j - gs.length) hi
    refine ⟨ho, hl, ?_, ?_⟩
    · intro u hmem
      have hlt := hu u hmem
      omega
    · intro hand
      obtain ⟨a, b, hab, hsign⟩ := ha hand
      refine ⟨a, b, hab, ?_⟩
      exact hsign.imp (fun ⟨x, y⟩ => ⟨Finset.mem_union.mpr (.inr x), Finset.mem_union.mpr (.inr y)⟩)
        (fun ⟨x, y⟩ => ⟨Finset.mem_union.mpr (.inr x), Finset.mem_union.mpr (.inr y)⟩)

private lemma blkPair {q : ℕ → Prop} {x y : ℕ} (hx : q x) (hy : q y) :
    ∀ u ∈ [x, y], q u := by
  intro u hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact hx
  · have h : u = y := List.mem_singleton.mp hu
    exact h ▸ hy

lemma cert_block (p n B a t v : ℕ) (rest : List ℕ) (lead : Bool) (hpn : p ≤ n)
    (hn : n ≤ B) (ha : lead = false → a < B) (ht : Tagged p n t (v :: rest)) :
    ∃ P L, Cert p n B (blockGates B a t v rest lead) P L := by
  let X := Finset.Ico B (B + rest.length)
  let P := if t < p then Finset.range p else Finset.range p ∪ X
  let L := if t < p then Finset.Ico p n ∪ X else Finset.Ico p n
  let S := if t < p then L else P
  let gs := blockGates B a t v rest lead
  let prev := fun i : ℕ => (v :: (List.range rest.length).map (fun j => B + j)).getD i 0
  have hraw : (∀ u ∈ v :: rest, u ∈ S ∧ u < B) ∧ t < B := by
    rcases ht with ⟨htp, hv⟩ | ⟨hpt, htn, hv⟩
    · refine ⟨?_, by omega⟩
      intro u hu
      obtain ⟨hpu, hun⟩ := hv u hu
      exact ⟨by simp [S, L, htp, hpu, hun], by omega⟩
    · have htp : ¬ t < p := by omega
      refine ⟨?_, by omega⟩
      intro u hu
      have hup := hv u hu
      exact ⟨by simp [S, P, htp, hup], by omega⟩
  have hsep : (t ∈ P ∧ S = L) ∨ (t ∈ L ∧ S = P) := by
    rcases ht with ⟨htp, _⟩ | ⟨hpt, htn, _⟩
    · exact Or.inl ⟨by simp [P, htp], by simp [S, htp]⟩
    · have htp : ¬ t < p := by omega
      exact Or.inr ⟨by simp [L, htp, hpt, htn], by simp [S, htp]⟩
  have hchain (i : ℕ) (hi : i < rest.length) : B + i ∈ S := by
    have hx : B + i ∈ X := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    by_cases h : t < p <;> simp [S, L, P, h, hx]
  have hprev (i : ℕ) (hi : i ≤ rest.length) : prev i ∈ S ∧ prev i < B + i := by
    cases i with
    | zero => simpa [prev, List.getD_cons_zero] using hraw.1 v (by simp)
    | succ j =>
      have hj : j < rest.length := by omega
      have e : prev (j + 1) = B + j := by
        simp [prev, List.getD_eq_getElem?_getD,
          List.getElem?_map, List.getElem?_range hj]
      rw [e]
      exact ⟨hchain j hj, by omega⟩
  have hrest (i : ℕ) (hi : i < rest.length) : rest.getD i 0 ∈ S ∧ rest.getD i 0 < B := by
    have hm : rest[i] ∈ v :: rest := List.mem_cons_of_mem _ (List.getElem_mem hi)
    simpa [List.getD_eq_getElem?_getD, hi] using hraw.1 _ hm
  have hlen : gs.length = rest.length + 1 + (if lead then 0 else 1) := by
    cases lead <;> simp [gs, blockGates]
  have gor (i : ℕ) (hi : i < rest.length) (hig : i < gs.length) :
      gs[i] = ⟨GateOp.or, [prev i, rest.getD i 0]⟩ := by
    dsimp only [gs, blockGates] at hig ⊢
    rw [List.getElem_append_left (by simpa using hi)]
    simp [prev]
  have gand (hig : rest.length < gs.length) :
      gs[rest.length] = ⟨GateOp.and, [t, prev rest.length]⟩ := by
    dsimp only [gs, blockGates] at hig ⊢
    rw [List.getElem_append_right (by simp)]
    simp [prev]
  have gjoin (hf : lead = false) (hig : rest.length + 1 < gs.length) :
      gs[rest.length + 1] = ⟨GateOp.or, [a, B + rest.length]⟩ := by
    dsimp only [gs, blockGates] at hig ⊢
    rw [List.getElem_append_right (by simp)]
    simp [hf]
  have hgen (w : ℕ) (hw : w ∈ X) : ∃ (j : ℕ) (hj : j < gs.length),
      w = B + j ∧ gs[j].op = GateOp.or ∧ ∀ u ∈ gs[j].inputs, u ∈ S := by
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hw
    have hi : w - B < rest.length := by omega
    have hig : w - B < gs.length := by omega
    refine ⟨w - B, hig, by omega, ?_⟩
    rw [gor _ hi hig]
    exact ⟨rfl, blkPair (hprev _ (by omega)).1 (hrest _ hi).1⟩
  refine ⟨P, L, ?_, ?_, ?_⟩
  · intro w hw
    by_cases h : t < p
    · exact Or.inl (by simpa [P, h] using hw)
    · rcases (show w < p ∨ w ∈ X by simpa [P, h] using hw) with hr | hx
      · exact Or.inl hr
      · exact Or.inr (by simpa only [S, h, ↓reduceIte] using hgen w hx)
  · intro w hw
    by_cases h : t < p
    · rcases (show (p ≤ w ∧ w < n) ∨ w ∈ X by simpa [L, h] using hw) with hr | hx
      · exact Or.inl hr
      · exact Or.inr (by simpa only [S, h, ↓reduceIte] using hgen w hx)
    · exact Or.inl (by simpa [L, h] using hw)
  · intro j hj
    change j < gs.length at hj
    change (gs[j].op = GateOp.and ∨ gs[j].op = GateOp.or) ∧ gs[j].inputs.length = 2 ∧
      (∀ u ∈ gs[j].inputs, u < B + j) ∧ (gs[j].op = GateOp.and → ∃ x y,
        gs[j].inputs = [x,y] ∧ ((x ∈ P ∧ y ∈ L) ∨ (x ∈ L ∧ y ∈ P)))
    by_cases hi : j < rest.length
    · rw [gor _ hi hj]
      refine ⟨Or.inr rfl, rfl, blkPair (hprev j (by omega)).2 ?_, ?_⟩
      · have h := (hrest j hi).2
        omega
      · intro e; cases e
    · by_cases he : j = rest.length
      · subst j
        rw [gand hj]
        have hp := hprev rest.length (by omega)
        refine ⟨Or.inl rfl, rfl, blkPair (by have h := hraw.2; omega) hp.2, ?_⟩
        intro _
        refine ⟨t, prev rest.length, rfl, ?_⟩
        rcases hsep with ⟨htP, hSL⟩ | ⟨htL, hSP⟩
        · exact Or.inl ⟨htP, hSL ▸ hp.1⟩
        · exact Or.inr ⟨htL, hSP ▸ hp.1⟩
      · have hf : lead = false := by
          cases hb : lead with
          | false => rfl
          | true =>
            have hlen' : gs.length = rest.length + 1 := by simpa [hb] using hlen
            omega
        have hlen' : gs.length = rest.length + 1 + 1 := by simpa [hf] using hlen
        have ej : j = rest.length + 1 := by omega
        subst j
        rw [gjoin hf hj]
        refine ⟨Or.inr rfl, rfl, blkPair (by have h := ha hf; omega) (by omega), ?_⟩
        intro e; cases e

lemma cert_cover (p n : ℕ) (hp : p ≤ n) (own : List (ℕ × List ℕ))
    (ht : ∀ tx ∈ own, Tagged p n tx.1 tx.2) (B a : ℕ) (lead : Bool)
    (hn : n ≤ B) (ha : lead = false → a < B) :
    ∃ P L, Cert p n B (coverGatesB B lead a own) P L := by
  induction own generalizing B a lead with
  | nil => exact ⟨∅, ∅, by simp [coverGatesB, Cert]⟩
  | cons tx os ih =>
    obtain ⟨t, vs⟩ := tx
    have tailTag : ∀ tx ∈ os, Tagged p n tx.1 tx.2 := fun x hx => ht x (List.mem_cons_of_mem _ hx)
    cases vs with
    | nil => exact ih tailTag B a lead hn ha
    | cons v rest =>
      let gs := blockGates B a t v rest lead
      have hlen : 0 < gs.length := by cases lead <;> simp [gs, blockGates]
      obtain ⟨P, L, hg⟩ := cert_block p n B a t v rest lead hp hn ha (ht (t, v :: rest) (by simp))
      obtain ⟨P', L', hh⟩ := ih tailTag (B + gs.length) (B + gs.length - 1) false (by omega) (by omega)
      exact ⟨_, _, cert_append hg hh⟩

lemma circuit_cert (p n : ℕ) (C : Circuit) (P L : Finset ℕ) (h : Cert p n n C.gates P L) :
    PEqualNP.TopForm.IsAO2 n C ∧
    (∀ w ∈ P, w < p ∨ ∃ j < C.gates.length, w = n + j ∧ (NestedCover.gateAt C j).op = GateOp.or ∧
      ∀ u ∈ (NestedCover.gateAt C j).inputs, u ∈ P) ∧
    (∀ w ∈ L, (p ≤ w ∧ w < n) ∨ ∃ j < C.gates.length, w = n + j ∧ (NestedCover.gateAt C j).op = GateOp.or ∧
      ∀ u ∈ (NestedCover.gateAt C j).inputs, u ∈ L) ∧
    ∀ j < C.gates.length, (NestedCover.gateAt C j).op = GateOp.and →
      ∃ a b, (NestedCover.gateAt C j).inputs = [a,b] ∧ (a ∈ P ∧ b ∈ L ∨ a ∈ L ∧ b ∈ P) := by
  obtain ⟨hP, hL, hg⟩ := h
  have gate (j : ℕ) (hj : j < C.gates.length) : NestedCover.gateAt C j = C.gates[j] :=
    List.getD_eq_getElem _ _ hj
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hmem
    exact (hg j hj).1
  · intro j hj u hu
    rw [gate j hj] at hu
    exact (hg j hj).2.2.1 u hu
  · intro g hmem
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hmem
    exact (hg j hj).2.1
  · intro w hw
    rcases hP w hw with h | ⟨j,hj,h₁,h₂,h₃⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, h₁, by rwa [gate j hj], by rwa [gate j hj]⟩
  · intro w hw
    rcases hL w hw with h | ⟨j,hj,h₁,h₂,h₃⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, h₁, by rwa [gate j hj], by rwa [gate j hj]⟩
  · intro j hj
    rw [gate j hj]
    exact (hg j hj).2.2.2

end PEqualNP.Outside.L_meta_3245

theorem PEqualNP.Outside.L_meta_3245 : ∀ (x1 x2 : ℕ) (x3 : List (ℕ × List ℕ)),   have x4 : ℕ := x1 + x2;   (∀ x5 ∈ x3, x5.2 ≠ [] ∧ ((x5.1 < x1 ∧ ∀ x7 ∈ x5.2, x1 ≤ x7 ∧ x7 < x4) ∨ x1 ≤ x5.1 ∧ x5.1 < x4 ∧ ∀ x7 ∈ x5.2, x7 < x1)) →     have x6 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x4 x3;     have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x6;     ∃ (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 x4 x6 ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x4 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x6.gates.length, (x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x7 x10).inputs = [x13, x14] ∧ (x13 ∈ x8 ∧ x14 ∈ x9 ∨ x13 ∈ x9 ∧ x14 ∈ x8) := by
  intro p l own
  dsimp only
  intro ht
  obtain ⟨P, L, h⟩ := PEqualNP.Outside.L_meta_3245.cert_cover p (p + l) (by omega) own
    (fun tx hx => (ht tx hx).2) (p + l) 0 true le_rfl (by simp)
  have gates : (coverCircuitB (p + l) own).gates = coverGatesB (p + l) true 0 own := by
    unfold coverCircuitB
    split <;> simp_all
  refine ⟨P, L, PEqualNP.Outside.L_meta_3245.circuit_cert p (p + l) _ P L ?_⟩
  rwa [gates]
