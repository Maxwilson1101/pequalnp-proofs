import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

-- Lost edges are minimal positive inputs which fail at the output after this slot is pinned low.
-- Choose a minimum circuit with as few dirty ANDs as possible. The first cut seeks a slot
-- with mutually intersecting losses; the second handles a nontrivial star of such losses.
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_1904_271
    (intersecting : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c,G.Adj a b → G.Adj b c → ¬G.Adj c a) →
      (∀ a b c d,G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d) →
      let B := fun (C : Circuit) => (Finset.range C.size).filter (IsDirtyAnd n G C)
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C=graphFun G ∅ ∧
      (∀ D, Monotone2 D → circuitFun n D=circuitFun n C → D.size=C.size → (B C).card≤(B D).card) ∧
      ((B C).Nonempty → ∃ j∈B C, let L := fun (a b : Fin n) => G.Adj a b ∧
          ({C with gates:=C.gates.set j ⟨.or,[]⟩}).eval (List.ofFn (pairInput a b))=false
        ∀ a b c d,L a b → L c d → a=c ∨ a=d ∨ b=c ∨ b=d))
    (branchingStar : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c,G.Adj a b → G.Adj b c → ¬G.Adj c a) →
      (∀ a b c d,G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a=c ∨ b=d) →
      ∀ (C : Circuit) (j : ℕ), IsMinimalMonoCircuit n C → circuitFun n C=graphFun G ∅ → IsDirtyAnd n G C j →
      let L := fun (a b : Fin n) => G.Adj a b ∧
        ({C with gates:=C.gates.set j ⟨.or,[]⟩}).eval (List.ofFn (pairInput a b))=false
      (∃ a b c,b≠c ∧ L a b ∧ L a c ∧ ∀ u v,L u v → a=u ∨ a=v) →
      ∃ D : Circuit, Monotone2 D ∧ circuitFun n D=circuitFun n C ∧ D.size=C.size ∧
        ((Finset.range D.size).filter (IsDirtyAnd n G D)).card < ((Finset.range C.size).filter (IsDirtyAnd n G C)).card) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → (∀ (x5 x6 x7 x8 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x5 → x5 = x7 ∨ x6 = x8) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ (∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = Decidable.decide (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9 ∧ x7 x8 = Bool.true ∧ x7 x9 = Bool.true)) ∧ (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → (∀ (x9 : Fin x1 → Bool), x7.eval (List.ofFn x9) = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true)) → x6.size ≤ x7.size) ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x7]? = Option.some x8 → x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x11 : Fin x1 → Bool), (x6.wires (List.ofFn x11)).getD (x1 + x7) Bool.false = Bool.true → ∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ x11 x13 = Bool.true ∧ x11 x14 = Bool.true := by
  classical
  let allowed (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
  let rd (w : List Bool) (i : ℕ) := w.getD i false
  let lew (u v : List Bool) := u.length = v.length ∧ ∀ i, rd u i = true → rd v i = true
  let app (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map (rd w))]
  let join (p s : List Gate) (g : Gate) (o : ℕ) : Circuit := ⟨p ++ g :: s,o⟩
  let ctx {n} (p s : List Gate) (x : Fin n → Bool) (b : Bool) := s.foldl app ((p.foldl app (List.ofFn x)) ++ [b])
  let edge {n} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) := ∃ a b, G.Adj a b ∧ x a=true ∧ x b=true
  let row {n} (a b : Fin n) (i : Fin n) := decide (i=a ∨ i=b)
  let det {n} (a b : Fin n) : Gate := ⟨.and,[a.val,b.val]⟩
  have snoc {u v : List Bool} {a b : Bool} (h : lew u v) (ab : a=true → b=true) : lew (u++[a]) (v++[b]) := by
    obtain ⟨len,all⟩ := h
    refine ⟨by simp [len],?_⟩
    intro i
    by_cases idx : i < u.length
    · simpa [rd,List.getD_eq_getElem?_getD,List.getElem?_append_left idx,List.getElem?_append_left (show i<v.length by omega)] using all i
    · have h₁ : u.length ≤ i := by omega
      have h₂ : v.length ≤ i := by omega
      simp only [rd,List.getD_eq_getElem?_getD,List.getElem?_append_right h₁,List.getElem?_append_right h₂,←len]
      cases i-u.length with | zero => exact ab | succ k => simp
  have fold_le (gs : List Gate) (M : ∀ g∈gs, allowed g) {w v} (h : lew w v) : lew (gs.foldl app w) (gs.foldl app v) := by
    induction gs generalizing w v with
    | nil => exact h
    | cons g gs ih =>
      apply ih (fun k hk => M k (by simp [hk]))
      apply snoc h
      rcases (M g (by simp)).1 with op|op
      · rw [op];change (g.inputs.map (rd w)).all id=true → (g.inputs.map (rd v)).all id=true
        simpa using fun (hw : ∀ i∈g.inputs, rd w i=true) i hi => h.2 i (hw i hi)
      · rw [op];change (g.inputs.map (rd w)).any id=true → (g.inputs.map (rd v)).any id=true
        simp only [List.any_eq_true,List.mem_map,exists_exists_and_eq_and]
        rintro ⟨i,hi,hw⟩;exact ⟨i,hi,h.2 i hw⟩
  have fold_prefix (gs : List Gate) (w : List Bool) : ∃ t, gs.foldl app w = w ++ t := by
    induction gs generalizing w with
    | nil => exact ⟨[],by simp⟩
    | cons g gs ih => obtain ⟨t,h⟩:=ih (app w g);exact ⟨_::t,by simpa [app,List.append_assoc] using h⟩
  have raw {n} (p : List Gate) (x : Fin n → Bool) (i : Fin n) : rd (p.foldl app (List.ofFn x)) i=x i := by
    obtain ⟨t,e⟩:=fold_prefix p (List.ofFn x);simp [rd,e,List.getD_eq_getElem?_getD,List.getElem?_append_left (by simpa using i.isLt : i.val < (List.ofFn x).length),List.getElem?_ofFn,i.isLt]
  have ctx_eq {n} (p s : List Gate) (g : Gate) (o) (x : Fin n → Bool) : (join p s g o).wires (List.ofFn x) = ctx p s x (g.op.eval (g.inputs.map (rd (p.foldl app (List.ofFn x))))) := by
    change (p ++ g::s).foldl app (List.ofFn x) = _;simp [ctx,app,List.foldl_append]
  have detector {n} (p s : List Gate) (a b : Fin n) (o) (x : Fin n → Bool) : (join p s (det a b) o).wires (List.ofFn x) = ctx p s x (x a && x b) := by
    rw [ctx_eq];change ctx p s x ([rd (p.foldl app (List.ofFn x)) a,rd (p.foldl app (List.ofFn x)) b].all id)=_
    simp [raw]
  have ctx_le {n} (p s : List Gate) (M : ∀ g∈s, allowed g) (x : Fin n → Bool) {a b : Bool} (hb : a=true → b=true) : lew (ctx p s x a) (ctx p s x b) := fold_le s M (snoc ⟨rfl,fun _ h=>h⟩ hb)
  have input_le {n} {x y : Fin n → Bool} (h : ∀ i,x i=true → y i=true) : lew (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp,?_⟩;intro i;by_cases hi:i<n <;> simp [rd,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi];exact h ⟨i,hi⟩
  have mono_eval {n} (C : Circuit) (M : Monotone2 C) {x y : Fin n → Bool} (h : ∀ i,x i=true → y i=true) : C.eval (List.ofFn x)=true → C.eval (List.ofFn y)=true := (fold_le C.gates M (input_le h)).2 C.output
  let exactG {n} (G : SimpleGraph (Fin n)) (C : Circuit) := ∀ x, C.eval (List.ofFn x)=true ↔ edge G x
  let bad {n} (G : SimpleGraph (Fin n)) (C : Circuit) (j : ℕ) := ∃ g, C.gates[j]?=some g ∧ g.op=.and ∧ ∃ x, ¬edge G x ∧ rd (C.wires (List.ofFn x)) (n+j)=true
  let dirt {n} (G : SimpleGraph (Fin n)) (C : Circuit) : Finset ℕ := by classical exact (Finset.range C.size).filter (bad G C)
  have dirt_iff {n G C j} : j∈@dirt n G C ↔ bad G C j := by
    classical
    simp only [dirt,Finset.mem_filter,Finset.mem_range,and_iff_right_iff_imp];rintro ⟨g,h,-⟩;exact List.getElem?_eq_some_iff.mp h |>.1
  have patch {n} (G : SimpleGraph (Fin n)) (p s : List Gate) (g : Gate) (o : ℕ) (a b : Fin n)
      (adj : G.Adj a b) (M : Monotone2 (join p s g o)) (E : exactG G (join p s g o))
      (loss : ∀ u v, G.Adj u v → rd (ctx p s (row u v) false) o=false → row u v a=true ∧ row u v b=true)
      (dirty : bad G (join p s g o) p.length) :
      let D := join p s (det a b) o
      Monotone2 D ∧ exactG G D ∧ (dirt G D).card < (dirt G (join p s g o)).card := by
    classical
    let D := join p s (det a b) o
    let C := join p s g o
    change Monotone2 D ∧ exactG G D ∧ _
    have sm : ∀ k∈s, allowed k := fun k hk => M k (by simp [join,hk])
    have dm : Monotone2 D := by
      intro k hk;change k∈p++det a b::s at hk
      rcases List.mem_append.mp hk with h|h
      · exact M k (by simp [join,h])
      · rcases List.mem_cons.mp h with rfl|h
        · exact ⟨Or.inl rfl,by simp [det]⟩
        · exact sm k h
    have off (x : Fin n → Bool) (no : ¬edge G x) : (x a && x b)=false := by
      cases ha:x a <;> cases hb:x b <;> try rfl
      exact (no ⟨a,b,adj,ha,hb⟩).elim
    have neg (x : Fin n → Bool) (no : ¬edge G x) : lew (D.wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
      rw [show D=join p s (det a b) o by rfl,detector,off x no,show C=join p s g o by rfl,ctx_eq]
      exact ctx_le p s sm x (by simp)
    have member (u v : Fin n) : row u v u=true ∧ row u v v=true := by simp [row]
    have positive (u v : Fin n) (uv : G.Adj u v) : D.eval (List.ofFn (row u v))=true := by
      let z:=row u v
      change rd (D.wires (List.ofFn z)) o=true
      rw [show D=join p s (det a b) o by rfl,detector]
      cases hz:rd (ctx p s z false) o with
      | true => exact (ctx_le p s sm z (by simp)).2 o hz
      | false =>
        obtain ⟨ha,hb⟩:=loss u v uv hz
        change z a=true at ha;change z b=true at hb;rw [ha,hb];simp only [Bool.true_and]
        have hc:rd (C.wires (List.ofFn z)) o=true := (E z).mpr ⟨u,v,uv,(member u v).1,(member u v).2⟩
        rw [show C=join p s g o by rfl,ctx_eq] at hc
        exact (ctx_le p s sm z (by simp)).2 o hc
    refine ⟨dm,?_,Finset.card_lt_card ?_⟩
    · intro x;constructor
      · intro hx;by_contra he;exact he ((E x).mp ((neg x he).2 o hx))
      · rintro ⟨u,v,huv,hu,hv⟩;apply mono_eval D dm (x:=row u v) _ (positive u v huv)
        intro i hi;rcases (of_decide_eq_true hi : i=u ∨ i=v) with rfl|rfl <;> assumption
    · have staysOff (x : Fin n → Bool) (no : ¬edge G x) : rd (D.wires (List.ofFn x)) (n+p.length) ≠ true := by
        obtain ⟨t,ht⟩:=fold_prefix s ((p.foldl app (List.ofFn x))++[x a && x b]);have hlen : (p.foldl app (List.ofFn x)).length=n+p.length := by
          have len (l : List Gate) (w : List Bool) : (l.foldl app w).length=w.length+l.length := by
            induction l generalizing w with
            | nil => simp
            | cons k ks ih => simp [List.foldl_cons,ih,app,Nat.add_assoc,Nat.add_comm 1]
          simp [len]
        have hf:=off x no
        rw [show D=join p s (det a b) o by rfl,detector];change rd (s.foldl app _) _ ≠ true
        rw [ht,List.append_assoc,←hlen];simp [rd,List.getD_eq_getElem?_getD,List.getElem?_append_right,hf]
      refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨p.length,dirt_iff.mpr dirty,?_⟩
      · intro j hj;obtain ⟨k,hk,hop,x,no,hx⟩:=dirt_iff.mp hj
        have ne : j≠p.length := fun h => staysOff x no (h ▸ hx)
        have eq : C.gates[j]?=D.gates[j]? := by
          change (p++g::s)[j]?=(p++det a b::s)[j]?
          by_cases lt:j<p.length
          · simp [List.getElem?_append_left lt]
          · have le:p.length≤j:=by omega
            simp only [List.getElem?_append_right le]
            obtain ⟨k,hk⟩ : ∃ k,j-p.length=k+1 := ⟨j-p.length-1,by omega⟩
            rw [hk];rfl
        exact dirt_iff.mpr ⟨k,eq.trans hk,hop,x,no,(neg x no).2 _ hx⟩
      · intro h;obtain ⟨_,_,_,x,no,hx⟩:=dirt_iff.mp h;exact staysOff x no hx
  have starSplit {α : Type} {G : SimpleGraph α} (tri : ∀ a b c,G.Adj a b → G.Adj b c → ¬G.Adj c a)
      (R : α → α → Prop) (sub : ∀ {a b}, R a b → G.Adj a b) (sym : ∀ {a b}, R a b → R b a)
      (meet : ∀ a b c d, R a b → R c d → a=c ∨ a=d ∨ b=c ∨ b=d) (existsR : ∃ a b,R a b) :
      (∃ a b, R a b ∧ ∀ u v, R u v → (a=u ∨ a=v) ∧ (b=u ∨ b=v)) ∨
      ∃ a b c, b≠c ∧ R a b ∧ R a c ∧ ∀ u v, R u v → a=u ∨ a=v := by
    classical
    by_cases fork: ∃ a b c, b≠c ∧ R a b ∧ R a c
    · right;obtain ⟨a,b,c,bc,ab,ac⟩:=fork
      refine ⟨a,b,c,bc,ab,ac,?_⟩;intro u v uv
      by_contra fail;push Not at fail
      have hb:=meet a b u v ab uv;have hc:=meet a c u v ac uv
      have no:=tri a b c (sub ab);have ca: G.Adj c a := (sub ac).symm
      rcases hb with h|h|h|h <;> rcases hc with k|k|k|k <;> first | exact fail.1 h | exact fail.2 h | exact fail.1 k | exact fail.2 k | exact bc (h.trans k.symm) | exact no (h ▸ k ▸ sub uv) ca | exact no (h ▸ k ▸ (sub uv).symm) ca
    · left;obtain ⟨a,b,ab⟩:=existsR;refine ⟨a,b,ab,?_⟩;intro u v uv
      have uniq {x y z} (h:R x y) (k:R x z) : y=z := by by_contra ne;exact fork ⟨x,y,z,ne,h,k⟩
      rcases meet a b u v ab uv with rfl|rfl|rfl|rfl
      · exact ⟨Or.inl rfl,Or.inr (uniq ab uv)⟩
      · exact ⟨Or.inr rfl,Or.inl (uniq ab (sym uv))⟩
      · exact ⟨Or.inr (uniq (sym ab) uv),Or.inl rfl⟩
      · exact ⟨Or.inl (uniq (sym ab) (sym uv)),Or.inr rfl⟩
  have fun_bool {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) : graphFun G ∅ x = decide (∃ a b,G.Adj a b ∧ x a=true ∧ x b=true) := by
    change (decide (∃ a ∈ (∅ : Finset (Fin n)),x a=true) || _) = _;simp
  have fun_iff {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : circuitFun n C=graphFun G ∅ ↔ exactG G C := by
    constructor
    · intro e x;change circuitFun n C x = true ↔ _;rw [e,fun_bool];exact decide_eq_true_iff
    · intro e;funext x;rw [fun_bool];apply Bool.eq_iff_iff.mpr;rw [decide_eq_true_iff];exact e x
  have dirty_iff {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) : IsDirtyAnd n G C j ↔ bad G C j := by
    constructor
    · rintro ⟨op,hj,x,hx,f⟩;refine ⟨C.gates[j],List.getElem?_eq_getElem hj,?_,x,?_,hx⟩
      · change (C.gates.getD j ⟨.or,[]⟩).op=.and at op
        simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some] using op
      · rw [fun_bool,decide_eq_false_iff_not] at f;exact f
    · rintro ⟨g,hg,op,x,no,hx⟩;refine ⟨?_,(List.getElem?_eq_some_iff.mp hg).1,x,hx,?_⟩
      · change (C.gates.getD j ⟨.or,[]⟩).op=.and
        simpa only [List.getD_eq_getElem?_getD,hg,Option.getD_some] using op
      · rw [fun_bool,decide_eq_false_iff_not];exact no
  have ds_eq {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : (Finset.range C.size).filter (IsDirtyAnd n G C)=dirt G C := by
    ext j;rw [Finset.mem_filter,Finset.mem_range,dirt_iff,dirty_iff];constructor
    · exact And.right
    · intro h;refine ⟨?_,h⟩;obtain ⟨g,e,_⟩:=h;exact (List.getElem?_eq_some_iff.mp e).1
  let lost {n} (G : SimpleGraph (Fin n)) (C : Circuit) (j : ℕ) (a b : Fin n) := G.Adj a b ∧ ({C with gates:=C.gates.set j ⟨.or,[]⟩}).eval (List.ofFn (pairInput a b))=false
  have repair {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (j : ℕ) (a b : Fin n) (ab : G.Adj a b) (m : Monotone2 C) (E : circuitFun n C=graphFun G ∅) (dj : IsDirtyAnd n G C j) (h : ∀ u v, lost G C j u v → (a=u ∨ a=v) ∧ (b=u ∨ b=v)) : ∃ D, Monotone2 D ∧ circuitFun n D=graphFun G ∅ ∧ D.size=C.size ∧ (dirt G D).card < (dirt G C).card := by
    obtain ⟨ls,o⟩:=C
    obtain ⟨g,hg,_,_⟩:=(dirty_iff G _ _).mp dj
    change ls[j]?=some g at hg
    obtain ⟨p,s,el,ep⟩ : ∃ p s,ls=p++g::s ∧ j=p.length := by
      refine ⟨ls.take j,ls.drop (j+1),?_,?_⟩
      · have he : ls.drop j=g::ls.drop (j+1) := List.drop_eq_getElem_cons (List.getElem?_eq_some_iff.mp hg).1 |>.trans (by rw [(List.getElem?_eq_some_iff.mp hg).2])
        exact (List.take_append_drop j ls).symm.trans (by rw [he])
      · simp [(List.getElem?_eq_some_iff.mp hg).1.le]
    subst ls;subst j
    have z (u v : Fin n) : ({gates:=(p++g::s).set p.length ⟨.or,[]⟩,output:=o} : Circuit).eval (List.ofFn (pairInput u v))=rd (ctx p s (row u v) false) o := by
      have eq : (p++g::s).set p.length ⟨.or,[]⟩=p++⟨.or,[]⟩::s := by simp [List.set_append]
      simp only [eq];change rd ((join p s ⟨.or,[]⟩ o).wires _) o = _;rw [ctx_eq];rfl
    obtain ⟨M,X,F⟩:=patch G p s g o a b ab m ((fun_iff G _).mp E) (by
      intro u v uv fail;have H:=h u v ⟨uv,(z u v).trans fail⟩;exact ⟨decide_eq_true H.1,decide_eq_true H.2⟩) ((dirty_iff G _ _).mp dj)
    exact ⟨_,M,(fun_iff G _).mpr X,by change (p++det a b::s).length=(p++g::s).length;simp,F⟩
  intro n G inst tri square
  by_cases nonempty : ∃ a b, G.Adj a b
  · obtain ⟨C,M,E,low,witness⟩:=intersecting n G tri square
    let B := fun (D : Circuit) => (Finset.range D.size).filter (IsDirtyAnd n G D)
    have empty : ¬(B C).Nonempty := by
      intro present
      obtain ⟨j,hj,meet⟩:=witness present
      have dj : IsDirtyAnd n G C j := (Finset.mem_filter.mp hj).2
      let R := lost G C j
      change ∀ a b c d,R a b → R c d → a=c ∨ a=d ∨ b=c ∨ b=d at meet
      have cannot {D : Circuit} (dm : Monotone2 D) (de : circuitFun n D=graphFun G ∅) (size : D.size=C.size) (improve : (dirt G D).card<(dirt G C).card) : False := by
        have bound:=low D dm (de.trans E.symm) size
        change ((Finset.range C.size).filter (IsDirtyAnd n G C)).card ≤ ((Finset.range D.size).filter (IsDirtyAnd n G D)).card at bound
        rw [ds_eq,ds_eq] at bound;exact (Nat.not_lt_of_ge bound) improve
      have fix (a b) (ab : G.Adj a b) (all : ∀ u v,R u v → (a=u ∨ a=v) ∧ (b=u ∨ b=v)) : False := by
        obtain ⟨D,dm,de,size,improve⟩:=repair G C j a b ab M.1 E dj all
        exact cannot dm de size improve
      by_cases someLoss : ∃ a b,R a b
      · have sub {a b} (h:R a b) := h.1
        have sym {a b} (h:R a b) : R b a := by
          have same : pairInput b a=pairInput a b := by funext i;change decide (i=b ∨ i=a)=decide (i=a ∨ i=b);simp only [or_comm]
          exact ⟨h.1.symm,by simpa only [same] using h.2⟩
        rcases starSplit tri R sub sym meet someLoss with ⟨a,b,ab,h⟩|fork
        · exact fix a b ab.1 h
        · obtain ⟨D,dm,de,size,improve⟩:=branchingStar n G tri square C j M E dj fork
          rw [ds_eq,ds_eq] at improve;exact cannot dm (de.trans E) size improve
      · obtain ⟨a,b,ab⟩:=nonempty;exact fix a b ab (fun u v h => (someLoss ⟨u,v,h⟩).elim)
    refine ⟨C,M.1,fun x => (congrFun E x).trans (fun_bool G x),?_,?_⟩
    · intro D dm exactD;apply M.2 D dm;rw [E];funext x;exact (exactD x).trans (fun_bool G x).symm
    · intro j g loc op x on;by_contra no
      have bd : bad G C j := ⟨g,loc,op,x,no,on⟩
      exact empty ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (List.getElem?_eq_some_iff.mp loc).1,(dirty_iff G C j).mpr bd⟩⟩
  · let C : Circuit := ⟨[],n⟩
    have m : Monotone2 C := by intro g h;cases h
    refine ⟨C,m,?_,fun _ _ _ => Nat.zero_le _,?_⟩
    · intro x;change (List.ofFn x).getD n false = _
      have no : ¬ ∃ a b,G.Adj a b ∧ x a=true ∧ x b=true := by rintro ⟨a,b,h,_,_⟩;exact nonempty ⟨a,b,h⟩
      simp [List.getD_eq_getElem?_getD,no]
    · intro j g e;change ([] : List Gate)[j]?=some g at e;simp at e
