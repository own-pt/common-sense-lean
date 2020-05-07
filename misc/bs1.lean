import tactic.rcases

/-
The problem is originally presented in:
A. Pease, G. Sutcliffe, N. Siegel, and S. Trac, “Large Theory
Reasoning with SUMO at CASC,” pp. 1–8, Jul. 2009.
Here we present the natural deduction proof in Lean.

adapted https://gist.github.com/digama0/16c62d1af34212de2e3fba380d87c043#file-common-sense-lean-lean-L170
-/

constant U : Type

constants SetOrClass Set Class Object Entity NullList_m List 
          CorpuscularObject Invertebrate Vertebrate Animal SpinalColumn 
          Organism Agent Physical Abstract
          subclass_m TransitiveRelation PartialOrderingRelation Relation : U
constant BananaSlug10 : U

@[class] constants exhaustiveDecomposition3 disjointDecomposition3 partition3 : U → U → U → Prop
@[class] constant ins : U → U → Prop 
@[class] constant subclass : U → U → Prop
@[class] constant disjoint : U → U → Prop
@[class] constant component : U → U → Prop
@[class] constant part : U → U → Prop
@[class] constant inList : U → U → Prop
@[class] constant ConsFn : U → U → U
@[class] constant ListFn1 : U → U
@[class] constant ListFn2 : U → U → U
@[class] constant ListFn3 : U → U → U → U

@[class] noncomputable def subclass1 := subclass
@[instance] def subclass1_single (x y : U) [subclass1 x y] : subclass x y := by assumption

/- SUMO axioms -/

@[instance] axiom a13 : ins subclass_m PartialOrderingRelation

@[instance] axiom a15 (x y z : U) [ins x SetOrClass] [ins y SetOrClass] 
  [ins z x] [subclass1 x y] : ins z y

/- EDITED (see https://github.com/own-pt/cl-krr/issues/23) -/
axiom a72773 (a : U) [ins a Animal] : (¬ ∃ p : U, ins p SpinalColumn ∧ part p a)
  → ¬ ins a Vertebrate

/- EDITED -/
axiom a72774 : ¬ ∃ s : U, ins s SpinalColumn ∧ part s BananaSlug10

axiom a72761 (x row0 row1 : U) [ins row0 Entity] [ins row1 Entity] [ins x Entity] :
 (ListFn3 x row0 row1 = ConsFn x (ListFn2 row0 row1))

axiom a72767 (x y : U) [ins x Entity] [ins y Entity] :
 ((ListFn2 x y) = (ConsFn x (ConsFn y NullList_m)))

axiom a72768 (x : U) [ins x Entity] : (ListFn1 x = ConsFn x NullList_m)

axiom a72769 (x : U) [ins x Entity] : ¬ inList x NullList_m  

axiom a72770 (L x y : U) [ins x Entity] [ins y Entity] [ins L List] :
 ((inList x (ConsFn y L)) ↔ ((x = y) ∨ inList x L))
  
@[instance] axiom a67959 : ins NullList_m List

@[instance] axiom a67958 : ins List SetOrClass
@[instance] axiom a72772 : ins BananaSlug10 Animal
@[instance] axiom a72771 : ins Animal SetOrClass
@[instance] axiom a72778 : ins Invertebrate SetOrClass
@[instance] axiom a71402 : ins Vertebrate SetOrClass 
@[instance] axiom a71371 : ins Organism SetOrClass
@[instance] axiom a71872 : ins Agent SetOrClass
@[instance] axiom a71669 : ins Object SetOrClass
@[instance] axiom a69763 : ins Physical SetOrClass
@[instance] axiom a67331 : ins Entity SetOrClass
@[instance] axiom a67448 : ins SetOrClass SetOrClass
@[instance] axiom a68771 : ins Abstract SetOrClass
@[instance] axiom a68763 : ins Relation SetOrClass
@[instance] axiom a71844 : ins TransitiveRelation SetOrClass
@[instance] axiom a72180 : ins PartialOrderingRelation SetOrClass

@[instance] axiom a71370 : partition3 Animal Vertebrate Invertebrate

axiom a67131 {c row0 row1 : U} [ins c Class] [ins row0 Class] [ins row1 Class] :
 (partition3 c row0 row1 ↔ (exhaustiveDecomposition3 c row0 row1 ∧ disjointDecomposition3 c row0 row1))

-- EDITED (see https://github.com/own-pt/cl-krr/issues/22)
axiom a67115 :
  ∀ (row0 row1 c obj : U),
    ∃ (item : U),
      ins item SetOrClass ∧
        (ins obj Entity →
          ins c SetOrClass → ins c Class →
          ins row0 Class → ins row0 Entity → 
          ins row1 Class → ins row1 Entity →
            exhaustiveDecomposition3 c row0 row1 → ins obj c → 
              inList item (ListFn2 row0 row1) ∧ ins obj item)

@[instance] axiom a67447 : partition3 SetOrClass Set Class 
axiom a67172 : ∃ x : U, ins x Entity
axiom a67173 : ∀ {c : U}, ins c Class ↔ subclass c Entity

@[instance] axiom a67818 : subclass1 PartialOrderingRelation TransitiveRelation

@[instance] axiom a67809 (x y z : U) [ins x SetOrClass] [ins y SetOrClass] [ins z SetOrClass]
  [ins subclass_m TransitiveRelation] [subclass x y] [subclass1 y z] : subclass x z

@[instance] axiom a71382 : subclass1 Vertebrate Animal
@[instance] axiom a71383 : subclass1 Invertebrate Animal
@[instance] axiom a71369 : subclass1 Animal Organism
@[instance] axiom a71340 : subclass1 Organism Agent
@[instance] axiom a67315 : subclass1 Agent Object
@[instance] axiom a67177 : subclass1 Object Physical
@[instance] axiom a67174 : subclass1 Physical Entity
@[instance] axiom a67446 : subclass1 SetOrClass Abstract
@[instance] axiom a67332 : subclass1 Abstract Entity
@[instance] axiom a67954 : subclass1 List Relation
@[instance] axiom a67450 : subclass1 Relation Abstract

-- commented in list.kif
@[instance] axiom novo1 (x L : U) [ins L Entity] [ins L List] : ins (ConsFn x L) List

-- some initial tests

lemma VertebrateAnimal (x : U) [ins x Vertebrate] : ins x Animal := by apply_instance
lemma subclass_TransitiveRelation : ins subclass_m TransitiveRelation := by apply_instance
lemma VertebrateOrganism (x : U) [ins x Vertebrate] : ins x Organism := by apply_instance
lemma VertebrateEntity (x : U) [ins x Vertebrate] : ins x Entity := by apply_instance

lemma listLemma [hne : nonempty U] {x y z : U} [ins x Entity] [ins y Entity] [ins z Entity] :
  inList x (ListFn2 y z) → x = y ∨ x = z :=
begin
  intros h1,
  rw a72767 at h1,
  have h2 : x = y ∨ inList x (ConsFn z NullList_m), {rwa ← a72770},
  cases h2,
  { exact or.inl h2 },
  { have h3 : x = z ∨ inList x NullList_m, {rwa ← a72770},
    cases h3,
    { exact or.inr h3 },
    { exfalso,
      exact a72769 x h3 } }
end

lemma lX [hne : nonempty U] {x c c1 c2}
  [ins c SetOrClass] [ins c1 SetOrClass] [ins c2 SetOrClass]
  [ins c Class] [ins c1 Class] [ins c2 Class] [ins x Entity] :
  partition3 c c1 c2 → ins x c → ¬ ins x c1 → ins x c2 := 
begin
  intros h1 h2 h3,
  obtain ⟨h4a, h4b⟩ := a67131.1 h1,
  obtain ⟨b, h7, h8⟩ := a67115 _ _ _ _, resetI,
  cases h8 _ _ _ _ _ _ _ h4a h2 with h8a h8b; try {apply_instance},
  obtain rfl | rfl := listLemma h8a,
  {contradiction}, {assumption}
end

set_option class.instance_max_depth 200
set_option trace.class_instances true

lemma subclass_animal_entity : subclass Animal Entity := by apply_instance
lemma subclass_vertebrate_entity : subclass Vertebrate Entity := by apply_instance
lemma subclass_invertebrate_entity : subclass Invertebrate Entity := by apply_instance

lemma ins_banana_entity : ins BananaSlug10 Entity := by apply_instance
lemma ins_animal_class : ins Animal Class := a67173.2 $ by apply_instance

lemma l0  [nonempty U] : ¬(ins BananaSlug10 Vertebrate) := a72773 _ a72774

instance Vertebrate_class : ins Vertebrate Class := a67173.2 $ by apply_instance
instance Invertebrate_class : ins Invertebrate Class := a67173.2 $ by apply_instance
instance Animal_class : ins Animal Class := a67173.2 $ by apply_instance

theorem Banana_Invertebrate [nonempty U] : ins BananaSlug10 Invertebrate :=
 by apply lX a71370 _ l0; apply_instance

example (X Y C : U) [h : partition3 C X Y] : subclass X C ∧ subclass Y C := sorry -- not provable

example (h : ins SetOrClass SetOrClass) : false := sorry -- not provable
