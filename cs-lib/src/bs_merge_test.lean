-- Type universe
constant U : Type

-- Definitions from Merge.kif
constants SetOrClass Set Class Object Entity NullList_m List 
          CorpuscularObject Organism Agent Physical Abstract
          Invertebrate Vertebrate Animal subclass_m Relation
          TransitiveRelation PartialOrderingRelation  : U

constants exhaustiveDecomposition3 disjointDecomposition3 partition3 : U → U → U → Prop
constant ins : U → U → Prop 
constant subclass : U → U → Prop
constant disjoint : U → U → Prop
constant component : U → U → Prop
constant part : U → U → Prop
constant inList : U → U → Prop
constant ConsFn : U → U → U
constant ListFn1 : U → U
constant ListFn2 : U → U → U
constant ListFn3 : U → U → U → U

-- SUMO axioms from Merge.kif
axiom a13 : ins subclass_m PartialOrderingRelation

axiom a15 : ∀ x y z : U, ins x SetOrClass ∧ ins y SetOrClass → 
 (subclass x y ∧ ins z x → ins z y)

axiom a72761 : ∀ x row0 row1 : U, ins row0 Entity ∧ ins row1 Entity ∧ ins x Entity → 
 (ListFn3 x row0 row1 = ConsFn x (ListFn2 row0 row1))

axiom a72767 : ∀ x y : U, (ins x Entity ∧ ins y Entity) → 
 ((ListFn2 x y) = (ConsFn x (ConsFn y NullList_m)))

axiom a72768 : ∀ x : U, ins x Entity → (ListFn1 x = ConsFn x NullList_m)

axiom a72769 : ∀ x : U, ins x Entity → ¬ inList x NullList_m  

axiom a72770 : ∀ L x y : U, (ins x Entity ∧ ins y Entity ∧ ins L List) → 
 ((inList x (ConsFn y L)) ↔ ((x = y) ∨ inList x L))
  
axiom a67959 : ins NullList_m List

axiom a67958 : ins List SetOrClass
axiom a72771 : ins Animal SetOrClass
axiom a72778 : ins Invertebrate SetOrClass
axiom a71402 : ins Vertebrate SetOrClass 
axiom a71371 : ins Organism SetOrClass
axiom a71872 : ins Agent SetOrClass
axiom a71669 : ins Object SetOrClass
axiom a69763 : ins Physical SetOrClass
axiom a67331 : ins Entity SetOrClass
axiom a67448 : ins SetOrClass SetOrClass
axiom a68771 : ins Abstract SetOrClass
axiom a68763 : ins Relation SetOrClass
axiom a71844 : ins TransitiveRelation SetOrClass
axiom a72180 : ins PartialOrderingRelation SetOrClass

axiom a71370 : partition3 Animal Vertebrate Invertebrate

axiom a67131 : ∀ (c row0 row1 : U), (ins c Class ∧ ins row0 Class ∧  ins row1 Class) → 
 (partition3 c row0 row1 ↔ (exhaustiveDecomposition3 c row0 row1 ∧ disjointDecomposition3 c row0 row1))

-- EDITED (see https://github.com/own-pt/cl-krr/issues/22)
axiom a67115 :
  ∀ (row0 row1 c obj : U),
    ∃ (item : U),
      ins item SetOrClass ∧
        (ins obj Entity →
          ins c SetOrClass ∧ ins c Class ∧ 
          ins row0 Class ∧ ins row0 Entity ∧ 
          ins row1 Class ∧ ins row1 Entity →
            exhaustiveDecomposition3 c row0 row1 → ins obj c → 
              inList item (ListFn2 row0 row1) ∧ ins obj item)

axiom a67447 : partition3 SetOrClass Set Class 
axiom a67172 : ∃ x : U, ins x Entity
axiom a67173 : ∀ c : U, ins c Class ↔ subclass c Entity
axiom a67818 : subclass PartialOrderingRelation TransitiveRelation

axiom a67809 : ∀ x y z : U, ins x SetOrClass ∧ ins y SetOrClass ∧ ins z SetOrClass → 
  ins subclass_m TransitiveRelation → (subclass x y ∧ subclass y z → subclass x z)

axiom a71382 : subclass Vertebrate Animal
axiom a71383 : subclass Invertebrate Animal
axiom a71369 : subclass Animal Organism
axiom a71340 : subclass Organism Agent
axiom a67315 : subclass Agent Object
axiom a67177 : subclass Object Physical
axiom a67174 : subclass Physical Entity
axiom a67446 : subclass SetOrClass Abstract
axiom a67332 : subclass Abstract Entity
axiom a67954 : subclass List Relation
axiom a67450 : subclass Relation Abstract