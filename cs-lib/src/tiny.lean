/- everithing derives from an universal type U -/
constant U : Type

constant ins : U → U → Prop
constant subclass : U → U → Prop
constant orientation : U → U → U → Prop
constant OppositeDirection : U → U → Prop


/- axioms and definitions from tiny+spatial transformation -/
/- the reference can be found at: tiny+spatial.tptp -/

constants BinaryRelation Relation BinaryPredicate Predicate
Entity Physical SetOrClass TransitivePositionalAttribute
PositionalAttribute: U

-- fof(a1,axiom,s_subclass(s_BinaryRelation, s_Relation)).
axiom a1 : subclass BinaryRelation Relation

-- fof(a2,axiom,s_subclass(s_BinaryPredicate, s_Predicate)).
axiom a2 : subclass BinaryPredicate Predicate

-- fof(a3,axiom,s_subclass(s_Predicate, s_Relation)).
axiom a3 : subclass Predicate Relation

-- fof(a4,axiom,s_subclass(s_Relation, s_Entity)).
axiom a4 : subclass Relation Entity

-- fof(a5,axiom,s_subclass(s_Physical, s_Entity)).
axiom a5 : subclass Physical Entity

-- fof(a6,axiom,s_instance(s_SetOrClass, s_SetOrClass)).
axiom a6 : ins SetOrClass SetOrClass

-- fof(a7,axiom,s_subclass(s_SetOrClass, s_Entity)).
axiom a7 : subclass SetOrClass Entity

-- fof(a10,axiom,s_instance(s_Entity, s_SetOrClass)).
axiom a10 : ins Entity SetOrClass

-- fof(a132,axiom,s_subclass(s_TransitivePositionalAttribute, s_PositionalAttribute)).
axiom a132 : subclass TransitivePositionalAttribute PositionalAttribute

-- fof(a133,axiom,! [A,C,P,B] : (((s_orientation(A, B, P) & (s_orientation(B, C, P) & s_instance(P, s_TransitivePositionalAttribute))) => s_orientation(A, C, P)))).
axiom a133 : ∀ A B C P,
    (orientation A  B  P) ∧ (orientation B C P) ∧
    (ins P  TransitivePositionalAttribute) → (orientation A C P)
