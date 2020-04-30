/- everithing derives from an universal type U -/
constant U : Type

constants DirectionalAttribute PositionalAttribute
North South East West Left Right Above Below Inside Outside: U

constant ins : U → U → Prop
constant subclass : U → U → Prop
constant orientation : U → U → U → Prop
constant OppositeDirection : U → U → Prop


/- axioms from SUMO -/

