/- Spatial Reasoning Problem 01 -/
/- It can be found at: SpatialQs.txt -/

/- (1) A is on the right of B. C is on the left of B. Hence, A is on the right of C -/

constant U : Type

constants A B C : U
constants Left Right : U
constant orientation : U → U → U → Prop

axiom a1 : orientation A B Right
axiom a2 : orientation C B Left

/- axioms to be added to SUMO -/

axiom a3 : ∀ X Y Z R, (orientation X Y R) ∧ (orientation Y Z R) → (orientation X Z R)
axiom a4 : ∀ OBJ1 OBJ2, (orientation OBJ1 OBJ2 Right) ↔ (orientation OBJ2 OBJ1 Left)

/- Demonstration Start -/
theorem A_is_on_the_right_of_C : orientation A C Right :=
begin
    have h, from (a4 _ _).elim_right a2,
    apply a3 _ _ _ _,
    apply and.intro a1 h
end
