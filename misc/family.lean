/-

From the adam's serie:

https://www.youtube.com/watch?v=SkruxPmN0kk
https://www.youtube.com/watch?v=nvHatVfiLPU

-/

constant U : Type


-- sumo axioms

constants SetOrClass Set Class Object Entity : U

constant ins : U → U → Prop 
constant subclass : U → U → Prop

constant element : U → U → Prop
constant birthplace : U → U → Prop
constant subProcess : U → U → Prop

-- problem axioms

constants John Mary Stanley Jimmy Jane Human SetJohnMaryStan SetJohnMaryJimmy OshkoshHuman
          OshkoshWisconsin FeymanLecture Lecture Thanking FeymansThankingBohr GeographicLocation : U

axiom john_human    : ins John Human
axiom mary_human    : ins Mary Human
axiom stanley_human : ins Stanley Human
axiom jimmy_human   : ins Jimmy Human
axiom jane_ohuman   : ins Jane OshkoshHuman 

axiom oshkoshwis_geo : ins OshkoshWisconsin GeographicLocation

axiom john_mary_stan : ins SetJohnMaryStan Set
axiom john_el_jms    : element John SetJohnMaryStan
axiom mary_el_jms    : element Mary SetJohnMaryStan
axiom stanley_el_jms : element Stanley SetJohnMaryStan

axiom john_mary_jimmy : ins SetJohnMaryJimmy Set
axiom john_el_jmj     : element John SetJohnMaryJimmy
axiom mary_el_jmj     : element Mary SetJohnMaryJimmy
axiom jimmy_jmj       : element Jimmy SetJohnMaryJimmy

-- https://en.wikipedia.org/wiki/Closed-world_assumption
axiom jimmy_not_jms   : ¬ element Jimmy SetJohnMaryStan

axiom oshkoshHuman_cl : subclass OshkoshHuman Human
axiom oshkoshHuman_ax : ∀ x : U, ins x OshkoshHuman → birthplace x OshkoshWisconsin


lemma sets_not_equal : ¬ SetJohnMaryStan = SetJohnMaryJimmy := 
begin
 intro a,
 have h₁, from jimmy_not_jms,
 rw a at h₁,
 exact (h₁ jimmy_jmj),
end

lemma birthplace_jane : birthplace Jane OshkoshWisconsin := 
begin
 have h₁, from oshkoshHuman_ax Jane,
 exact (h₁ jane_ohuman),
end
