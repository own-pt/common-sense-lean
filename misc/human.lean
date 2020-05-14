/-
Typeful Ontologies with Direct Multilingual Verbalization
Krasimir Angelov, Ramona Enache

From https://www.molto-project.eu/sites/default/files/FinalSUMOCNL.pdf
-/

constant Class : Type

-- SUMO immediateSubclass
constant subClass : Class → Class → Type

-- SUMO subclass
constant Inherits : Class → Class → Type

constant El : Class → Type
constant Ind : Class → Type

constant Var : Class → Type

variable var {c1 c2 : Class} : Inherits c1 c2 → Var c1 → El c2
variable el (c1 c2 : Class) : Inherits c1 c2 → Ind c1 → El c2

/-
constant Formula : Type

constant qex (c : Class) : (Var c → Formula) → Formula 
constant qal (c : Class) : (Var c → Formula) → Formula

constant lno : Formula → Formula
constants land lor limpl lequiv : Formula → Formula → Formula
-/

variable inhz (c : Class) : Inherits c c
variable inhs {c1 c2 c3 : Class} : subClass c1 c2 → Inherits c2 c3 → Inherits c1 c3

variable both : Class → Class → Class 
variable either : Class → Class → Class

variable bothL (c1 c2 : Class): subClass (both c1 c2) c1
variable bothR (c1 c2 : Class) : subClass (both c1 c2) c2 
variable eitherC (c1 c2 c3 : Class) : subClass c1 c3 → subClass c2 c3 → subClass (either c1 c2) c3

-- variable KappaFn (c : Class) : (Var c → Formula) → Class
-- variable funkappa (c:Class) (p : (Var c) → Formula) : subClass (KappaFn c p) c

variable KappaFn (c : Class) : (Var c → Prop) → Class
variable funkappa (c:Class) (p : (Var c) → Prop) : subClass (KappaFn c p) c



-- HumanAdultMan < HumanAdult < Human < Hominid < Entity

variables Wading BodyOfWater Human Hominid Entity HumanAdult 
          CognitiveAgent HumanAdultMan RealNumber NonnegativeRealNumber : Class

variable ham_ha            : subClass HumanAdultMan HumanAdult
variable human_adult_human : subClass HumanAdult Human
variable human_hominid     : subClass Human Hominid
variable hominid_entity    : subClass Hominid Entity

variable H1 : Ind Human

#check el Human Hominid (inhs human_hominid (inhz Hominid)) H1 

variable AbsoluteValueFn : El RealNumber → Ind NonnegativeRealNumber

/-
variable located : El Wading → El BodyOfWater → Formula

#check qal Wading (λ (p : Var Wading), qex BodyOfWater (λ (w : Var BodyOfWater), 
          located (var (inhz Wading) p) (var (inhz BodyOfWater) w)))
-/

variable located : El Wading → El BodyOfWater → Prop

#check ∀ p : Var Wading, ∃ w : Var BodyOfWater, located (var (inhz Wading) p) (var (inhz BodyOfWater) w)


theorem test0 : Inherits Hominid Entity :=
 inhs hominid_entity (inhz Entity)

variable humanClass : subClass Human (both CognitiveAgent Hominid)

theorem test7 : Inherits Human Hominid := 
 inhs humanClass (@inhs (both CognitiveAgent Hominid) Hominid Hominid (bothR CognitiveAgent Hominid) (inhz Hominid))

theorem test1 : Inherits Human Hominid := 
 inhs human_hominid (inhz Hominid)

theorem test2 : Inherits HumanAdult Human := 
 inhs human_adult_human (inhz Human)

theorem test3 : Inherits HumanAdultMan HumanAdult := 
 inhs ham_ha (inhz HumanAdult)

-- why I need the @ ?
theorem test4 : Inherits Human Entity := 
 inhs human_hominid (test0 inhz @inhs Hominid Entity hominid_entity)

theorem test5 : Inherits HumanAdult Entity := 
 inhs human_adult_human (test4 inhz @inhs Human Hominid Entity human_hominid hominid_entity)

theorem test6 : Inherits HumanAdultMan Entity :=
 inhs ham_ha (test5 inhz @inhs Human Hominid Entity HumanAdult human_adult_human human_hominid hominid_entity)

