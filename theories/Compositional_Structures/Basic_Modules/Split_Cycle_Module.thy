section \<open>Split Cycle Module\<close>

theory Split_Cycle_Module
  imports "Component_Types/Electoral_Module"
          "Component_Types/Margin_Graph_Creator"
          "Component_Types/Graph_Winner_Finder"
          "Component_Types/Cycle_Resolver"
          "../Elect_Composition"
begin

text\<open>
  The Split Cycle Module uses several other modules to perform the split cycle voting rule.
  It's made up of three Electoral Modules used sequentially.
\<close>

datatype candidates = A|B|C|D

(*WITHOUT LIMIT_PROFILE*)

fun mgWeight::"'a Weight_Function" where
"mgWeight cand P arc = (prefer_count (P) (snd arc) (fst arc)) 
- (prefer_count (P) (fst arc) (snd arc)) "

subsection \<open>First Round\<close>

text\<open>
  In the first round of the split cycle module we use the margin graph creator and 
  the graph winner finder to create a margin graph out of our profile and determine 
  some preliminary results.
  Condorcet winners will be declared winners and Condorcet losers will be declared
  losers but the majority of the candidates remain.
\<close>

fun split_cycle_first_round::"'a Electoral_Module" where
"split_cycle_first_round a p = evaluateGraph(createMarginGraph a p mgWeight)"

fun split_cycle_second_round::"'a Electoral_Module" where
"split_cycle_second_round a p = evaluateGraph( resolveAllCycles 
(createMarginGraph a p mgWeight) mgWeight p)"


fun rejectAll :: "'a Electoral_Module" where
"rejectAll a p = ({},a,{})"

function (sequential) split_cycle_complete::"'a Electoral_Module" where
"split_cycle_complete a p = ((split_cycle_first_round \<triangleright> 
split_cycle_second_round) \<triangleright> rejectAll) a p"
  by pat_completeness auto


fun testProfile::"candidates \<Rightarrow> candidates \<Rightarrow> candidates \<Rightarrow> candidates Profile" where 
"testProfile A B C =  [{(A,A),(B,B),(C,C),(A,B),(B,C),(A,C)}]"|
  "testProfile x y z = [{}]"

lemma "profile {} [{}] = True"
 unfolding profile_def all_set_conv_all_nth
  by simp

lemma "split_cycle_first_round {} [{}] = ({},{},{})"
  by auto

lemma "profile {0} [{(0,0)}] = True"
  unfolding profile_def all_set_conv_all_nth
  by simp


lemma "profile {A,B,C} (testProfile A B C)= True"
  unfolding profile_def 
            all_set_conv_all_nth 
            linear_order_on_def 
            partial_order_on_def
            preorder_on_def
            refl_on_def
            trans_def antisym_def
            total_on_def
  by simp

lemma [simp]:"getArcs {A,B,C} = {(A,B),(A,C),(B,A),(B,C),(C,A),(C,B)}"
  by auto

lemma[simp]: "limit_profile {A,B,C} (testProfile A B C) = testProfile A B C"
  by auto


lemma help11[simp]: "card {i. i = c \<and> x \<in> (s ! c)} = (if x\<in>(s ! c) then 1 else 0)"
  by auto

lemma help12[simp]: "{i. i = c \<and> x \<in> (s ! i)} = (if x\<in>(s ! c) then {c} else {})"
  by auto

(*
lemma help13[simp]:"card {i. i < n \<and> x \<in>((y # ys) ! i)} = (if n > 1 then 
   card {i. i = 0 \<and> x \<in> ([y] ! 0)}
  + card {i. i < n - 1 \<and> x \<in> (ys ! i)} else
   card {i. i = 0 \<and> x \<in> ([y] ! 0)})"
using card_Un_disjoint
  by simp_all
 *)

(*


lemma[simp]: "prefer_count (testProfile A B C) B A  = 1"
  by simp_all

lemma[simp]: "prefer_count (testProfile A B C) A B  = 0"
  by simp_all
*)
lemma [simp]:"mgWeight {A,B,C} (testProfile A B C) (A,B) = 1"
  by auto



lemma "createMarginGraph {A,B,C} (testProfile A B C) mgWeight 
= \<lparr>verts = {A,B,C}, arcs = {(A,B),(B,C),(A,C)},tail=fst, head=snd\<rparr> "
  by auto

lemma[simp]: "{a. (a = (A, B) \<or> a = (B, C) \<or> a = (A, C)) \<and> snd a = C} = {(B,C),(A,C)}"
  by auto

lemma "evaluateGraph \<lparr>verts = {A,B,C}, arcs = {(A,B),(B,C),(A,C)},tail=fst, head=snd\<rparr> = ({A},{C},{B})"
  by auto

(*Haskell, SML, Scala, OCaml*)

export_code split_cycle_first_round in Haskell
module_name SplitCycle file_prefix example

lemma "split_cycle_first_round {A,B,C} [{(A,A),(B,B),(C,C),(A,B),(B,C),(A,C)}] =({A},{C},{B})"
  

lemma "split_cycle_first_round {A,B,C} [{(A,A),(B,B),(C,C),(A,B),(B,C),(A,C)},{(A,A),(B,B),(C,C),(A,B),(B,C),(A,C)}] =({A},{C},{B})"
  

  

end