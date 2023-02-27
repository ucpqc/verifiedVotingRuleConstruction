section \<open>Split Cycle Module\<close>

theory Split_Cycle_Module
  imports "Component_Types/Electoral_Module"
          "Component_Types/Margin_Graph_Creator"
          "Component_Types/Graph_Winner_Finder"
          "Component_Types/Cycle_Resolver"
          Reject_Module
begin

text\<open>
  The Split Cycle Module uses several other modules to perform the split cycle voting rule.
  It's made up of three Electoral Modules used sequentially.
\<close>

datatype candidates = A|B|C|D

fun mg_weight::"'a Weight_Function" where
"mg_weight cand P arc = (prefer_count P (fst arc) (snd arc)) 
- (prefer_count P (snd arc) (fst arc))"

fun split_cycle::"'a Electoral_Module" where
"split_cycle a p = evaluate_graph( resolve_all_cycles 
(create_margin_graph a p mg_weight) mg_weight p)"

fun split_cycle_first_round::"'a Electoral_Module" where
"split_cycle_first_round a p = evaluate_graph(create_margin_graph a p mg_weight)"

lemma first_round_sound:"electoral_module split_cycle_first_round"
  unfolding electoral_module_def
  using Graph_Winner_Finder.validResult
proof -
  show "\<forall>A rs. finite_profile (A::'a set) rs \<longrightarrow> well_formed A (split_cycle_first_round A rs)"
    by (metis (no_types) candidates_are_vertices split_cycle_first_round.simps validResult)
qed

lemma condorcet_winner_in_graph: "condorcet_winner a p c \<longrightarrow> c \<in> a"
  by simp

lemma condorcet_weight:
  assumes "condorcet_winner a p c"
  shows "\<forall>x\<in>(a - {c}). mg_weight a p (x,c) = 0"
proof 
  have "\<forall>x\<in>(a-{c}). wins c p x"
    using assms 
    by simp
  then have preferred:"\<forall>x\<in>(a-{c}).prefer_count p c x > prefer_count p x c "
    by simp
  then have "\<forall>x\<in>(a-{c}).prefer_count p x c - prefer_count p c x = 0 "
  proof -
    show ?thesis
      using preferred diff_is_0_eq order_less_imp_le
      by metis
  qed
  then show "\<And>x. x \<in> a - {c} \<Longrightarrow> mg_weight a p (x, c) = 0"
    by simp
qed

lemma condorcet_winner_no_in_arcs:
  assumes "condorcet_winner a p c"
  shows "in_arcs (create_margin_graph a p mg_weight) c = {}"
proof -
  have first:"\<forall>x\<in>(a - {c}). mg_weight a p (x,c) = 0 \<and> c\<in>a"
    using assms condorcet_weight condorcet_winner_in_graph
    by simp
  then show ?thesis
    using condorcet_degree
    by metis
qed

lemma condorcet_winner_is_winner:
  assumes "condorcet_winner a p c"
  shows "c \<in> elect (split_cycle) a p"
proof -
  have "in_arcs (create_margin_graph a p mg_weight) c = {}"
    using condorcet_winner_no_in_arcs assms
    by metis
  then have no_in_arcs: "in_arcs (resolve_all_cycles 
    (create_margin_graph a p mg_weight) mg_weight p) c = {}"
    using resolving_in_arcs_empty
    by metis
  moreover have "c\<in>verts(create_margin_graph a p mg_weight)"
    using assms
    by simp
  then have "c\<in>verts(resolve_all_cycles 
    (create_margin_graph a p mg_weight) mg_weight p)"
    using resolve_cycle_preserves_verts
    by metis
  then have "c\<in>get_winners (resolve_all_cycles 
    (create_margin_graph a p mg_weight) mg_weight p)"
    using winners_def no_in_arcs in_arcs_def
    by simp
  then show ?thesis
    by simp
qed
    
lemma non_condorcet_weight:
  assumes "condorcet_winner a p c"
  shows "\<forall>x\<in>(a - {c}). mg_weight a p (c,x) > 0"
proof 
  have "\<forall>x\<in>(a-{c}). wins c p x"
    using assms 
    by simp
  then have unpreferred:"\<forall>x\<in>(a-{c}).prefer_count p c x > prefer_count p x c "
    by simp
  then have "\<forall>x\<in>(a-{c}).prefer_count p c x - prefer_count p x c > 0 "
  proof -
    show ?thesis
      using unpreferred zero_less_diff by blast 
  qed
  then show "\<And>x. x \<in> a - {c} \<Longrightarrow> mg_weight a p (c, x) > 0"
    by simp
qed    

lemma non_condorcet_is_loser: 
  assumes "condorcet_winner a p c"
  shows "(a-{c}) =  reject (split_cycle) a p"
proof -
  have "(\<forall>x\<in>(a - {c}). mg_weight a p (c,x) > 0) \<and> c\<in>a"
    using non_condorcet_weight condorcet_winner_in_graph assms
    by metis
  then have unresolved:"\<forall>x\<in>(a - {c}). \<exists>y. y\<in>in_arcs (create_margin_graph a p mg_weight) x 
    \<and> y \<in>out_arcs (create_margin_graph a p mg_weight) c"
    using non_condorcet_degree
    by metis
  then have "\<forall>x\<in>(a - {c}). \<exists>y. (y\<in>in_arcs (
    resolve_all_cycles (create_margin_graph a p mg_weight) mg_weight p) x) 
    \<and> (y \<in>out_arcs (
    resolve_all_cycles (create_margin_graph a p mg_weight) mg_weight p) c)"
  proof (cases "cycle_exists (create_margin_graph a p mg_weight)")
    case True
    have "in_arcs (create_margin_graph a p mg_weight) c = {}"
      using condorcet_winner_no_in_arcs assms
      by metis
    then have "(out_arcs (create_margin_graph a p mg_weight) c)
      \<inter> set (get_simple_cycle (create_margin_graph a p mg_weight)) = {}"
      using condorcet_not_in_simple_cycle True Int_commute
      by metis
      
    then show ?thesis sorry
  next
    case False
    then have "arcs (resolve_all_cycles (create_margin_graph a p mg_weight) mg_weight p)
      = arcs (create_margin_graph a p mg_weight)"
      by simp
    then show ?thesis 
      using unresolved in_in_arcs_conv in_out_arcs_conv resolve_all_cycles_preserves_head resolve_all_cycles_preserves_tail
      by (metis (no_types, lifting) )
      
  qed

lemma first_round_condorcet_consistent:"condorcet_consistency split_cycle"
  sorry

 
fun testProfile::"candidates \<Rightarrow> candidates \<Rightarrow> candidates \<Rightarrow> candidates Profile" where 
"testProfile A B C =  [{(A,A),(B,B),(C,C),(A,B),(B,C),(A,C)}]"|
  "testProfile x y z = [{}]"

lemma "profile {} [{}] = True"
 unfolding profile_def all_set_conv_all_nth
  by simp


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

lemma [simp]:"get_arcs {A,B,C} = {(A,B),(A,C),(B,A),(B,C),(C,A),(C,B)}"
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

export_code split_cycle_second_round in Scala
module_name SplitCycle file_prefix example

lemma "split_cycle_first_round {A,B,C} [{(A,A),(B,B),(C,C),(A,B),(B,C),(A,C)}] =({A},{C},{B})"
  

lemma "split_cycle_first_round {A,B,C} [{(A,A),(B,B),(C,C),(A,B),(B,C),(A,C)},{(A,A),(B,B),(C,C),(A,B),(B,C),(A,C)}] =({A},{C},{B})"
  
*)
  

end