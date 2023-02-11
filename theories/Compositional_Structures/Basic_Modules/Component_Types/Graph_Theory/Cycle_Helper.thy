(* Title:  Cycle_Helper.thy
   
*)

theory Cycle_Helper
  imports "Graph_Theory.Digraph" 
          "Graph_Theory.Arc_Walk" 
          "../Social_Choice_Types/Profile"
          "../Cycle_Detector"
          "../Margin_Graph_Creator"
begin

section \<open>Additional theorems for Graphs\<close>

text\<open>
  The following three functions serve to turn any cycle into a simple cycle
\<close>

fun trim::"'b awalk \<Rightarrow> 'b awalk" where
"trim [] = []" |
"trim (e # es) = (if distinct es then (e#es) else trim es)"

fun trimCyclicalPath::"'b awalk \<Rightarrow> 'b awalk" where
"trimCyclicalPath path = trim(rev(trim path))" 

fun getSingleCycle::"('a,('a*'a)) pre_digraph \<Rightarrow> ('a*'a) awalk" where
"getSingleCycle G = (SOME x. x \<in> getCyclicalWalks G)"

fun getSimpleCycle::"('a,('a*'a)) pre_digraph \<Rightarrow> ('a*'a) awalk" where
"getSimpleCycle G = trimCyclicalPath (getSingleCycle G)"

text\<open>
  These three functions serve to find the elements in a list with minimum weight
\<close>

fun min_elems :: "('a*'a) list => 'a Weight_Function \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> ('a*'a) set" where
"min_elems [] f c p = {}" |
"min_elems (x#xs) f c p= (if (\<forall> y \<in> set xs. f c p y \<ge> f c p x) then {x} 
else {}) \<union> min_elems xs f c p"

lemma min_elems_in_set:
shows "(min_elems l f c p) \<subseteq> set l"
proof
  fix x
  assume "x \<in> min_elems l f c p"
  thus "x \<in> set l"
  proof (induction l)
    case Nil
    then show ?case 
      by auto
  next
    case (Cons a l')
    then have "x \<in> min_elems (a # l') f c p"
      by simp
    then have assm:"x \<in> (if (\<forall> y \<in> set l'. f c p y \<ge> f c p a) then {a} else {}) \<union> min_elems l' f c p"
      by simp 
    then show ?case 
      proof (cases "\<forall> y \<in> set l'. f c p y \<ge> f c p a")
        case True
        then have either: "x \<in> ({a} \<union> min_elems l' f c p)" 
          using assm
          by simp
        then have "a \<in> set (a # l')"
          by auto
        then show ?thesis 
          using Cons.IH either
          by fastforce
      next
        case False
        then have "x \<in> min_elems l' f c p"
          by (smt (verit, ccfv_SIG) False Un_empty_left assm)
        then show ?thesis 
          using Cons.IH
          by fastforce
      qed
  qed
qed


lemma single_cycle_non_distinct:
  assumes cycle:"cycleExists G"
  shows "distinct (getSingleCycle G) = False"
proof -
  have not_empty:"getCyclicalWalks G \<noteq> {}"
    using cycle
    by auto
  then have single_cycle_in_cycles:"(getSingleCycle G)\<in>(getCyclicalWalks G)"
    using some_in_eq getSingleCycle.simps
    by metis
  have "\<forall>x\<in>(getCyclicalWalks G). distinct x = False"
    by auto
  then show "distinct (getSingleCycle G) = False"
    using single_cycle_in_cycles 
    by auto 
qed

lemma single_cycle_non_empty:
  assumes cycle:"cycleExists G"
  shows "(getSingleCycle G) \<noteq> []"
proof -
  have not_empty:"getCyclicalWalks G \<noteq> {}"
    using cycle
    by auto
  then have single_cycle_in_cycles:"(getSingleCycle G)\<in>(getCyclicalWalks G)"
    using some_in_eq getSingleCycle.simps
    by metis
  have "\<forall>x\<in>(getCyclicalWalks G). legitPath G x"
    by auto
  then show "(getSingleCycle G) \<noteq> []"
    using single_cycle_in_cycles legit_path_non_empty
    by auto
qed


lemma single_cycle_in_arcs:
  assumes cycle:"cycleExists G"
  shows "set (getSingleCycle G) \<subseteq> arcs G"
proof -
  have not_empty:"getCyclicalWalks G \<noteq> {}"
    using cycle
    by auto
  have single_cycle_in_cycles:"(getSingleCycle G)\<in>(getCyclicalWalks G)"
    using getSingleCycle.simps not_empty some_in_eq
    by metis
  show "set (getSingleCycle G) \<subseteq> arcs G"
    using single_cycle_in_cycles
    sorry
qed


lemma trim_subset: "set (trimCyclicalPath p) \<subseteq> set p"
   sorry

lemma trim_nonempty: "p \<noteq> [] \<Longrightarrow> trim p \<noteq> []"
proof (induction p)
  case Nil
  then show ?case by simp
next
  case (Cons a p)
  then show ?case
  proof (cases "distinct p")
    case True
    then show ?thesis by simp
  next
    case False
    then have "trim p \<noteq> []"
      using Cons.IH by fastforce
    then show ?thesis by simp
  qed
qed
  

lemma trim_cyc_nonempty: "p \<noteq> [] \<Longrightarrow> trimCyclicalPath p \<noteq> []"
  by simp
 
lemma min_elems_nonempty:
  assumes non_empty:"l \<noteq> []"
  shows "min_elems l f c p \<noteq> {}"
proof -
  show ?thesis
    using non_empty assms min_elems.elims min_elems.simps(2)
    by metis
qed


lemma smallest_arcs_nonempty:
  assumes Cycle:"cycleExists G"
  shows "min_elems (getSimpleCycle G) f c p \<noteq> {}"
proof -
  have first_step:"getSingleCycle G \<noteq> []"
    using Cycle CollectD cycleExists.elims(2) distinct.simps(1) ex_in_conv getCyclicalWalks.simps getSingleCycle.simps
    by metis 
  have second_step:"getSimpleCycle G \<noteq> []"
    using first_step
    by simp
  show "min_elems (getSimpleCycle G) f c p \<noteq> {}"
    using second_step
    by simp
qed


lemma getSimpleCycle_in_arcs:
assumes cycle:"cycleExists G"
shows "set (getSimpleCycle G) \<subseteq> arcs G"
proof (rule subsetI)
fix x
  assume x_in_cycle:"x \<in> set (getSimpleCycle G)"
  have simple_in_single:"set (getSimpleCycle G) \<subseteq> set (getSingleCycle G)"
    using trim_subset
    by simp
  then have single_in_arcs:"set (getSingleCycle G) \<subseteq> arcs G"
    using single_cycle_in_arcs cycle
    by simp
  then have x_in_arcs: "x \<in> arcs G"
    using single_in_arcs x_in_cycle simple_in_single 
    by simp
show "x \<in> arcs G"
by (rule x_in_arcs)
qed



lemma smallest_arcs_in_graph:
  assumes "cycleExists G"
  shows "min_elems (getSimpleCycle G) f c p \<subseteq> arcs G"
proof
  fix x
  assume "x \<in> min_elems (getSimpleCycle G) f c p"
  then have "x \<in> set (getSimpleCycle G)" using min_elems_in_set by blast
  then show "x \<in> arcs G" using assms getSimpleCycle_in_arcs by blast
qed


lemma empty_graph_has_no_cycle:
  assumes empty:"arcs G = {}"
  shows "cycleExists G = False"
proof -
  have "getCyclicalWalks G = {}"
    proof (rule ccontr)
      assume "getCyclicalWalks G \<noteq> {}"
      then obtain w where "w \<in> getCyclicalWalks G"
        by auto
      then have "legitPath G w"
        by auto
      then have "set w \<subseteq> arcs G"
        sorry
      then show False 
        using empty
        by auto
    qed
    then show ?thesis
      by simp
qed


end