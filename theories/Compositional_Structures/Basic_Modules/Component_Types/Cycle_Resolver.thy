section \<open>Cycle_Resolver\<close>

theory Cycle_Resolver
  imports "Graph_Theory.Digraph" 
          "Graph_Theory.Arc_Walk" 
          "Social_Choice_Types/Profile"
          "Cycle_Detector"
          "Margin_Graph_Creator"
begin

text\<open>
\<close>

type_synonym ('a, 'b) Cycle_Resolver = "('a, 'b) pre_digraph \<Rightarrow> 'a Weight_Function \<Rightarrow>  'a Profile \<Rightarrow>('a, 'b) pre_digraph"

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

text\<open>
  These functions are actually important
\<close>

fun resolveCycle::"('a*'a) list\<Rightarrow>('a, ('a*'a)) pre_digraph \<Rightarrow> 'a Weight_Function \<Rightarrow>  'a Profile \<Rightarrow>('a, ('a*'a)) pre_digraph" where
"resolveCycle cyc G f p = 
\<lparr>verts = verts G, arcs = arcs G - 
(min_elems cyc f (verts G) p),
tail=tail G, head=head G\<rparr>"

fun resolveOneCycle ::"('a,('a*'a)) Cycle_Resolver" where
"resolveOneCycle G f p = resolveCycle (getSimpleCycle G) G f p"

lemma min_elems_in_set[simp]:
assumes "l \<noteq> []"
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
  then have "x \<in> (if (\<forall> y \<in> set l'. f c p y \<ge> f c p a) then {a} else {}) \<union> min_elems l' f c p"
    by simp 
  then show ?case 
    using UnCI insert_iff set_ConsD
    by metis
  qed
qed


lemma single_cycle_non_distinct[simp]:
  assumes "cycleExists G"
  shows "distinct (getSingleCycle G) = False"
proof -
  show ?thesis
    using CollectD assms cycleExists.elims(2) ex_in_conv getCyclicalWalks.simps getSingleCycle.elims
    by metis 
qed

lemma single_cycle_non_empty[simp]:
  assumes "cycleExists G"
  shows "(getSingleCycle G) \<noteq> []"
proof -
  show ?thesis
    using CollectD assms cycleExists.elims(2) distinct.simps(1) ex_in_conv getCyclicalWalks.simps getSingleCycle.simps
    by metis
qed

lemma single_cycle_in_arcs[simp]:
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
    by simp
qed

lemma trim_subset[simp]: "set (trimCyclicalPath p) \<subseteq> set p"
   sorry


lemma trim_nonempty[simp]: "p \<noteq> [] \<Longrightarrow> trim p \<noteq> []"
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
  
lemma trim_cyc_nonempty[simp]: "p \<noteq> [] \<Longrightarrow> trimCyclicalPath p \<noteq> []"
  by simp
 

lemma min_elems_nonempty[simp]:
  assumes non_empty:"l \<noteq> []"
  shows "min_elems l f c p \<noteq> {}"
proof -
  show ?thesis
    using non_empty assms min_elems.elims min_elems.simps(2)
    by metis
qed

lemma smallest_arcs_nonempty[simp]:
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

lemma getSimpleCycle_in_arcs[simp]:
assumes cycle:"cycleExists G"
shows "set (getSimpleCycle G) \<subseteq> arcs G"
proof (rule subsetI)
fix x
  assume x_in_cycle:"x \<in> set (getSimpleCycle G)"
  have simple_in_single:"set (getSimpleCycle G) \<subseteq> set (getSingleCycle G)"
    using trim_subset
    by simp
  have single_in_arcs:"set (getSingleCycle G) \<subseteq> arcs G"
    using single_cycle_in_arcs cycle
    by simp
have x_in_arcs: "x \<in> arcs G"
  using single_cycle_in_arcs trim_subset x_in_cycle
  by simp
show "x \<in> arcs G"
by (rule x_in_arcs)
qed


lemma smallest_arcs_in_graph[simp]:
  assumes "cycleExists G"
  shows "min_elems (getSimpleCycle G) f c p \<subseteq> arcs G"
proof
  fix x
  assume "x \<in> min_elems (getSimpleCycle G) f c p"
  then have "x \<in> set (getSimpleCycle G)" using min_elems_in_set by blast
  then show "x \<in> arcs G" using assms getSimpleCycle_in_arcs by blast
qed

lemma resolveCycle_strictly_decreases_arcs[simp]:
  assumes cycle_exists: "cycleExists G"
  shows "(arcs G) \<supset> (arcs (resolveOneCycle G f p))"
proof -
  have min_elems_in_arcs: "min_elems (getSimpleCycle G) f c p \<subseteq> arcs G"
    using smallest_arcs_in_graph cycle_exists by simp
  have getSimpleCycle_in_arcs: "set (getSimpleCycle G) \<subseteq> arcs G"
    using getSimpleCycle_in_arcs cycle_exists by simp
  have removed_at_least_one_arc: "min_elems (getSimpleCycle G) f c p \<subset> arcs G"
    using min_elems_in_arcs by blast
  have removed_at_least_one_element: "set (getSimpleCycle G) \<subset> arcs G"
    using getSimpleCycle_in_arcs by blast
  have is_subset:"(arcs G) \<supset> (arcs G - min_elems (getSimpleCycle G) f c p)"
    using removed_at_least_one_arc card_Diff_singleton by auto
  finally show ?thesis .
  using is_subset
  by simp
qed


lemma empty_graph_has_no_cycle[simp]:
  assumes "cycleExists G"
  shows "arcs G \<noteq> {}"
proof -
  show ?thesis
    using no_arcs_no_cycle assms no_arcs_no_cycle old.unit.exhaust surjective
    by metis (full_types)
qed

lemma resolveAllCycles_terminates:
"\<lbrakk>(cycleExists G); (arcs G\<noteq> {})\<rbrakk> \<Longrightarrow>  ((arcs (resolveAllCycles G f p)) \<subset> (arcs G))"
proof (induction G f p rule: resolveAllCycles.induct)
case (G f p)
assume "cycleExists G" and "(arcs G\<noteq> {})"
then have "((arcs (resolveAllCycles G f p)) \<subset> (arcs G))"
using resolveOneCycle_strictly_decreases_arcs by auto
thus "arcs (resolveAllCycles (resolveOneCycle G f p) f p) \<subset> (arcs G)"
using "1.IH" by auto
qed


function (sequential) resolveAllCycles::"('a, ('a*'a)) Cycle_Resolver" where
"resolveAllCycles G f p= (if cycleExists G 
  then resolveAllCycles (resolveOneCycle G f p)f p else G)"
  by pat_completeness auto
termination
proof-
  show ?thesis
    using resolveAllCycles_terminates
qed


