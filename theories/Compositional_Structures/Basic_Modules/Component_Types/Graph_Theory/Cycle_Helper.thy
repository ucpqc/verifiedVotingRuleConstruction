(* Title:  Cycle_Helper.thy
   
*)

theory Cycle_Helper
  imports "Graph_Theory.Digraph" 
          "Graph_Theory.Arc_Walk" 
          "../Social_Choice_Types/Profile"
begin

section \<open>Additional theorems for Graphs\<close>

type_synonym 'a Margin_Graph = "('a, ('a\<times>'a)) pre_digraph"
type_synonym 'a Weight_Function = "'a set \<Rightarrow> 'a Profile \<Rightarrow> ('a*'a) \<Rightarrow> nat"

subsection \<open>Finding Cycles\<close>

text\<open>
  The following two functions serve to find cycles in a graph
\<close>

fun path ::"('a, 'b) pre_digraph \<Rightarrow> 'b awalk \<Rightarrow> bool" where
"path G [] = True" |
"path G [e] = (e\<in>(arcs G) \<and> head G e \<noteq> tail G e)" |
"path G (e # (f # es))= (e\<in>(arcs G) \<and> head G e \<noteq> tail G e \<and> (head G e) =
 (tail G f)\<and> path G (f#es))"

fun get_cyclical_walks::"('a, 'b) pre_digraph \<Rightarrow> 'b awalk set" where
"get_cyclical_walks G = {walk.(path G walk)\<and>
 (length walk \<le> card(verts G)) \<and> \<not>(distinct walk)}"

fun cycle_exists::"('a, 'b) pre_digraph \<Rightarrow> bool" where
"cycle_exists G = (get_cyclical_walks G  \<noteq> {})"

lemma first_in_arc:"path G (e # es) \<longrightarrow> e\<in>arcs G"
  using path.elims(2) by blast
 
lemma head_of_path_is_path: 
  assumes "path G (Cons a b)"
  shows "path G [a]"
proof -
  show ?thesis
    using assms
  proof -
    obtain bb :: "'b list \<Rightarrow> 'b" and bbs :: "'b list \<Rightarrow> 'b list" where
      "\<forall>bs. bs = bb bs # bbs bs \<or> bs = []"
      using list.exhaust
      by metis
    then show ?thesis
      using assms path.simps(2) path.simps(3)
      by metis
  qed    
qed

lemma tail_of_path_is_path:
  assumes "path G (e # es)"
  shows "path G es"
proof -
  show ?thesis
    using assms
  proof (cases "es = []")
    case True
    then have is_empty:"es = []" by metis
    have empty_good:"path G []"
      by simp
    thus "path G es" 
      using is_empty empty_good by metis
next
  case False
  then have "path G (e #  es)" using assms by simp
  then show "path G es" 
    using path.simps(3) False path.elims(1)
    by auto
  qed
qed

lemma path_in_graph: 
  shows "path G walk \<longrightarrow> set walk \<subseteq> arcs G"
proof (induction walk)
  case Nil
  then show ?case by simp
next
  case (Cons a walk)
  assume IH1:"path G walk \<longrightarrow> set walk \<subseteq> arcs G"
  then show "path G (a#walk) \<longrightarrow> set (a#walk) \<subseteq> arcs G"
  proof -
    have "set walk \<subseteq> arcs G \<or> \<not> path G walk"
      using IH1
      by metis
    then show ?thesis
      using first_in_arc insert_subsetI list.simps(15) tail_of_path_is_path
      by (metis (full_types) )
  qed
qed

lemma path_prior_arc_exists:
  assumes "path G (e#es)"
  shows "\<forall>x \<in>set es. \<exists>y\<in>set(e#es). tail G x = head G y"
  using assms
proof (induction es arbitrary:e)
  case Nil
  then show ?case by simp
next
  case (Cons a es)  
  then have is_path:"path G (a#es)"   
    by simp
  then have "tail G a = head G e" 
    using Cons.prems path.elims(3)
    by simp
  then have IS:"\<exists>y \<in> set (e#a#es). tail G a = head G y" 
    by simp
  then have "\<forall>x\<in>set es. \<exists>y\<in>set (a # es). tail G x = head G y"
    using is_path Cons.IH
    by metis
  then have "\<forall>x\<in>set (a#es). \<exists>y\<in>set (e#a#es). tail G x = head G y"
    using IS
    by simp
  then show ?case by auto
qed
  
lemma no_in_arcs_only_head_of_path:
  assumes "in_arcs G c = {}"
  assumes "path G (e#es)"
  shows "(set (es) \<inter> out_arcs G c) = {}"
proof -
  have subset_es:"set es \<subseteq> set (e#es)"
    by auto
  have first_step:"set (e#es) \<inter> in_arcs G c = {}"
    using assms(1)
    by simp
  then have "\<nexists>a. a\<in>(set (e#es)) \<and> head G a = c"
    using assms(2) path_in_graph by fastforce
  then show ?thesis
    using assms(2) path_prior_arc_exists disjoint_iff_not_equal in_out_arcs_conv
    by metis
qed
    


lemma getCyclicalWalks_in_arcs:
 shows "\<forall> walk \<in> get_cyclical_walks G. set walk \<subseteq> arcs G"
proof (intro ballI)
fix walk
assume "walk \<in> get_cyclical_walks G"
  from this have "path G walk"
    by auto
  then show "set walk \<subseteq> arcs G" 
    using path_in_graph
    by metis
qed

lemma empty_graph_has_no_cycle:
  assumes "arcs G = {}"
  shows "cycle_exists G = False"
proof -
  have "get_cyclical_walks G = {}"
    proof (rule ccontr)
      assume "get_cyclical_walks G \<noteq> {}"
      then obtain w where w_cyclical:"w \<in> get_cyclical_walks G"
        by auto
      then have "path G w"
        by auto
      then have w_in_arcs: "set w \<subseteq> arcs G"
        using path_in_graph
        by metis
      have "distinct w = False"
        using w_cyclical
        by simp
      then have w_not_empty:"w \<noteq> []"
        by auto
      then show False 
        using assms w_in_arcs w_not_empty
        by simp
    qed
    then show ?thesis
      by simp
  qed

lemma less_arcs_less_paths:
  assumes "arcs H\<subseteq>arcs G""verts H=verts G""head H=head G""tail H=tail G""path H w"
  shows "path G w"
  using assms
proof (induction rule:path.induct)
  case (1 G)
  then show ?case by simp
next
  case (2 G e)
  then show ?case using path.simps(2) by auto
next
  case (3 G e f es)
  then show ?case using path.simps(3) by auto
qed

lemma less_arcs_less_cycles:
  assumes "arcs H\<subseteq>arcs G""verts H=verts G""head H=head G""tail H=tail G"
  shows "get_cyclical_walks H \<subseteq> get_cyclical_walks G"
proof (rule subsetI)
  fix x
  assume "x\<in>get_cyclical_walks H"
  then have x_def:"path H x \<and> (length x \<le> card(verts H)) \<and> \<not>(distinct x)"
    by simp
  then have less_paths:" path G x" 
    using less_arcs_less_paths assms
    by metis
  have "card (verts H) = card (verts G)"
    using assms(2)
    by metis
  then have "(length x \<le> card(verts G))" using x_def by simp
  then have "path G x \<and> (length x \<le> card(verts G)) \<and> \<not>(distinct x)"
    using less_paths x_def by simp
  then show "x\<in>get_cyclical_walks G" using get_cyclical_walks.simps by simp
qed

subsection \<open>Turning Cycles into simple cycles\<close>

text\<open>
  The following three functions serve to turn any cycle into a simple cycle
\<close>

fun trim::"'b awalk \<Rightarrow> 'b awalk" where
"trim [] = []" |
"trim (e # es) = (if distinct es then (e#es) else trim es)"

fun trim_cyclical_path::"'b awalk \<Rightarrow> 'b awalk" where
"trim_cyclical_path walk = trim(rev(trim walk))" 

lemma trim_subset: "set (trim p) \<subseteq> set p"
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
    then have induct:"trim (a#p) = trim p"
      by simp
    have "trim [p] = [p]" by simp
    then show ?thesis using induct
      by (simp add: local.Cons subset_insertI2) 
  qed
qed

lemma trim_cyc_subset: "set (trim_cyclical_path p) \<subseteq> set p"
  using trim_subset dual_order.trans set_rev trim_cyclical_path.simps
  by metis

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

lemma trim_cyc_nonempty:
  assumes "p \<noteq> []" 
  shows"trim_cyclical_path p \<noteq> []"
proof -
  have "trim p \<noteq> []"
    using assms trim_nonempty
    by metis
  then have "rev (trim p) \<noteq> []"
    using rev_nonempty_induct
    by simp
  then show ?thesis
    using trim_nonempty
    by auto
qed

lemma trim_head_away:
  assumes "distinct (e#es) = False"
  assumes "A \<inter> set (es) = {}"
  assumes "e\<in>A"
  shows "A \<inter> set(trim_cyclical_path(e#es)) = {}"
proof -
  have "e\<notin>set es"
    using assms(2) assms(3)
    by auto
  then have "distinct es = False"
    using assms(1)
    by simp
  then have "trim (e#es) = trim (es)"
    by simp
  then have headless:"trim_cyclical_path (e#es) = trim (rev (trim es))"
    by simp
  have "set (trim (rev (trim es))) \<subseteq> set es"
    using trim_cyc_subset
    by fastforce
  then have "set(trim_cyclical_path(e#es)) \<subseteq> set es"
    using headless
    by simp
  then show ?thesis
    using assms(2)
    by auto
qed

lemma no_in_arcs_no_head:
  assumes "in_arcs G c = {}"
  assumes "(e#es) \<in> get_cyclical_walks G"
  shows "out_arcs G c \<inter> set (trim_cyclical_path(e#es)) = {}"
proof -
  have non_distinct:"distinct (e#es) = False"
    using assms(2)
    by simp
  have "path G (e#es)"
    using assms(2)
    by simp
  then have tail_not_inter:" out_arcs G c \<inter> set (es) = {}"
    using no_in_arcs_only_head_of_path assms inf_commute
    by metis
  then show ?thesis 
  proof (cases "e\<in>out_arcs G c")
    case True
    then show ?thesis
      using trim_head_away assms(2) tail_not_inter non_distinct
      by metis
  next
    case False
    then have total_not_inter:"out_arcs G c \<inter> set (e#es) = {}"
      using tail_not_inter 
      by auto
    then show ?thesis 
    proof -
      have "set (trim_cyclical_path (e # es)) \<subseteq> set (e # es)"
        by (meson trim_cyc_subset)
      then show ?thesis
        using total_not_inter
        by blast
    qed
  qed
qed  

text \<open>These are just helpful for proofs\<close>

definition all_simple_cycles::"('a, 'b) pre_digraph \<Rightarrow> 'b awalk set" where
"all_simple_cycles G =  trim_cyclical_path ` (get_cyclical_walks G)"

definition all_arcs_in_cycles::"('a, 'b) pre_digraph \<Rightarrow> 'b set" where
"all_arcs_in_cycles G = \<Union> (set ` (all_simple_cycles G))"

lemma cyc_arc_still_arc: "all_arcs_in_cycles G \<subseteq> arcs G"
proof -
  have 1:"\<forall>x\<in>all_simple_cycles G. \<exists>y\<in>get_cyclical_walks G. set x \<subseteq> set y"
    using trim_cyc_subset all_simple_cycles_def image_iff
    by metis
  have 2:"\<forall>y\<in>get_cyclical_walks G. set y \<subseteq> arcs G"
    using getCyclicalWalks_in_arcs
    by metis
  then show ?thesis 
    using 1 all_arcs_in_cycles_def Union_least dual_order.trans image_iff
    by (smt (verit))
qed

lemma less_paths_less_cycles:
  assumes "get_cyclical_walks H \<subseteq> get_cyclical_walks G"
  shows "all_arcs_in_cycles H \<subseteq> all_arcs_in_cycles G"
  using all_arcs_in_cycles_def all_simple_cycles_def assms Union_mono image_mono
  by metis

                                
text \<open>These currently get used in the implementation. 
  WARNING: Only call get_single_cycle if you know cycle_exists G, 
  otherwise an error will be thrown.\<close>

fun get_single_cycle::"('a,('a*'a)) pre_digraph \<Rightarrow> ('a*'a) awalk" where
"get_single_cycle G = (SOME x. x \<in> get_cyclical_walks G)"

fun get_simple_cycle::"('a,('a*'a)) pre_digraph \<Rightarrow> ('a*'a) awalk" where
"get_simple_cycle G = trim_cyclical_path (get_single_cycle G)"

lemma simple_cycle_other_def:
  assumes "cycle_exists G"
  shows "get_simple_cycle G \<in> all_simple_cycles G"
proof - 
  have single_cycle_def:"(get_single_cycle G) \<in> get_cyclical_walks G"
    using assms cycle_exists.simps get_single_cycle.simps some_in_eq
    by metis
  have "get_simple_cycle G = trim_cyclical_path (get_single_cycle G)"
    by simp
  then show ?thesis
    using all_simple_cycles_def single_cycle_def
    by auto
qed

lemma simple_cycle_subset:
  assumes "cycle_exists G"
  shows"set(get_simple_cycle G) \<subseteq> all_arcs_in_cycles G"
proof -
  have "get_simple_cycle G \<in> all_simple_cycles G"
    using assms simple_cycle_other_def
    by metis
  then show ?thesis
    using all_arcs_in_cycles_def Union_upper rev_image_eqI
    by metis
qed




lemma single_cycle_non_distinct:
  assumes "cycle_exists G"
  shows "distinct (get_single_cycle G) = False"
proof -
  have not_empty:"get_cyclical_walks G \<noteq> {}"
    using assms
    by simp
  then have single_cycle_in_cycles:"(get_single_cycle G)\<in>(get_cyclical_walks G)"
    using some_in_eq get_single_cycle.simps
    by metis
  have "\<forall>x\<in>(get_cyclical_walks G). distinct x = False"
    by simp
  then show "distinct (get_single_cycle G) = False"
    using single_cycle_in_cycles 
    by simp 
qed

lemma single_cycle_non_empty:
  assumes cycle:"cycle_exists G"
  shows "(get_single_cycle G) \<noteq> []"
proof -
  have not_empty:"get_cyclical_walks G \<noteq> {}"
    using cycle
    by simp
  then have single_cycle_in_cycles:"(get_single_cycle G)\<in>(get_cyclical_walks G)"
    using some_in_eq get_single_cycle.simps
    by metis
  then have "distinct (get_single_cycle G) = False"
    by simp
  then show "(get_single_cycle G) \<noteq> []"
    by auto
qed


lemma single_cycle_in_arcs:
  assumes cycle:"cycle_exists G"
  shows "set (get_single_cycle G) \<subseteq> arcs G"
proof -
  have not_empty:"get_cyclical_walks G \<noteq> {}"
    using cycle
    by auto
  have single_cycle_in_cycles:"(get_single_cycle G)\<in>(get_cyclical_walks G)"
    using get_single_cycle.simps not_empty some_in_eq
    by metis
  then have "path G (get_single_cycle G)"
    by simp
  then show "set (get_single_cycle G) \<subseteq> arcs G"
    using path_in_graph
    by metis
qed


lemma get_simple_cycle_in_arcs:
assumes cycle:"cycle_exists G"
shows "set (get_simple_cycle G) \<subseteq> arcs G"
proof (rule subsetI)
  fix x
  assume x_in_cycle:"x \<in> set (get_simple_cycle G)"
  have simple_in_single:"set (get_simple_cycle G) \<subseteq> set (get_single_cycle G)"
    using trim_cyc_subset
    by simp
  then have single_in_arcs:"set (get_single_cycle G) \<subseteq> arcs G"
    using single_cycle_in_arcs cycle
    by simp
  then have x_in_arcs: "x \<in> arcs G"
    using single_in_arcs x_in_cycle simple_in_single 
    by auto
  show "x \<in> arcs G"
    by (rule x_in_arcs)
qed


lemma condorcet_not_in_cycle:
  assumes "in_arcs G c = {}"
  assumes "cycle_exists G"
  shows "(all_arcs_in_cycles G) \<inter> out_arcs G c = {}"
proof -
  have "\<forall>x\<in>all_simple_cycles G. \<exists>y\<in>get_cyclical_walks G. x=trim_cyclical_path y"
    using  all_simple_cycles_def image_iff
    by metis
  then have "\<forall>x\<in>all_simple_cycles G. \<exists>y\<in>get_cyclical_walks G. 
    (x=trim_cyclical_path y) \<and> path G y"
    using get_cyclical_walks.simps
    by simp
  then have "\<forall>x\<in>all_simple_cycles G. set x \<inter> out_arcs G c = {}"
    using  no_in_arcs_no_head assms empty_set inf_bot_right inf_commute path.elims(2) subset_empty trim_cyc_subset
    by (smt (verit))
  then show ?thesis
    using all_arcs_in_cycles_def Union_disjoint image_iff
    by (smt (verit, best))
qed

subsection \<open>Finding the arc with the smallest weight in a cycle\<close>

text\<open>
  This function serves to find the elements in a list with minimum weight
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
          using False Un_empty_left assm
          by (smt (verit, ccfv_SIG))
        then show ?thesis 
          using Cons.IH
          by fastforce
      qed
  qed
qed

lemma min_elems_empty_list:
  shows "min_elems xs f c p = {} \<longrightarrow> xs = []"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume IH:"min_elems xs f c p = {} \<longrightarrow> xs = []"
  then have "min_elems (a#xs) f c p \<subseteq> {a} \<union> min_elems xs f c p"
    by auto
  then show "min_elems (a#xs) f c p = {} \<longrightarrow> (a#xs) = []" using IH by auto
qed
  
lemma smallest_arcs_nonempty:
  assumes Cycle:"cycle_exists G"
  shows "min_elems (get_simple_cycle G) f c p \<noteq> {}"
proof -
  have first_step:"get_single_cycle G \<noteq> []"
    using Cycle single_cycle_non_empty
    by metis 
  have second_step:"get_simple_cycle G \<noteq> []"
    using first_step trim_cyc_nonempty
    by simp
  show "min_elems (get_simple_cycle G) f c p \<noteq> {}"
    using second_step min_elems_empty_list
    by metis
qed

lemma smallest_arcs_in_graph:
  assumes "cycle_exists G"
  shows "min_elems (get_simple_cycle G) f c p \<subseteq> arcs G"
proof
  fix x
  assume "x \<in> min_elems (get_simple_cycle G) f c p"
  then have "x \<in> set (get_simple_cycle G)" using min_elems_in_set by blast
  then show "x \<in> arcs G" using assms get_simple_cycle_in_arcs by blast
qed

end