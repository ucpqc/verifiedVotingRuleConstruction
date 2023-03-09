section \<open>Cycle_Resolver\<close>

theory Cycle_Resolver
  imports
          "Graph_Theory/Cycle_Helper"
begin

text\<open>
\<close>

type_synonym 'a Cycle_Resolver = 
"'a Margin_Graph \<Rightarrow> 'a Weight_Function \<Rightarrow> 'a Profile \<Rightarrow>'a Margin_Graph"

subsection \<open>Finding the arc with the smallest weight in a cycle\<close>

text\<open>
  This function serves to find the elements in a list with minimum weight
\<close>

fun min_elems ::  "'a Weight_Function \<Rightarrow> 'a set 
  \<Rightarrow> 'a Profile  \<Rightarrow> ('a*'a) list \<Rightarrow> ('a*'a) set" where
"min_elems f c p [] = {}" |
"min_elems f c p (x#xs)= (if (\<forall> y \<in> set xs. f c p y \<ge> f c p x) then {x} 
else {}) \<union> min_elems f c p xs"

lemma min_elems_in_set:
shows "(min_elems f c p l) \<subseteq> set l"
proof
  fix x
  assume "x \<in> min_elems f c p l"
  thus "x \<in> set l"
  proof (induction l)
    case Nil
    then show ?case 
      by auto
  next
    case (Cons a l')
    then have "x \<in> min_elems f c p (a # l')"
      by simp
    then have assm:"x \<in> (if (\<forall> y \<in> set l'. f c p y \<ge> f c p a) then {a} else {}) \<union> min_elems f c p l'"
      by simp 
    then show ?case 
      proof (cases "\<forall> y \<in> set l'. f c p y \<ge> f c p a")
        case True
        then have either: "x \<in> ({a} \<union> min_elems f c p l')" 
          using assm
          by simp
        then have "a \<in> set (a # l')"
          by auto
        then show ?thesis 
          using Cons.IH either
          by fastforce
      next
        case False
        then have "x \<in> min_elems  f c p l'"
          using False Un_empty_left assm
          by (smt (verit, ccfv_SIG))
        then show ?thesis 
          using Cons.IH
          by fastforce
      qed
  qed
qed

lemma min_elems_empty_list:
  shows "min_elems f c p xs = {} \<longrightarrow> xs = []"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  assume IH:"min_elems f c p xs = {} \<longrightarrow> xs = []"
  then have "min_elems f c p (a#xs) \<subseteq> {a} \<union> min_elems f c p xs"
    by auto
  then show "min_elems f c p (a#xs) = {} \<longrightarrow> (a#xs) = []" using IH by auto
qed
  
lemma smallest_arcs_nonempty:
  assumes "cycle_exists G"
  shows "min_elems f c p (get_simple_cycle G) \<noteq> {}"
proof -
  have first_step:"get_single_cycle G \<noteq> []"
    using assms single_cycle_non_empty
    by metis 
  have second_step:"get_simple_cycle G \<noteq> []"
    using first_step trim_cyc_nonempty
    by simp
  show ?thesis
    using second_step min_elems_empty_list
    by metis
qed

lemma smallest_arcs_in_graph:
  assumes "cycle_exists G"
  shows "min_elems f c p (get_simple_cycle G) \<subseteq> arcs G"
proof
  fix x
  assume "x \<in> min_elems f c p (get_simple_cycle G)"
  then have "x \<in> set (get_simple_cycle G)" using min_elems_in_set by blast
  then show "x \<in> arcs G" using assms get_simple_cycle_in_arcs by blast
qed


definition min_arcs::"'a Margin_Graph \<Rightarrow> 'a Weight_Function \<Rightarrow> 'a set 
\<Rightarrow> 'a Profile \<Rightarrow> ('a*'a) set" where
"min_arcs G f c p = \<Union> (min_elems f c p ` (all_simple_cycles G))"

lemma min_arcs_in_cyc_arcs:"min_arcs G f c p \<subseteq> all_arcs_in_cycles G"
proof -
  show ?thesis
  using min_elems_in_set all_arcs_in_cycles_def Sup_mono image_iff min_arcs_def
  by (smt (verit))
qed


lemma min_arcs_steadfast:
  assumes "arcs H=arcs G - X""verts H=verts G""head H=head G""tail H=tail G""path H w"
  assumes "X = min_elems f c p (get_simple_cycle G)"
  shows "min_arcs H f c p= min_arcs G f c p - X"
proof -
  have "\<forall>a\<in>min_arcs G f c p - X. \<exists>cyc\<in>all_simple_cycles H. 
    a\<in>min_elems f c p  cyc"
    sorry
  then have dir1:"min_arcs H f c p \<supseteq> min_arcs G f c p - X"
    using min_arcs_def
    by blast
  have "get_cyclical_walks H \<subseteq> get_cyclical_walks G"
    using Diff_subset assms(1) assms(2) assms(3) assms(4) less_arcs_less_cycles
    by metis
  then have "min_arcs H f c p \<subseteq> min_arcs G f c p"
    using all_simple_cycles_def min_arcs_def Union_mono image_mono
    by metis
  moreover have "X \<inter> min_arcs H f c p = {}"
    using assms(1) min_arcs_in_cyc_arcs cyc_arc_still_arc
    by fastforce
  ultimately have dir2:"min_arcs H f c p \<subseteq> min_arcs G f c p - X"
    by auto
  then show ?thesis
    using dir1 dir2
    by simp
qed

  
fun resolve_cycle::"('a*'a) list\<Rightarrow>'a Margin_Graph \<Rightarrow> 'a Weight_Function \<Rightarrow>  'a Profile \<Rightarrow>('a, ('a*'a)) pre_digraph" where
"resolve_cycle cyc G f p = 
\<lparr>verts = verts G, arcs = arcs G - 
(min_elems f (verts G) p cyc),
tail=tail G, head=head G\<rparr>"

fun resolve_one_cycle ::"'a Cycle_Resolver" where
"resolve_one_cycle G f p = resolve_cycle (get_simple_cycle G) G f p"

lemma resolve_cycle_strictly_decreases_arcs:
  assumes "cycle_exists G"
  shows "(arcs G) \<supset> (arcs (resolve_one_cycle G f p))"
proof -
  have min_elems_in_arcs: "min_elems f (verts G) p (get_simple_cycle G) \<subseteq> arcs G"
    using smallest_arcs_in_graph assms by simp
  have getSimpleCycle_in_arcs: "set (get_simple_cycle G) \<subseteq> arcs G"
    using get_simple_cycle_in_arcs assms by simp
  have removed_at_least_one_arc: "min_elems f (verts G) p (get_simple_cycle G) \<noteq> {}"
    using smallest_arcs_nonempty assms
    by blast
  have is_subset:"(arcs G) \<supset> (arcs G - min_elems f (verts G) p (get_simple_cycle G))"
    using removed_at_least_one_arc min_elems_in_arcs
    by auto
  have is_also_subset: "(arcs G) \<supset> (arcs (resolve_cycle (get_simple_cycle G) G f p))"
    using is_subset
    by auto
  then show ?thesis
  using is_also_subset
  by simp
qed

lemma strict_card_subset:
  assumes 
    subset:"a \<subset> b" and
    finite_b: "finite b"
  shows "card a < card b"
      using psubset_card_mono subset finite_b
      by blast 

lemma resolve_cycle_reduces_card:
  assumes
    cycle_exists: "cycle_exists G" and
    finite_arcs: "finite (arcs G)"
  shows "card (arcs G) > card (arcs (resolve_one_cycle G f p))"
proof-
  have "arcs G \<supset> arcs (resolve_one_cycle G f p)"
    using resolve_cycle_strictly_decreases_arcs cycle_exists
    by simp
  then have "card (arcs G) > card (arcs (resolve_one_cycle G f p))"
    using finite_arcs strict_card_subset
    by simp
  then show ?thesis
    by auto
qed 

lemma termination_helper:
  assumes 
    cycle_exists: "cycle_exists G \<and> finite (arcs G)" 
  shows "((resolve_one_cycle G f p, f, p), G, f, p)
       \<in> measure (\<lambda>(G, f, p). card (arcs G))"
  using cycle_exists resolve_cycle_reduces_card
  by auto



function resolve_all_cycles::"'a Cycle_Resolver" where
"resolve_all_cycles G f p= (if (cycle_exists G \<and> finite (arcs G))
  then resolve_all_cycles (resolve_one_cycle G f p)f p else G)"
  by pat_completeness auto
termination  
  using resolve_cycle_reduces_card strict_card_subset termination_helper
  by (relation "(measure (\<lambda> (G, f, p). card (arcs G)))") blast 

lemma no_cycles_after_resolving:
  assumes "finite (arcs G)"
  shows "\<not>cycle_exists (resolve_all_cycles G f p)"
proof (cases "cycle_exists G \<and> finite (arcs G)")
  case True
  then show ?thesis
  proof (induction G f p rule: resolve_all_cycles.induct)
    case (1 G f p)
    then show ?case
      using  order_less_imp_le resolve_all_cycles.simps resolve_cycle_strictly_decreases_arcs rev_finite_subset
      by metis
  qed
next 
  case False
  then have "\<not>cycle_exists G \<or> \<not>finite (arcs G)"
    by simp
  then have no_cyc:"\<not>cycle_exists G" using assms
    by simp
  then have "(resolve_all_cycles G f p) = G"
    using resolve_all_cycles.simps
    by simp
  then show ?thesis 
    using no_cyc
    by metis
qed

lemma tail_equal[simp]:"tail G = tail (resolve_one_cycle G f p)" by simp

lemma resolve_cycle_preserves_verts:"verts G = verts (resolve_all_cycles G f p)" 
proof (cases "cycle_exists G \<and> finite (arcs G)")
  case True
  have IH: "verts G = verts (resolve_all_cycles G f p)"
    by (induction G f p rule: resolve_all_cycles.induct) simp
  then show ?thesis
    by blast
next
  case False
  then have "(resolve_all_cycles G f p) = G"
    using resolve_all_cycles.simps
    by meson
  then show ?thesis by metis
qed

lemma arcs_subset:
shows "arcs (resolve_all_cycles G f p) \<subseteq> arcs G"
proof (cases "cycle_exists G \<and> finite (arcs G)")
  case True
  then show ?thesis
  proof (induction rule:resolve_all_cycles.induct)
    case (1 G f p)
    then show ?case
      using dual_order.strict_trans2 psubsetE resolve_all_cycles.simps resolve_cycle_strictly_decreases_arcs
      by (metis (no_types, opaque_lifting))  
  qed
next
  case False
  then have "arcs (resolve_all_cycles G f p) = arcs G"
    using resolve_all_cycles.simps
    by metis
  then show ?thesis by simp
qed

lemma resolve_one_cycle_preserves_non_cycle_arcs:
  assumes "cycle_exists G"
  shows "arcs G - arcs(resolve_one_cycle G f p) \<subseteq> (all_arcs_in_cycles G)"
proof -
  have "arcs(resolve_one_cycle G f p) = arcs G - min_elems f (verts G) p (get_simple_cycle G)"
    by simp
  have min_in_simp:"min_elems f (verts G) p (get_simple_cycle G) \<subseteq> set(get_simple_cycle G)"
    using min_elems_in_set
    by metis
  then have "set(get_simple_cycle G) \<subseteq> (all_arcs_in_cycles G)"
    using simple_cycle_subset assms
    by metis
  then show ?thesis
    using min_in_simp resolve_cycle_strictly_decreases_arcs
    by auto 
qed

lemma resolve_one_cycle_preserves_non_min_arcs:
  assumes "cycle_exists G"
  shows "arcs G - arcs(resolve_one_cycle G f p) \<subseteq> (min_arcs G f (verts G) p)"
proof -
  have "arcs(resolve_one_cycle G f p) = arcs G - min_elems f (verts G) p (get_simple_cycle G)"
    by simp
  then show ?thesis
    using min_arcs_def Sup_upper assms double_diff image_eqI order_refl simple_cycle_other_def smallest_arcs_in_graph
    by metis
qed

lemma resolve_one_cycle_reduces_min_arcs:
  assumes "cycle_exists G"
  shows "arcs G - arcs(resolve_one_cycle G f p) = (min_arcs G f (verts G) p) 
    - min_arcs (resolve_one_cycle G f p) f (verts (resolve_one_cycle G f p)) p "
proof -
  have A:"arcs G - arcs(resolve_one_cycle G f p) \<subseteq> (min_arcs G f (verts G) p) 
    - min_arcs (resolve_one_cycle G f p) f (verts (resolve_one_cycle G f p)) p"
  proof -
    have 1:"arcs G - arcs(resolve_one_cycle G f p) \<subseteq> (min_arcs G f (verts G) p)"
      using assms resolve_one_cycle_preserves_non_min_arcs
      by simp
    have 2:"min_arcs (resolve_one_cycle G f p) f (verts (resolve_one_cycle G f p)) p
      \<subseteq> arcs(resolve_one_cycle G f p)"
      using min_arcs_in_cyc_arcs cyc_arc_still_arc dual_order.trans
      by metis
    then show ?thesis
      using 1 2
      by auto
  qed
  have B:"arcs G - arcs(resolve_one_cycle G f p) \<supseteq> (min_arcs G f (verts G) p) 
    - min_arcs (resolve_one_cycle G f p) f (verts (resolve_one_cycle G f p)) p"
    sorry
  then show ?thesis
    using A B 
    by simp
qed

lemma resolve_one_cycle_keeps_x:
  assumes "cycle_exists G" "finite (arcs G)" "x \<in> arcs G" "x \<notin> all_arcs_in_cycles G"
  shows "x \<in> arcs (resolve_one_cycle G f p)"
proof -
  have "arcs(resolve_one_cycle G f p) = arcs G - min_elems f (verts G) p (get_simple_cycle G)"
    by simp
  have min_in_simp:"min_elems f (verts G) p (get_simple_cycle G) \<subseteq> set(get_simple_cycle G)"
    using min_elems_in_set
    by metis
  then have "set(get_simple_cycle G) \<subseteq> (all_arcs_in_cycles G)"
    using simple_cycle_subset assms
    by metis
  then have "x\<notin>min_elems f (verts G) p (get_simple_cycle G)"
    using assms(4) min_in_simp
    by auto
  then show ?thesis
    using assms(3)
    by simp
qed

lemma helper:
  assumes "cycle_exists G \<and> finite(arcs G)"
  shows "arcs G - arcs (resolve_one_cycle G f p) \<subseteq> 
  all_arcs_in_cycles G - all_arcs_in_cycles (resolve_one_cycle G f p)"
proof -
  have "arcs (resolve_one_cycle G f p) 
  = arcs (resolve_cycle (get_simple_cycle G) G f p)"
    by simp
  then have start:"arcs G - arcs (resolve_one_cycle G f p) 
  = arcs G - (arcs G - (min_elems f (verts G) p (get_simple_cycle G)))"
    by simp
  then have diff:"arcs G - arcs (resolve_one_cycle G f p) 
  = (min_elems f (verts G) p (get_simple_cycle G))"
    using double_diff equalityE smallest_arcs_in_graph assms
    by metis
  then have middle:"arcs G - arcs (resolve_one_cycle G f p) \<subseteq> all_arcs_in_cycles G"
    using min_elems_in_set simple_cycle_subset assms
    by blast
  have "all_arcs_in_cycles (resolve_one_cycle G f p) 
  \<subseteq> arcs (resolve_one_cycle G f p)"
    using cyc_arc_still_arc
    by metis
  then have "all_arcs_in_cycles (resolve_one_cycle G f p) 
  \<subseteq> (arcs G - (min_elems f (verts G) p (get_simple_cycle G)))"
    using start
    by simp
  then show "arcs G - arcs (resolve_one_cycle G f p) \<subseteq> 
  all_arcs_in_cycles G - all_arcs_in_cycles (resolve_one_cycle G f p)" using middle diff
    by auto
qed
    
lemma helper2:
  assumes "cycle_exists G \<and> finite(arcs G)"
  shows "arcs G - all_arcs_in_cycles G \<subseteq> 
      arcs (resolve_one_cycle G f p) - all_arcs_in_cycles (resolve_one_cycle G f p)"
proof (rule subsetI)
  fix x
  assume asm:"x\<in>arcs G - all_arcs_in_cycles G"
  have "arcs G - arcs (resolve_one_cycle G f p) \<subseteq> 
    all_arcs_in_cycles G - all_arcs_in_cycles (resolve_one_cycle G f p)"
    using helper assms
    by metis                               
  then have x_here:"x\<in>arcs (resolve_one_cycle G f p)"
    using asm
    by blast
  have "all_arcs_in_cycles (resolve_one_cycle G f p) \<subseteq> all_arcs_in_cycles G"
    using less_arcs_less_cycles less_paths_less_cycles Diff_subset resolve_cycle.simps
      resolve_one_cycle.simps select_convs
    by metis
  then have x_not_here:"x\<notin>all_arcs_in_cycles (resolve_one_cycle G f p)"
    using asm
    by blast 
  show "x\<in>arcs (resolve_one_cycle G f p) - all_arcs_in_cycles (resolve_one_cycle G f p)"
    using x_here x_not_here
    by simp
qed
    

lemma resolve_all_cycles_preserves_non_cycle_arcs:
  "arcs G - arcs (resolve_all_cycles G f p) \<subseteq>  (all_arcs_in_cycles G)"
proof (cases "cycle_exists G \<and> finite (arcs G)")
  case True
  then show ?thesis
  proof (induction rule:resolve_all_cycles.induct)
    case (1 G f p)
    then have rec:"resolve_all_cycles G f p = 
      resolve_all_cycles (resolve_one_cycle G f p) f p"
      by simp 
    have IH:"arcs (resolve_one_cycle G f p) -
      arcs (resolve_all_cycles (resolve_one_cycle G f p) f p)
      \<subseteq> all_arcs_in_cycles (resolve_one_cycle G f p)"
      using Diff_cancel less_by_empty resolve_all_cycles.simps 1
      by metis
    then have sub1:"arcs (resolve_one_cycle G f p) -
      arcs (resolve_all_cycles G f p)
      \<subseteq> all_arcs_in_cycles (resolve_one_cycle G f p)"
      using rec
      by metis
    have sub2:"arcs G - arcs (resolve_one_cycle G f p) \<subseteq> 
       all_arcs_in_cycles G - all_arcs_in_cycles (resolve_one_cycle G f p)" 
      using helper 1(2)
      by simp
    then have "arcs G - all_arcs_in_cycles G \<subseteq> 
      arcs (resolve_one_cycle G f p) - all_arcs_in_cycles (resolve_one_cycle G f p)"
      using cyc_arc_still_arc helper2 1
      by simp
    then have "arcs G - arcs(resolve_all_cycles G f p) 
      - all_arcs_in_cycles (G) = {}"
      using sub1 sub2
      by blast
    then show ?case
      using sub1
      by blast
  qed
next
  case False
  then have "resolve_all_cycles G f p = G"
    using resolve_all_cycles.simps
    by metis
  then have "arcs G - arcs (resolve_all_cycles G f p) = {}"
    using Diff_cancel
    by metis
  then show ?thesis
    by blast
qed

lemma min_elems_get_resolved:
  assumes "finite (arcs G)"
  shows "(min_arcs G f (verts G) p) \<subseteq> arcs G - arcs(resolve_all_cycles G f p)"
proof (rule subsetI)
  fix x
  assume x_def:"x\<in>(min_arcs G f (verts G) p)"
  have "(min_arcs G f (verts G) p)\<subseteq>arcs G"
    using min_arcs_in_cyc_arcs cyc_arc_still_arc dual_order.trans
    by metis
  then have 1:"x\<in>arcs G"
    using x_def
    by auto
  have "(min_arcs G f (verts G) p) \<noteq> {}"
    using x_def
    by auto
  then have "all_simple_cycles G \<noteq> {}"
    using min_arcs_def
    by blast
  then have "get_cyclical_walks G \<noteq> {}"
    using all_simple_cycles_def
    by blast
  then have "cycle_exists G"
    by simp
  then have x_to_cyc:"x\<in>arcs G \<longrightarrow> cycle_exists G"
    by simp
  have 2:"x\<notin>arcs(resolve_all_cycles G f p)"
    sorry
  show "x\<in>(arcs G - arcs(resolve_all_cycles G f p))"
    using 1 2
    by simp
qed


lemma resolve_all_cycles_preserves_tail: 
"tail (resolve_all_cycles G f p) = tail G"
proof (cases "cycle_exists G \<and> finite (arcs G)")
  case True
  show ?thesis
  proof (induction rule:resolve_all_cycles.induct)
    case (1 G f p)
    then show ?case
      by simp 
  qed   
next
  case False
  then have "tail (resolve_all_cycles G f p) = tail G"
    using resolve_all_cycles.simps
    by metis
  then show ?thesis by simp
qed

lemma resolve_all_cycles_preserves_head: 
"head (resolve_all_cycles G f p) = head G"
proof (cases "cycle_exists G \<and> finite (arcs G)")
  case True
  show ?thesis
  proof (induction rule:resolve_all_cycles.induct)
    case (1 G f p)
    then show ?case
      by simp 
  qed   
next
  case False
  then have "head (resolve_all_cycles G f p) = head G"
    using resolve_all_cycles.simps
    by metis
  then show ?thesis by simp
qed


lemma resolving_in_arcs_empty: 
  assumes "in_arcs G x = {}"
  shows "in_arcs (resolve_all_cycles G f p) x = {}"
proof -
  have start:"{e \<in> arcs G. head G e = x} = {}"
    using assms in_arcs_def
    by metis
  have "arcs (resolve_all_cycles G f p) \<subseteq> arcs G"
    using arcs_subset
    by metis
  then have "{e \<in> arcs (resolve_all_cycles G f p). head (resolve_all_cycles G f p) e = x} = {}"
    using assms start resolve_all_cycles_preserves_head Collect_empty_eq subset_iff
    by (smt (verit, ccfv_SIG) )
  then show ?thesis
    using in_arcs_def
    by (metis (no_types))
qed
    

end
