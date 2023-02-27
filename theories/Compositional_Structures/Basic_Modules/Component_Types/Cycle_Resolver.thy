section \<open>Cycle_Resolver\<close>

theory Cycle_Resolver
  imports
          "Graph_Theory/Cycle_Helper"
begin

text\<open>
\<close>

type_synonym 'a Cycle_Resolver = 
"'a Margin_Graph \<Rightarrow> 'a Weight_Function \<Rightarrow> 'a Profile \<Rightarrow>'a Margin_Graph"

text\<open>
  These functions are actually important
\<close>

fun resolve_cycle::"('a*'a) list\<Rightarrow>'a Margin_Graph \<Rightarrow> 'a Weight_Function \<Rightarrow>  'a Profile \<Rightarrow>('a, ('a*'a)) pre_digraph" where
"resolve_cycle cyc G f p = 
\<lparr>verts = verts G, arcs = arcs G - 
(min_elems cyc f (verts G) p),
tail=tail G, head=head G\<rparr>"

fun resolve_one_cycle ::"'a Cycle_Resolver" where
"resolve_one_cycle G f p = resolve_cycle (get_simple_cycle G) G f p"

lemma resolve_cycle_strictly_decreases_arcs:
  assumes "cycle_exists G"
  shows "(arcs G) \<supset> (arcs (resolve_one_cycle G f p))"
proof -
  have min_elems_in_arcs: "min_elems (get_simple_cycle G) f (verts G) p \<subseteq> arcs G"
    using smallest_arcs_in_graph assms by simp
  have getSimpleCycle_in_arcs: "set (get_simple_cycle G) \<subseteq> arcs G"
    using get_simple_cycle_in_arcs assms by simp
  have removed_at_least_one_arc: "min_elems (get_simple_cycle G) f (verts G) p \<noteq> {}"
    using smallest_arcs_nonempty assms
    by blast
  have is_subset:"(arcs G) \<supset> (arcs G - min_elems (get_simple_cycle G) f (verts G) p)"
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
  have "arcs(resolve_one_cycle G f p) = arcs G - min_elems (get_simple_cycle G) f (verts G) p"
    by simp
  have min_in_simp:"min_elems (get_simple_cycle G) f (verts G) p \<subseteq> set(get_simple_cycle G)"
    using min_elems_in_set
    by metis
  then have "set(get_simple_cycle G) \<subseteq> (all_arcs_in_cycles G)"
    using simple_cycle_subset assms
    by metis
  then show ?thesis
    using min_in_simp resolve_cycle_strictly_decreases_arcs
    by auto 
qed

lemma resolve_one_cycle_keeps_x:
  assumes "cycle_exists G" "finite (arcs G)" "x \<in> arcs G" "x \<notin> all_arcs_in_cycles G"
  shows "x \<in> arcs (resolve_one_cycle G f p)"
proof -
  have "arcs(resolve_one_cycle G f p) = arcs G - min_elems (get_simple_cycle G) f (verts G) p"
    by simp
  have min_in_simp:"min_elems (get_simple_cycle G) f (verts G) p \<subseteq> set(get_simple_cycle G)"
    using min_elems_in_set
    by metis
  then have "set(get_simple_cycle G) \<subseteq> (all_arcs_in_cycles G)"
    using simple_cycle_subset assms
    by metis
  then have "x\<notin>min_elems (get_simple_cycle G) f (verts G) p"
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
  = arcs G - (arcs G - (min_elems (get_simple_cycle G) f (verts G) p))"
    by simp
  then have diff:"arcs G - arcs (resolve_one_cycle G f p) 
  = (min_elems (get_simple_cycle G) f (verts G) p)"
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
  \<subseteq> (arcs G - (min_elems (get_simple_cycle G) f (verts G) p))"
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
