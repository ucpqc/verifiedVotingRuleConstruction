section \<open>Cycle_Resolver\<close>

theory Cycle_Resolver
  imports "Graph_Theory.Digraph" 
          "Graph_Theory.Arc_Walk" 
          "Social_Choice_Types/Profile"
          "Cycle_Detector"
          "Margin_Graph_Creator"
          "Graph_Theory/Cycle_Helper"
begin

text\<open>
\<close>

type_synonym ('a, 'b) Cycle_Resolver = 
"('a, 'b) pre_digraph \<Rightarrow> 'a Weight_Function \<Rightarrow> 'a Profile \<Rightarrow>('a, 'b) pre_digraph"

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

lemma resolveCycle_strictly_decreases_arcs:
  assumes cycle_exists: "cycleExists G"
  shows "(arcs G) \<supset> (arcs (resolveOneCycle G f p))"
proof -
  have min_elems_in_arcs: "min_elems (getSimpleCycle G) f (verts G) p \<subseteq> arcs G"
    using smallest_arcs_in_graph cycle_exists by simp
  have getSimpleCycle_in_arcs: "set (getSimpleCycle G) \<subseteq> arcs G"
    using getSimpleCycle_in_arcs cycle_exists by simp
  have removed_at_least_one_arc: "min_elems (getSimpleCycle G) f (verts G) p \<noteq> {}"
    using smallest_arcs_nonempty cycle_exists
    by blast
  have is_subset:"(arcs G) \<supset> (arcs G - min_elems (getSimpleCycle G) f (verts G) p)"
    using removed_at_least_one_arc min_elems_in_arcs
    by auto
  have is_also_subset: "(arcs G) \<supset> (arcs (resolveCycle (getSimpleCycle G) G f p))"
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

lemma resolveCycle_reduces_card:
  assumes
    cycle_exists: "cycleExists G" and
    finite_arcs: "finite (arcs G)"
  shows "card (arcs G) > card (arcs (resolveOneCycle G f p))"
proof-
  have "arcs G \<supset> arcs (resolveOneCycle G f p)"
    using resolveCycle_strictly_decreases_arcs cycle_exists
    by simp
  then have "card (arcs G) > card (arcs (resolveOneCycle G f p))"
    using finite_arcs strict_card_subset
    by simp
  then show ?thesis
    by auto
qed
     

function (sequential) resolveAllCycles::"('a, ('a*'a)) Cycle_Resolver" where
"resolveAllCycles G f p= (if (cycleExists G \<and> finite (arcs G))
  then resolveAllCycles (resolveOneCycle G f p)f p else G)"
  by pat_completeness auto
termination 
  apply (relation "(measure (\<lambda> (G, f, p). card (arcs G)))")
   apply auto
 using resolveCycle_reduces_card strict_card_subset
  apply simp
  apply auto
  done

end
