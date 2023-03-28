section \<open>Graph-Winner-Finder\<close>

theory Graph_Winner_Finder
  imports "Graph_Theory/Cycle_Helper" 
          "Social_Choice_Types/Result"
begin

text\<open>
  The Graph Winner Finder takes a margin graph and sorts all vertices 
  into one of three categories: winners, losers, and unknown/deferred.  
  It does this by determining each vertice's in- and out-degree, which is
  the number of arcs with said vertice as their head/tail.

  WARNING: It's important to use inarcs = {} instead of indegree = 0.
  Same with outdegree. This is because indegree and outdegree use card.
  And using cardinality is a cardinal sin.
  It also causes the program to fail.
\<close>

type_synonym 'a Graph_Winner_Finder = "'a Margin_Graph \<Rightarrow> 'a Result"

fun get_winners::"('a,'b) pre_digraph \<Rightarrow> 'a set" where
"get_winners G = {v::'a. v\<in>verts G \<and> in_arcs G v = {}}"

fun get_losers::"('a, 'b) pre_digraph \<Rightarrow> 'a set" where
"get_losers G = {v::'a. v\<in>verts G \<and> v\<notin>get_winners G}"

fun evaluate_graph::"'a Graph_Winner_Finder" where
"evaluate_graph G = (get_winners G, get_losers G, {})"

lemma validResult:"\<forall>G::('a,('a*'a)) pre_digraph.(well_formed (verts G) (evaluate_graph G))"
  by auto
 
lemma in_arcs_translate[simp]:"in_arcs G x \<equiv> {a \<in> arcs G. head G a = x}"
  unfolding in_arcs_def
  by simp

lemma out_arcs_translate[simp]:"out_arcs G x \<equiv> {a \<in> arcs G. tail G a = x}"
  unfolding out_arcs_def
  by simp
  
lemma winners_def:"x\<in>(get_winners G) \<equiv> x\<in>(verts G)\<and>  {a\<in>(arcs G). head G a = x}= {}"
  by simp_all




end
