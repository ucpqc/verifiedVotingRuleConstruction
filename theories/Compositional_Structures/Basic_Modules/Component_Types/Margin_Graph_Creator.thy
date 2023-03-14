section \<open>Margin-Graph-Creator\<close>

theory Margin_Graph_Creator
  imports "Graph_Theory/Cycle_Helper"
begin

text\<open>
  The Margin Graph Creator takes a profile and a weight function and returns a graph.
  A weight function assigns an arc a natural number based on a profile. We call
  this number the arc's weight.
  The Margin Graph Creator first creates a graph with all candidates as vertices
  connected to each other.
  Then all arcs with a weight of 0 get deleted.
\<close>

type_synonym 'a Margin_Graph_Creator = "'a set \<Rightarrow> 'a Profile
 \<Rightarrow> 'a Weight_Function \<Rightarrow> 'a Margin_Graph"


fun get_arcs::"'a set \<Rightarrow>  ('a*'a) set" where
"get_arcs A = {(u,v). (u,v)\<in>(A\<times>A) \<and> (u\<noteq>v)}"

fun create_full_graph::"'a set \<Rightarrow> 'a Margin_Graph" where
"create_full_graph A = (| verts = A, arcs = get_arcs A, tail = fst, head = snd |)"

fun delete_empty_edges::"'a Margin_Graph \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Weight_Function \<Rightarrow> ('a, ('a*'a)) pre_digraph"
  where "delete_empty_edges G A p f = 
(| verts = verts G, arcs = {(u,v)\<in>arcs G.(f A p (u,v))\<noteq>0} , tail = tail G, head = head G |)"

fun create_margin_graph::"'a Margin_Graph_Creator" where
"create_margin_graph A p f = delete_empty_edges (create_full_graph A) A p f"


lemma candidates_are_vertices:"verts (create_margin_graph A p f) = A"
  by simp

lemma condorcet_degree:
  assumes "\<forall>x\<in>(A - {c}). f A p (x,c) = 0 \<and> c\<in>A"
  shows "in_arcs (create_margin_graph A p f) c = {}"
proof -
  have "\<forall>x\<in>(A - {c}). (x,c)\<in>arcs (create_full_graph A)"
    using assms
    by simp
  then have "\<forall>x\<in>(A - {c}). (x,c)\<notin>arcs (delete_empty_edges (create_full_graph A) A p f)"
    using assms
    by simp
  then have "\<forall>x\<in>(A - {c}). (x,c)\<notin>arcs (create_margin_graph A p f)"
    by simp
  then have "\<forall>y\<in>(arcs (create_margin_graph A p f)). 
    (head (create_margin_graph A p f)) y \<noteq> c" 
    by auto
  then have "{e \<in> arcs (create_margin_graph A p f)
    . head (create_margin_graph A p f) e = c} = {}"
    by simp
  then show ?thesis 
    using in_arcs_def 
    by metis
qed

lemma non_condorcet_degree:
  assumes "(\<forall>x\<in>(A - {c}). f A p (c,x) > 0) \<and> c\<in>A"
  shows "\<forall>x\<in>(A - {c}). \<exists>y. y\<in>in_arcs (create_margin_graph A p f) x 
    \<and> y \<in>out_arcs (create_margin_graph A p f) c"
proof -
  have one:"c\<in>A"
    using assms by metis
  have two:"\<forall>x\<in>(A - {c}).x \<noteq> c"
    by simp
  then have "\<forall>x\<in>(A - {c}). (c,x)\<in>arcs (create_full_graph A)"
    using one
    by auto
  then have "\<forall>x\<in>(A - {c}). (c,x)\<in>arcs (delete_empty_edges (create_full_graph A) A p f)"
    using assms
    by simp
  then have "\<forall>x\<in>(A - {c}). (c,x)\<in>arcs (create_margin_graph A p f)"
    by simp
  then have "\<forall>x\<in>(A - {c}). (\<exists>y\<in>arcs (create_margin_graph A p f).
    head (create_margin_graph A p f) y = x 
    \<and> tail (create_margin_graph A p f) y = c)"
    by auto
  then show ?thesis 
    by simp
qed

lemma no_in_arcs_no_weights:
  assumes "in_arcs (create_margin_graph A p f) c = {} \<and> c \<in> A"
  shows "\<forall>x\<in>A-{c}. f A p (x,c) = 0"
proof -
  have "{e \<in> arcs (create_margin_graph A p f)
    . head (create_margin_graph A p f) e = c} = {}"
    using assms in_arcs_def
    by metis
  then have "\<forall>y\<in>(arcs (create_margin_graph A p f)). 
    (head (create_margin_graph A p f)) y \<noteq> c" 
    by auto
  then have "\<forall>y\<in>(arcs (create_margin_graph A p f)). 
    snd y \<noteq> c" 
    by auto
  then have "\<forall>x\<in>(A - {c}). (x,c)\<notin>arcs (create_margin_graph A p f)"
    using snd_conv
    by meson
  then have "\<forall>x\<in>(A - {c}). (x,c)\<notin>arcs (delete_empty_edges (create_full_graph A) A p f)"
    using assms
    by simp
  moreover have "\<forall>x\<in>(A - {c}). (x,c)\<in>arcs (create_full_graph A)"
    using assms
    by simp 
  ultimately show ?thesis 
    using delete_empty_edges.simps case_prodI mem_Collect_eq select_convs(2)
    by (metis (mono_tags, lifting))  
qed

end


