section \<open>Margin-Graph-Creator\<close>

theory Margin_Graph_Creator
  imports "Graph_Theory.Digraph" 
          "Social_Choice_Types/Profile"
begin

text\<open>
  The Margin Graph Creator takes a profile and a weight function and returns a graph.
  A weight function assigns an arc a natural number based on a profile. We call
  this number the arc's weight.
  The Margin Graph Creator first creates a graph with all candidates as vertices
  connected to each other.
  Then all arcs with a weight of 0 get deleted.
\<close>

type_synonym 'a Weight_Function = "'a set \<Rightarrow> 'a Profile \<Rightarrow> ('a*'a) \<Rightarrow> nat"
type_synonym 'a Margin_Graph_Creator = "'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Weight_Function \<Rightarrow> ('a, ('a*'a)) pre_digraph"


fun getArcs::"'a set \<Rightarrow>  ('a*'a) set" where
"getArcs A = {(u,v). (u,v)\<in>(A\<times>A) \<and> (u\<noteq>v)}"

fun createFullGraph::"'a set \<Rightarrow> ('a, ('a*'a)) pre_digraph" where
"createFullGraph A = (| verts = A, arcs = getArcs A, tail = fst, head = snd |)"

fun deleteEmptyEdges::"('a, ('a*'a)) pre_digraph \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> 'a Weight_Function \<Rightarrow> ('a, ('a*'a)) pre_digraph"
  where "deleteEmptyEdges G a p f = 
(| verts = verts G, arcs = {(u,v)\<in>arcs G.(f a p (u,v))\<noteq>0} , tail = tail G, head = head G |)"

fun createMarginGraph::"'a Margin_Graph_Creator" where
"createMarginGraph a p f = deleteEmptyEdges (createFullGraph a) a p f"


lemma "getArcs {0} = {}" 
  by auto

lemma "getArcs {0::nat,1} = {(0,1),(1,0)}"
  by auto

lemma "verts (createMarginGraph a p f) = a"
  by auto



(*
export_code getArcs in Scala
module_name Arcs file_prefix example


lemma "profile {} [{(Suc 0,2::nat)}] = false" (*Liste von Menge von Tupel*)
  by auto
*)
end


