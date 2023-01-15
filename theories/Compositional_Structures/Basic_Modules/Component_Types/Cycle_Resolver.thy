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

fun trim::"'b awalk \<Rightarrow> 'b awalk" where
"trim [] = []" |
"trim (e # es) = (if distinct es then (e#es) else trim es)"

fun trimCyclicalPath::"'b awalk \<Rightarrow> 'b awalk" where
"trimCyclicalPath path = trim(rev(trim path))" 

fun getSimpleCycle::"('a,('a*'a)) pre_digraph \<Rightarrow> ('a*'a) awalk" where
"getSimpleCycle G = trimCyclicalPath (SOME x. x \<in> getCyclicalWalks G)"
(*
fun getCycle::"('a,('a*'a)) pre_digraph \<Rightarrow> ('a*'a) awalk" where
"getCycle G = (SOME x. x \<in> getCyclicalWalks G)"
*)


fun findSmallestArc :: "'a Weight_Function \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> ('a*'a) list \<Rightarrow>('a*'a)" where
"findSmallestArc f c p [x] = x" |
"findSmallestArc f c p (x#y#zs) = (let m = findSmallestArc f c p (y#zs) in if f c p x \<le> f c p m then x else m)"

fun findArcsWithSameLength :: "('a*'a)\<Rightarrow>('a*'a) list\<Rightarrow>'a Weight_Function \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow>('a*'a) set" where
"findArcsWithSameLength a l f c p= {x.(x\<in>set l) \<and> f c p x = f c p a}"

fun resolveOneCycle ::"('a,('a*'a)) Cycle_Resolver" where
"resolveOneCycle G f p = (let c = getSimpleCycle G in 
\<lparr>verts = verts G, arcs = arcs G - 
findArcsWithSameLength(findSmallestArc f (verts G) p c) c f (verts G) p ,
tail=tail G, head=head G\<rparr>)" 


fun resolveAllCycles::"('a, ('a*'a)) Cycle_Resolver" where
"resolveAllCycles G f p= (if cycleExists G then resolveAllCycles (resolveOneCycle G f p) f p else G)"

lemma "card (arcs G) <= card (arcs (resolveOneCycle G f p))"
  by auto

lemma "cycleExists G \<equiv> getCycle G \<noteq>[]"
  by simp

lemma "\<not>distinct [] = False"
  by auto

lemma "a\<in>(set (getCycle G))\<longrightarrow>a\<in>arcs G"
by auto

end


