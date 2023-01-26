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

fun findSmallestArc :: "'a Weight_Function \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> ('a*'a) list \<Rightarrow>('a*'a)" where
"findSmallestArc f c p [x] = x" |
"findSmallestArc f c p (x#y#zs) = 
  (let m = findSmallestArc f c p (y#zs) in if f c p x \<le> f c p m then x else m)"

fun findArcsWithSameLength :: "('a*'a)\<Rightarrow>('a*'a) list\<Rightarrow>'a Weight_Function \<Rightarrow> 
  'a set \<Rightarrow> 'a Profile \<Rightarrow>('a*'a) set" where
"findArcsWithSameLength a l f c p= {x.(x\<in>set l) \<and> f c p x = f c p a}"

fun findSmallestArcs:: "'a Weight_Function \<Rightarrow> 'a set \<Rightarrow> 'a Profile \<Rightarrow> ('a*'a) list
   \<Rightarrow> ('a*'a) set" where
"findSmallestArcs f c p l = findArcsWithSameLength(findSmallestArc f c p l) l f c p"

fun resolveOneCycle ::"('a,('a*'a)) Cycle_Resolver" where
"resolveOneCycle G f p = (let cyc = getSimpleCycle G in 
\<lparr>verts = verts G, arcs = arcs G - 
(findSmallestArcs f (verts G) p cyc),
tail=tail G, head=head G\<rparr>)"

lemma[simp]: "cycleExists G \<Longrightarrow> getCyclicalWalks G \<noteq> {}"
  by auto

lemma[simp]: " getCyclicalWalks G \<noteq> {}\<Longrightarrow>\<exists>x. getSimpleCycle G = x "
  by auto
(*
lemma "getSimpleCycle G \<noteq> [] \<equiv>findSmallestArcs f (verts G) p (getSimpleCycle G) \<noteq>{}"
  by auto  

lemma Cycle_Resolver.resolveOneCycle.cases: (\<And>G f p. ?x = (G, f, p) \<Longrightarrow> ?P) \<Longrightarrow> ?P
  Product_Type.prod_cases3: (\<And>a b c. ?y = (a, b, c) \<Longrightarrow> ?thesis) \<Longrightarrow> ?thesis
*)            

lemma resolving_reduces_arcs[simp]: "(arcs (resolveOneCycle G f p)) \<subseteq> (arcs G)"
  using Diff_subset resolveOneCycle.simps select_convs(2)
  by metis

function (sequential) resolveAllCycles::"('a, ('a*'a)) Cycle_Resolver" where
"resolveAllCycles G f p= (if cycleExists G 
  then resolveAllCycles (resolveOneCycle G f p)f p else G)"
  by pat_completeness auto

termination
proof-
  show ?thesis
    using resolving_reduces_arcs
    sorry
qed


lemma 
  assumes "cycleExists G"
  shows "arcs G \<noteq> {}"
proof -
  show ?thesis
using no_arcs_no_cycle
    by (metis (full_types) assms no_arcs_no_cycle old.unit.exhaust surjective)
qed
    

(*
lemma " \<And>G x. length x \<le> card (verts G) \<Longrightarrow>
           legitPath G x \<Longrightarrow> \<not> distinct x \<Longrightarrow> False"
  by simp

  


lemma "resolveAllCycles \<lparr> verts = v, arcs = {},tail = t, head = h\<rparr>
 = \<lparr> verts = v, arcs = {},tail = t, head = h\<rparr>"
  
*)


(*
lemma "cycleExists G \<equiv> getCycle G \<noteq>[]"

  by simp

lemma "\<not>distinct [] = False"
  by auto

lemma "a\<in>(getCyclicalWalks G)\<longrightarrow>(set a)\<subseteq>arcs G"

by auto
*)
end


