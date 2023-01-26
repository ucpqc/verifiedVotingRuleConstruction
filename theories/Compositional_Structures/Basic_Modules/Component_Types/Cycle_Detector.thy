section \<open>Cycle_Detector\<close>

theory Cycle_Detector
  imports "Graph_Theory.Digraph" 
          "Graph_Theory.Arc_Walk" 
          "Social_Choice_Types/Profile"
begin

text\<open>
\<close>

type_synonym ('a, 'b) Cycle_Detector = "('a, 'b) pre_digraph \<Rightarrow> bool"

(*
fun legitPath ::"('a, 'b) pre_digraph \<Rightarrow> 'a \<Rightarrow> 'b awalk \<Rightarrow> 'a \<Rightarrow> bool" where
"legitPath G u [] v = ((u = v) \<and> u\<in>(verts G))" |
"legitPath G u (e # es) v = (e\<in>(arcs G)\<and> u\<in>(verts G)\<and> v\<in>(verts G)\<and> tail G e = u \<and> legitPath G (head G e) es v)"
*)

fun legitPath ::"('a, 'b) pre_digraph \<Rightarrow> 'b awalk \<Rightarrow> bool" where
"legitPath G [] = False" |
"legitPath G [e] = (e\<in>(arcs G) \<and> head G e \<noteq> tail G e)" |
"legitPath G (e # (f # es))= (e\<in>(arcs G) \<and> head G e \<noteq> tail G e \<and> (head G e) =
 (tail G f)\<and> legitPath G (f#es))"

fun getCyclicalWalks::"('a, 'b) pre_digraph \<Rightarrow> 'b awalk set" where
"getCyclicalWalks G = {walk.(legitPath G walk)\<and> (length walk \<le> card(verts G)) \<and> \<not>(distinct walk)}"

(*
fun getAllPaths::"('a, 'b) pre_digraph \<Rightarrow> 'b awalk set" where
"getAllPaths G = []"
*)

fun cycleExists::"('a, 'b) Cycle_Detector" where
"cycleExists G = (getCyclicalWalks G  \<noteq> {})"

lemma "legitPath G [a] \<longrightarrow> a \<in> arcs G"
  by auto

lemma "legitPath G (e # es) \<longrightarrow> e\<in>arcs G"
  using legitPath.elims(2) by blast
  
(*
lemma "legitPath G p \<and> a\<in>(set p) \<longrightarrow> a\<in>arcs G"


lemma legitPathInGraph[code]: 
  fixes  G :: "('a, 'b) pre_digraph" and
    a :: "'b" and
    p :: "'b awalk"
  shows "legitPath G p \<and> a\<in>set p \<longrightarrow> a\<in>arcs G"
proof (induction p rule: rev_induct, simp)
  case (Nil)
  have oneArc:"legitPath G [x] \<and> a\<in>set [x] \<longrightarrow> a\<in>arcs G"
    by auto
  case (snoc x xs)
  have head:"legitPath G (e # es) \<longrightarrow> e\<in>arcs G"
    by auto*)

lemma[simp]: "legitPath \<lparr>verts = v, arcs = {}, tail = t, head = h\<rparr> x = False"
  using legitPath.elims(1) by force

lemma no_arcs_no_cycle[simp]: "cycleExists \<lparr> verts = v, arcs = {},tail = t, head = h\<rparr> = False"
  by simp
(*
lemma "b\<in>(getCyclicalWalks G)\<and>a\<in>(set b) \<longrightarrow> a\<in>(arcs G)"
  
  by auto


lemma "getCyclicalWalks \<lparr>verts = {A,B,C}, arcs = {(A,B),(B,A),(A,C)},tail=fst, head=snd\<rparr> = {}"
  by auto

lemma "cycleExists \<lparr>verts = {A,B,C}, arcs = {(A,B),(B,A),(A,C)},tail=fst, head=snd\<rparr> = True"
  by auto
*)

end


