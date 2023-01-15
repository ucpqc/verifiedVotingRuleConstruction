section \<open>Graph-Winner-Finder\<close>

theory Graph_Winner_Finder
  imports "Graph_Theory.Digraph" 
          "Social_Choice_Types/Result"
begin

text\<open>
  The Graph Winner Finder takes a margin graph and sorts all vertices 
  into one of three categories: winners, losers, and unknown/deferred.  
  It does this by determining each vertice's in- and out-degree, which is
  the number of arcs with said vertice as their head/tail.
\<close>


type_synonym ('a, 'b) Graph_Winner_Finder = "('a, 'b) pre_digraph \<Rightarrow> 'a Result"

fun getWinners::"('a,'b) pre_digraph \<Rightarrow> 'a set" where
"getWinners G = {v::'a. v\<in>verts G \<and> in_degree G v = 0}"

fun getLosers::"('a, 'b) pre_digraph \<Rightarrow> 'a set" where
"getLosers G = {v::'a. v\<in>verts G \<and> in_degree G v > 0 \<and> out_degree G v = 0}"

fun getDeferred::"('a, 'b) pre_digraph \<Rightarrow> 'a set" where
"getDeferred G = {v::'a. v\<in>verts G \<and> v\<notin>getWinners G \<and> v\<notin>getLosers G}"

fun evaluateGraph::"('a,'b) Graph_Winner_Finder" where
"evaluateGraph G = (getWinners G,getLosers G, getDeferred G)"

value "evaluateGraph \<lparr> verts={0::nat,1::nat,2::nat},arcs={(0,1),(1,2)}, tail = fst, head = snd \<rparr>"

lemma validResult:"\<forall>G::('a, 'b) pre_digraph.(well_formed (verts G) (evaluateGraph G))"
  by auto
  

lemma in_degree_translate[simp]:"in_degree G x \<equiv> card {a \<in> arcs G. head G a = x}"
  unfolding in_degree_def in_arcs_def
  by simp

lemma out_degree_translate[simp]:"out_degree G x \<equiv> card {a \<in> arcs G. tail G a = x}"
  unfolding out_degree_def out_arcs_def
  by simp
  
(*
lemma "\<forall>G::('a, 'b) pre_digraph.\<forall>x::'a\<in>(verts G).in_degree G x \<equiv> card {a \<in> (arcs G).(head G) a = x}"
  by auto


lemma "(card {e\<in>A. e=a} = 0) \<equiv> (\<forall>x\<in>A. x\<noteq>a)"
  unfolding card_def
  by blast
*)

lemma "x\<in>(getWinners G) \<equiv> x\<in>(verts G)\<and> card {a\<in>(arcs G). head G a = x}= 0"
  by simp_all

lemma "x\<in>(getLosers G) \<equiv> x\<in>(verts G) \<and> card {a\<in>(arcs G). head G a = x} > 0 \<and> card {b\<in>(arcs G). tail G b = x} = 0"
  by simp_all



end
