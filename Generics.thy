theory Generics
  imports Graph Morphism "HOL-Library.Countable"
begin

type_synonym ('l,'m) ngraph = "(nat,nat,'l,'m) pre_graph"

definition to_ngraph :: "('v::countable,'e :: countable,'l,'m) pre_graph \<Rightarrow> ('l,'m) ngraph" where
\<open>to_ngraph G \<equiv> \<lparr>nodes = to_nat ` V\<^bsub>G\<^esub>, edges = to_nat ` E\<^bsub>G\<^esub>
  , source= \<lambda>e. to_nat (s\<^bsub>G\<^esub> (from_nat e)), target = \<lambda>e. to_nat (t\<^bsub>G\<^esub> (from_nat e))
  , node_label = \<lambda>v. l\<^bsub>G\<^esub> (from_nat v), edge_label = \<lambda>e. m\<^bsub>G\<^esub> (from_nat e)\<rparr>\<close>

definition from_ngraph :: " ('l,'m) ngraph \<Rightarrow> ('v::countable,'e :: countable,'l,'m) pre_graph" where
\<open>from_ngraph G \<equiv> \<lparr>nodes = from_nat ` V\<^bsub>G\<^esub>, edges = from_nat ` E\<^bsub>G\<^esub>
  , source = \<lambda>e. from_nat (s\<^bsub>G\<^esub> (to_nat e)), target = \<lambda>e. from_nat (t\<^bsub>G\<^esub> (to_nat e))
  , node_label = \<lambda>e. l\<^bsub>G\<^esub> (to_nat e), edge_label = \<lambda>e. m\<^bsub>G\<^esub> (to_nat e)\<rparr>\<close>

lemma ngraph_to_from[simp]:
  \<open>from_ngraph (to_ngraph G) = G\<close>
  by (simp add: from_ngraph_def to_ngraph_def from_nat_def)

lemma graph_ngraph_corres_iff: 
  \<open>graph (to_ngraph G) \<longleftrightarrow> graph G \<close>
proof
  show \<open>graph (to_ngraph G)\<close> if \<open>graph G\<close>
  proof 
    show \<open>finite V\<^bsub>to_ngraph G\<^esub>\<close>
      using graph.finite_nodes[OF \<open>graph G\<close>]
      by (simp add: to_ngraph_def)
  next
    show \<open>finite E\<^bsub>to_ngraph G\<^esub>\<close>
      using graph.finite_edges[OF \<open>graph G\<close>]
      by (simp add: to_ngraph_def)
  next
    show \<open>s\<^bsub>to_ngraph G\<^esub> e \<in> V\<^bsub>to_ngraph G\<^esub>\<close> if \<open>e \<in> E\<^bsub>to_ngraph G\<^esub>\<close> for e
      using graph.source_integrity[OF \<open>graph G\<close>] that
      by (auto simp add: to_ngraph_def)
  next
    show \<open>t\<^bsub>to_ngraph G\<^esub> e \<in> V\<^bsub>to_ngraph G\<^esub>\<close> if \<open>e \<in> E\<^bsub>to_ngraph G\<^esub>\<close> for e
      using graph.target_integrity[OF \<open>graph G\<close>] that
      by (auto simp add: to_ngraph_def)
  qed
next
  show \<open>graph G\<close> if \<open>graph (to_ngraph G)\<close>
  proof 
    show \<open>finite V\<^bsub>G\<^esub>\<close>
      using graph.finite_nodes[OF \<open>graph (to_ngraph G)\<close>] that
      by (auto simp add: to_ngraph_def dest: finite_imageD)
  next
    show \<open>finite E\<^bsub>G\<^esub>\<close>
      using graph.finite_edges[OF \<open>graph (to_ngraph G)\<close>] that
      by (auto simp add: to_ngraph_def dest: finite_imageD)
  next
    show \<open>s\<^bsub>G\<^esub> e \<in> V\<^bsub>G\<^esub>\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
      using graph.source_integrity[OF \<open>graph (to_ngraph G)\<close>] that
      by (fastforce simp add: to_ngraph_def)
  next
    show \<open>t\<^bsub>G\<^esub> e \<in> V\<^bsub>G\<^esub>\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
      using graph.target_integrity[OF \<open>graph (to_ngraph G)\<close>] that
      by (fastforce simp add: to_ngraph_def)
  qed
qed
(* 
lemma ngraph_subset_graph_iff:
  shows \<open>V\<^bsub>G\<^esub> \<subseteq> V\<^bsub>H\<^esub> \<longleftrightarrow> V\<^bsub>to_ngraph G\<^esub> \<subseteq> V\<^bsub>to_ngraph H\<^esub>\<close>
  sorry *)
    
  




type_synonym nmorph = "(nat,nat,nat,nat) pre_morph"

definition to_nmorph :: "('v\<^sub>1::countable,'v\<^sub>2::countable,'e\<^sub>1::countable,'e\<^sub>2::countable) pre_morph \<Rightarrow> nmorph" where
"to_nmorph m \<equiv> \<lparr>node_map = \<lambda>v. to_nat (\<^bsub>m\<^esub>\<^sub>V (from_nat v)), edge_map = \<lambda>e. to_nat (\<^bsub>m\<^esub>\<^sub>E (from_nat e))\<rparr>"

definition from_nmorph :: "nmorph \<Rightarrow> ('v\<^sub>1::countable,'v\<^sub>2::countable,'e\<^sub>1::countable,'e\<^sub>2::countable) pre_morph" where
"from_nmorph m \<equiv> \<lparr>node_map = \<lambda>v. from_nat (\<^bsub>m\<^esub>\<^sub>V (to_nat v)), edge_map = \<lambda>e. from_nat (\<^bsub>m\<^esub>\<^sub>E (to_nat e))\<rparr>"

lemma nmorph_to_from[simp]:
  \<open>from_nmorph (to_nmorph m) = m\<close>
  by (simp add: from_nmorph_def to_nmorph_def from_nat_def)


lemma 
  morph_eq_nmorph_iff: \<open>morphism G H m \<longleftrightarrow> morphism (to_ngraph G) (to_ngraph H) (to_nmorph m)\<close>
proof
  show \<open>morphism (to_ngraph G) (to_ngraph H) (to_nmorph m)\<close> if asm: \<open>morphism G H m\<close>
  proof intro_locales
    show \<open>graph (to_ngraph G)\<close>
      using morphism.axioms(1)[OF that] 
      by (auto iff: graph_ngraph_corres_iff[of G])
  next
    show \<open>graph (to_ngraph H)\<close>
      using morphism.axioms(2)[OF that] 
      by (auto iff: graph_ngraph_corres_iff[of H])
  next
    show \<open>morphism_axioms (to_ngraph G) (to_ngraph H) (to_nmorph m)\<close>
    proof
      show \<open>\<^bsub>to_nmorph m\<^esub>\<^sub>E e \<in> E\<^bsub>to_ngraph H\<^esub>\<close> if \<open>e \<in> E\<^bsub>to_ngraph G\<^esub>\<close> for e
        using morphism.morph_edge_range[OF asm] that
        by (auto simp add: to_ngraph_def to_nmorph_def)
    next
      show \<open>\<^bsub>to_nmorph m\<^esub>\<^sub>V v \<in> V\<^bsub>to_ngraph H\<^esub>\<close> if \<open>v \<in> V\<^bsub>to_ngraph G\<^esub>\<close> for v
        using morphism.morph_node_range[OF asm] that
        by (auto simp add: to_ngraph_def to_nmorph_def)
    next
      show \<open>\<^bsub>to_nmorph m\<^esub>\<^sub>V (s\<^bsub>to_ngraph G\<^esub> e) = s\<^bsub>to_ngraph H\<^esub> (\<^bsub>to_nmorph m\<^esub>\<^sub>E e)\<close>
        if \<open>e \<in> E\<^bsub>to_ngraph G\<^esub>\<close> for e
        using morphism.source_preserve[OF asm] that
        by (auto simp add: to_ngraph_def to_nmorph_def)
    next
      show \<open>\<^bsub>to_nmorph m\<^esub>\<^sub>V (t\<^bsub>to_ngraph G\<^esub> e) = t\<^bsub>to_ngraph H\<^esub> (\<^bsub>to_nmorph m\<^esub>\<^sub>E e)\<close>
        if \<open>e \<in> E\<^bsub>to_ngraph G\<^esub>\<close> for e
        using morphism.target_preserve[OF asm] that
        by (auto simp add: to_ngraph_def to_nmorph_def)
    next
      show \<open>l\<^bsub>to_ngraph G\<^esub> v = l\<^bsub>to_ngraph H\<^esub> (\<^bsub>to_nmorph m\<^esub>\<^sub>V v)\<close>
        if \<open>v \<in> V\<^bsub>to_ngraph G\<^esub>\<close> for v
        using morphism.label_preserve[OF asm] that
        by (auto simp add: to_ngraph_def to_nmorph_def)
    next
      show \<open>m\<^bsub>to_ngraph G\<^esub> e = m\<^bsub>to_ngraph H\<^esub> (\<^bsub>to_nmorph m\<^esub>\<^sub>E e)\<close>
        if \<open>e \<in> E\<^bsub>to_ngraph G\<^esub>\<close> for e
        using morphism.mark_preserve[OF asm] that
        by (auto simp add: to_ngraph_def to_nmorph_def)
    qed
  qed
next
  show \<open>morphism G H m\<close> if asm: \<open>morphism (to_ngraph G) (to_ngraph H) (to_nmorph m)\<close>
  proof intro_locales
    show \<open>graph G\<close>
      using morphism.axioms(1)[OF that] 
      by (auto iff: graph_ngraph_corres_iff[of G])
  next
    show \<open>graph H\<close>
      using morphism.axioms(2)[OF that] 
      by (auto iff: graph_ngraph_corres_iff[of H])
  next
    show \<open>morphism_axioms G H m\<close>
    proof
      show \<open>\<^bsub>m\<^esub>\<^sub>E e \<in> E\<^bsub>H\<^esub>\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
        using morphism.morph_edge_range[OF asm] that
        by (fastforce simp add: to_ngraph_def to_nmorph_def)
    next
      show \<open>\<^bsub>m\<^esub>\<^sub>V v \<in> V\<^bsub>H\<^esub>\<close> if \<open>v \<in> V\<^bsub>G\<^esub>\<close> for v
        using morphism.morph_node_range[OF asm] that
        by (fastforce simp add: to_ngraph_def to_nmorph_def)
    next
      show \<open>\<^bsub>m\<^esub>\<^sub>V (s\<^bsub>G\<^esub> e) = s\<^bsub>H\<^esub> (\<^bsub>m\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
        using morphism.source_preserve[OF asm] that
        by (fastforce simp add: to_ngraph_def to_nmorph_def)
    next
      show \<open>\<^bsub>m\<^esub>\<^sub>V (t\<^bsub>G\<^esub> e) = t\<^bsub>H\<^esub> (\<^bsub>m\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
        using morphism.target_preserve[OF asm] that
        by (fastforce simp add: to_ngraph_def to_nmorph_def)
    next
      show \<open>l\<^bsub>G\<^esub> v = l\<^bsub>H\<^esub> (\<^bsub>m\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>G\<^esub>\<close> for v
        using morphism.label_preserve[OF asm] that
        by (fastforce simp add: to_ngraph_def to_nmorph_def)
    next
      show \<open>m\<^bsub>G\<^esub> e = m\<^bsub>H\<^esub> (\<^bsub>m\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>G\<^esub>\<close> for e
        using morphism.mark_preserve[OF asm] that
        by (fastforce simp add: to_ngraph_def to_nmorph_def)
    qed
  qed
qed
(* 
lemma blaa:
  \<open>\<^bsub>to_nmorph f\<^esub>\<^sub>V (to_nat x) \<in> V\<^bsub>to_ngraph G\<^esub> \<longleftrightarrow> \<^bsub>f\<^esub>\<^sub>V x \<in> V\<^bsub>G\<^esub>\<close>
  sorry

lemma blaa1:
  \<open>\<^bsub>to_nmorph f\<^esub>\<^sub>E (to_nat x) \<in> E\<^bsub>to_ngraph G\<^esub> \<longleftrightarrow> \<^bsub>f\<^esub>\<^sub>E x \<in> E\<^bsub>G\<^esub>\<close>
  sorry
 *)
lemma  morph_tong_tong_u_is_morph_tonm:
  assumes \<open>morphism (to_ngraph D) (to_ngraph D') u\<close>
  shows \<open>morphism D D' (from_nmorph u)\<close>
proof intro_locales
  show \<open>graph D\<close>
    using graph_ngraph_corres_iff morphism.axioms(1)[OF assms]
    by blast
next
  show \<open>graph D'\<close>
    using graph_ngraph_corres_iff morphism.axioms(2)[OF assms]
    by blast
next
  show \<open>morphism_axioms D D' (from_nmorph u)\<close>
    using assms
    by (auto simp add: morphism_axioms_def from_nmorph_def to_nmorph_def morphism_def to_ngraph_def from_ngraph_def)
qed
  

lemma comp_lift_node:
  \<open>(\<forall>v \<in> V\<^bsub>G\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>k \<circ>\<^sub>\<rightarrow> m\<^esub>\<^sub>V v) \<longleftrightarrow> (\<forall>v \<in> V\<^bsub>to_ngraph G\<^esub>. \<^bsub>(to_nmorph f) \<circ>\<^sub>\<rightarrow> (to_nmorph g)\<^esub>\<^sub>V v = \<^bsub>(to_nmorph k) \<circ>\<^sub>\<rightarrow> (to_nmorph m)\<^esub>\<^sub>V v)\<close>
proof
  show \<open>\<forall>v\<in>V\<^bsub>to_ngraph G\<^esub>. \<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>to_nmorph k \<circ>\<^sub>\<rightarrow> to_nmorph m\<^esub>\<^sub>V v\<close>
    if \<open>\<forall>v\<in>V\<^bsub>G\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>k \<circ>\<^sub>\<rightarrow> m\<^esub>\<^sub>V v\<close>
    using that
    unfolding morph_comp_def
    by (auto simp add: to_nmorph_def to_ngraph_def)
next
  show \<open>\<forall>v\<in>V\<^bsub>G\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>k \<circ>\<^sub>\<rightarrow> m\<^esub>\<^sub>V v\<close>
    if \<open>\<forall>v\<in>V\<^bsub>to_ngraph G\<^esub>. \<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>to_nmorph k \<circ>\<^sub>\<rightarrow> to_nmorph m\<^esub>\<^sub>V v\<close>
    using that
    unfolding morph_comp_def
    by (auto simp add: to_nmorph_def to_ngraph_def)
qed

lemma comp_lift_node1:
  \<open>(\<forall>v \<in> V\<^bsub>G\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v) \<longleftrightarrow> (\<forall>v \<in> V\<^bsub>to_ngraph G\<^esub>. \<^bsub>(to_nmorph f) \<circ>\<^sub>\<rightarrow> (to_nmorph g)\<^esub>\<^sub>V v = \<^bsub>(to_nmorph k)\<^esub>\<^sub>V v)\<close>
proof
  show \<open>\<forall>v\<in>V\<^bsub>to_ngraph G\<^esub>. \<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>to_nmorph k\<^esub>\<^sub>V v\<close> if \<open>\<forall>v\<in>V\<^bsub>G\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v\<close>
    using that
    unfolding morph_comp_def
    by (auto simp add: to_nmorph_def to_ngraph_def)
next
  show \<open>\<forall>v\<in>V\<^bsub>G\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v \<close> if \<open>\<forall>v\<in>V\<^bsub>to_ngraph G\<^esub>. \<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>V v = \<^bsub>to_nmorph k\<^esub>\<^sub>V v\<close>
    using that
    unfolding morph_comp_def
    by (auto simp add: to_nmorph_def to_ngraph_def)
qed
   
lemma comp_lift_edge:
\<open>(\<forall>e \<in> E\<^bsub>G\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>k \<circ>\<^sub>\<rightarrow> m\<^esub>\<^sub>E e) \<longleftrightarrow> (\<forall>e \<in> E\<^bsub>to_ngraph G\<^esub>. \<^bsub>(to_nmorph f) \<circ>\<^sub>\<rightarrow> (to_nmorph g)\<^esub>\<^sub>E e = \<^bsub>(to_nmorph k) \<circ>\<^sub>\<rightarrow> (to_nmorph m)\<^esub>\<^sub>E e)\<close>
proof
  show \<open>\<forall>e\<in>E\<^bsub>to_ngraph G\<^esub>. \<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>to_nmorph k \<circ>\<^sub>\<rightarrow> to_nmorph m\<^esub>\<^sub>E e\<close>
    if \<open>\<forall>e\<in>E\<^bsub>G\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>k \<circ>\<^sub>\<rightarrow> m\<^esub>\<^sub>E e\<close>
    using that
    unfolding morph_comp_def
    by (auto simp add: to_nmorph_def to_ngraph_def)
next
  show \<open>\<forall>e\<in>E\<^bsub>G\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>k \<circ>\<^sub>\<rightarrow> m\<^esub>\<^sub>E e\<close>
    if \<open>\<forall>e\<in>E\<^bsub>to_ngraph G\<^esub>. \<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>to_nmorph k \<circ>\<^sub>\<rightarrow> to_nmorph m\<^esub>\<^sub>E e\<close>
    using that
    unfolding morph_comp_def
    by (auto simp add: to_nmorph_def to_ngraph_def)
qed

lemma comp_lift_edge1:
  \<open>(\<forall>e \<in> E\<^bsub>G\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>k\<^esub>\<^sub>E e) \<longleftrightarrow> (\<forall>e \<in> E\<^bsub>to_ngraph G\<^esub>. \<^bsub>(to_nmorph f) \<circ>\<^sub>\<rightarrow> (to_nmorph g)\<^esub>\<^sub>E e = \<^bsub>(to_nmorph k)\<^esub>\<^sub>E e)\<close>
proof
  show \<open> \<forall>e\<in>E\<^bsub>to_ngraph G\<^esub>. \<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>to_nmorph k\<^esub>\<^sub>E e\<close> if \<open>\<forall>e\<in>E\<^bsub>G\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>k\<^esub>\<^sub>E e\<close>
    using that
    unfolding morph_comp_def
    by (auto simp add: to_nmorph_def to_ngraph_def)
next
  show \<open>\<forall>e\<in>E\<^bsub>G\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e = \<^bsub>k\<^esub>\<^sub>E e\<close> if \<open>\<forall>e\<in>E\<^bsub>to_ngraph G\<^esub>. \<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> to_nmorph g\<^esub>\<^sub>E e = \<^bsub>to_nmorph k\<^esub>\<^sub>E e\<close>
using that
    unfolding morph_comp_def
    by (auto simp add: to_nmorph_def to_ngraph_def)
qed
 
definition lift_morph :: "nmorph \<Rightarrow> ('a::countable,nat,'b::countable,nat) pre_morph" where
"lift_morph f \<equiv> \<lparr>node_map = \<lambda>v. \<^bsub>f\<^esub>\<^sub>V (to_nat v), edge_map = \<lambda>e. \<^bsub>f\<^esub>\<^sub>E (to_nat e)\<rparr>"


(* lemma abc:
  shows \<open>morphism G H f \<longleftrightarrow> morphism (to_ngraph G) (to_ngraph H) (lift_morph (to_nmorph f))\<close>
  sorry *)

end