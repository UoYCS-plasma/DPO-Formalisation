theory PullbackConstruction
  imports Morphism Pullback
begin

locale pullback_construction =
  f: morphism B D f +
  g: morphism C D g 
  for B D C f g
begin

abbreviation V where \<open>V \<equiv> {(x,y). x \<in> V\<^bsub>B\<^esub> \<and> y \<in> V\<^bsub>C\<^esub> \<and> \<^bsub>f\<^esub>\<^sub>V x = \<^bsub>g\<^esub>\<^sub>V y}\<close>
abbreviation E where \<open>E \<equiv> {(x,y). x \<in> E\<^bsub>B\<^esub> \<and> y \<in> E\<^bsub>C\<^esub> \<and> \<^bsub>f\<^esub>\<^sub>E x = \<^bsub>g\<^esub>\<^sub>E y}\<close>
fun s where \<open>s (x,y) = (s\<^bsub>B\<^esub> x, s\<^bsub>C\<^esub> y)\<close>
fun t where \<open>t (x,y) = (t\<^bsub>B\<^esub> x, t\<^bsub>C\<^esub> y)\<close>
fun l where \<open>l (x,_) = l\<^bsub>B\<^esub> x\<close>
fun m where \<open>m (x,_) = m\<^bsub>B\<^esub> x\<close>

definition A where \<open>A \<equiv> \<lparr>nodes = V, edges = E, source = s, target = t, node_label = l, edge_label = m\<rparr>\<close>


sublocale A: graph A
proof
  show \<open>finite V\<^bsub>A\<^esub>\<close>
  proof -
    have \<open>finite (V\<^bsub>B\<^esub> \<times> V\<^bsub>C\<^esub>)\<close>
      using f.G.finite_nodes g.G.finite_nodes
      by simp
    moreover have \<open>V \<subseteq> V\<^bsub>B\<^esub> \<times> V\<^bsub>C\<^esub>\<close>
      by blast
    ultimately show ?thesis
      by (simp add: A_def finite_subset)
  qed
next
  show \<open>finite E\<^bsub>A\<^esub>\<close>
  proof -
    have \<open>finite (E\<^bsub>B\<^esub> \<times> E\<^bsub>C\<^esub>)\<close>
      using f.G.finite_edges g.G.finite_edges
      by simp
    moreover have \<open>E \<subseteq> E\<^bsub>B\<^esub> \<times> E\<^bsub>C\<^esub>\<close>
      by blast
    ultimately show ?thesis
      by (simp add: A_def finite_subset)
  qed
next
  show \<open>s\<^bsub>A\<^esub> e \<in> V\<^bsub>A\<^esub>\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
    using that f.G.source_integrity g.G.source_integrity
    by (auto simp add: A_def f.source_preserve g.source_preserve)
next
  show \<open>t\<^bsub>A\<^esub> e \<in> V\<^bsub>A\<^esub>\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
    using that f.G.target_integrity g.G.target_integrity
    by (auto simp add: A_def f.target_preserve g.target_preserve)
qed


definition b where \<open>b \<equiv> \<lparr>node_map = fst, edge_map = fst\<rparr>\<close>
sublocale b: morphism A B b
  by standard (auto simp add: A_def b_def)


definition c where \<open>c \<equiv> \<lparr>node_map = snd, edge_map = snd\<rparr>\<close>
sublocale c: morphism A C c
  by standard 
    (auto simp add: A_def c_def f.mark_preserve g.mark_preserve f.label_preserve g.label_preserve)

(* Proof: Fundamentals of Alg. Graph Trans, Ehrig, Prange Taentzer *)
sublocale pp: pullback_diagram A B C D b c f g
proof
  show \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
    using that
    by(auto simp add: A_def b_def c_def morph_comp_def)

  show ce: \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
    using that
    by(auto simp add: A_def b_def c_def morph_comp_def)

  show \<open>Ex1M
            (\<lambda>x. morphism A' (to_ngraph A) x \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>to_nmorph b \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>to_nmorph c \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e))
            A'\<close>
    if A':\<open>graph A'\<close> and \<open>morphism A' (to_ngraph C) c'\<close> \<open>morphism A' (to_ngraph B) b'\<close> 
      \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>to_nmorph g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close> 
      \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>to_nmorph f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>to_nmorph g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close>
    for A' :: "('c, 'd) ngraph" and c' b'
  proof -

    interpret A: graph \<open>to_ngraph A\<close>
      using graph_ngraph_corres_iff A.graph_axioms
      by blast

    interpret A': graph A'
      using A' by assumption

    define u where \<open>u \<equiv> \<lparr>node_map = \<lambda>v. (\<^bsub>b'\<^esub>\<^sub>V v, \<^bsub>c'\<^esub>\<^sub>V v), edge_map = \<lambda>e. (\<^bsub>b'\<^esub>\<^sub>E e, \<^bsub>c'\<^esub>\<^sub>E e)\<rparr>\<close>
    term A
    interpret u: morphism A' \<open>to_ngraph A\<close> \<open>to_nmorph u\<close>
      apply standard
using ce that(5)
           apply (auto simp add: u_def morph_comp_def b_def c_def A_def)
try0
      sledgehammer
    proof


end

end

