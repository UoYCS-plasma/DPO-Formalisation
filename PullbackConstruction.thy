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


definition b :: "('a \<times> 'g, 'a, 'b \<times> 'h, 'b) pre_morph" where \<open>b \<equiv> \<lparr>node_map = fst, edge_map = fst\<rparr>\<close>
sublocale b: morphism A B b
  by standard (auto simp add: A_def b_def)


definition c :: "('a \<times> 'g, 'g, 'b \<times> 'h, 'h) pre_morph"
  where \<open>c \<equiv> \<lparr>node_map = snd, edge_map = snd\<rparr>\<close>

sublocale c: morphism A C c
  by standard 
    (auto simp add: A_def c_def f.mark_preserve g.mark_preserve f.label_preserve g.label_preserve)

(* Proof: Fundamentals of Alg. Graph Trans, Ehrig, Prange Taentzer *)
sublocale pb: pullback_diagram A B C D b c f g
proof
  show \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
    using that
    by(auto simp add: A_def b_def c_def morph_comp_def)
next
  show ce: \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
    using that
    by(auto simp add: A_def b_def c_def morph_comp_def)
next
  show \<open>Ex1M (\<lambda>x. morphism A' A x
          \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) 
          \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) 
          \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) 
          \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e))
            A'\<close>
    if A':\<open>graph A'\<close> and 
      \<open>morphism A' C c'\<close> 
      \<open>morphism A' B b'\<close> 
      \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close> 
      \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close>
    for A' :: "('c, 'd) ngraph" and c' b'
  proof -

    interpret b': morphism A' B b'
      using \<open>morphism A' B b'\<close>
      by assumption

     interpret c': morphism A' C c'
       using \<open>morphism A' C c'\<close>
       by assumption

    define u :: "(nat, 'a \<times> 'g, nat, 'b \<times> 'h) pre_morph" where 
      \<open>u \<equiv> \<lparr>node_map = \<lambda>v. (\<^bsub>b'\<^esub>\<^sub>V v, \<^bsub>c'\<^esub>\<^sub>V v)
           ,edge_map = \<lambda>e. (\<^bsub>b'\<^esub>\<^sub>E e, \<^bsub>c'\<^esub>\<^sub>E e)\<rparr>\<close>

    interpret u: morphism A' A u
    proof
      show ue: \<open>\<^bsub>u\<^esub>\<^sub>E e \<in> E\<^bsub>A\<^esub>\<close> if \<open>e \<in> E\<^bsub>A'\<^esub>\<close> for e
        using \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close> 
            that  b'.morph_edge_range  c'.morph_edge_range 
        by(simp add: u_def A_def morph_comp_def)
    next
      show \<open>\<^bsub>u\<^esub>\<^sub>V v \<in> V\<^bsub>A\<^esub>\<close> if \<open>v \<in> V\<^bsub>A'\<^esub>\<close> for v
        using \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close> 
            that  b'.morph_node_range  c'.morph_node_range 
        by(simp add: u_def A_def morph_comp_def)
    next
      show \<open>\<^bsub>u\<^esub>\<^sub>V (s\<^bsub>A'\<^esub> e) = s\<^bsub>A\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>A'\<^esub>\<close> for e
        by(simp add: u_def A_def morph_comp_def b'.source_preserve c'.source_preserve that)
    next
      show \<open>\<^bsub>u\<^esub>\<^sub>V (t\<^bsub>A'\<^esub> e) = t\<^bsub>A\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>A'\<^esub>\<close> for e
        by(simp add: u_def A_def morph_comp_def b'.target_preserve c'.target_preserve that)
    next
      show \<open>l\<^bsub>A'\<^esub> v = l\<^bsub>A\<^esub> (\<^bsub>u\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>A'\<^esub>\<close> for v
        by (simp add: u_def A_def b'.label_preserve to_ngraph_def that)
    next
      show \<open>m\<^bsub>A'\<^esub> e = m\<^bsub>A\<^esub> (\<^bsub>u\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>A'\<^esub>\<close> for e
        by (simp add: u_def A_def b'.mark_preserve to_ngraph_def that)
    qed  

    show ?thesis
    proof (rule_tac x = u in exI, intro conjI)
      show \<open>morphism A' A u\<close>
        using u.morphism_axioms
        by assumption
    next
      show \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v\<close>
        by (simp add: b_def u_def morph_comp_def)
    next
      show \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e\<close>
        by (simp add: b_def u_def morph_comp_def)
  next
    show \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close>
      by (simp add: c_def u_def morph_comp_def)
  next
    show \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close>
      by (simp add: c_def u_def morph_comp_def)
  next
    show \<open>\<forall>y. morphism A' A y 
      \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) 
      \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) 
      \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) 
      \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e) 
      \<longrightarrow> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>y\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>y\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v)\<close>
    proof safe
      show \<open>\<^bsub>u'\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e\<close>
        if \<open>morphism A' A u'\<close> 
          and \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v\<close> 
          and \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e\<close>
          and \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close>
          and \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close>
          and \<open>e \<in> E\<^bsub>A'\<^esub>\<close>
        for u' e
      proof -
        have \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. fst (\<^bsub>u'\<^esub>\<^sub>E e) = \<^bsub>b'\<^esub>\<^sub>E e\<close>
          using \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e\<close>
          by (simp add: b_def morph_comp_def)
        moreover

        have \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. snd (\<^bsub>u'\<^esub>\<^sub>E e) = \<^bsub>c'\<^esub>\<^sub>E e\<close>
          using \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close>
          by (simp add: c_def morph_comp_def)

        ultimately show ?thesis
          using \<open>e \<in> E\<^bsub>A'\<^esub>\<close>
          by (simp add: u_def) (metis surjective_pairing)
      qed
    next
      show \<open>\<^bsub>u'\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v\<close>
        if \<open>morphism A' A u'\<close> 
          and \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v\<close> 
          and \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e\<close>
          and \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close>
          and \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close>
          and \<open>v \<in> V\<^bsub>A'\<^esub>\<close>
        for u' v
      proof -
        have \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. fst (\<^bsub>u'\<^esub>\<^sub>V v) = \<^bsub>b'\<^esub>\<^sub>V v\<close>
          using \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v\<close> 
          by (simp_all add: b_def morph_comp_def)
        moreover

        have \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. snd (\<^bsub>u'\<^esub>\<^sub>V v) = \<^bsub>c'\<^esub>\<^sub>V v\<close>
          using \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close>
          by (simp add: c_def morph_comp_def)

        ultimately show ?thesis
          using \<open>v \<in> V\<^bsub>A'\<^esub>\<close>
          by (simp add: u_def) (metis surjective_pairing)
    qed
  qed
qed
qed
qed
end



context pushout_diagram
begin


theorem uniqueness_pc:
  fixes C' c' g'
  assumes 
    C': \<open>graph C'\<close> and
    c': \<open>morphism A C' c'\<close> and
    g': \<open>morphism C' D g'\<close>
  shows \<open>pushout_diagram A B C' D b c' f g' \<longleftrightarrow> (\<exists>u. bijective_morphism C C' u)\<close>
proof 
  show \<open>\<exists>u. bijective_morphism C C' u\<close>
    if \<open>pushout_diagram A B C' D b c' f g'\<close>
  proof -

    interpret po1: pushout_diagram A B C D b c f g
      by (simp add: pushout_diagram_axioms)

    interpret po2: pushout_diagram A B C' D b c' f g'
      using that by assumption


    (* front right *)
    interpret fr: pullback_construction C' D C g' g ..

    (* back left *)
    interpret bt: pullback_diagram A A A B idM idM b b
    proof
      show \<open>\<^bsub>b \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v = \<^bsub>b \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v\<close> if \<open> v \<in> V\<^bsub>A\<^esub> \<close> for v
        by (simp add: morph_comp_def)
    next
      show \<open>\<^bsub>b \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e = \<^bsub>b \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
        by (simp add: morph_comp_def)
    next
      show \<open>Ex1M
            (\<lambda>x. morphism A' A x \<and>
                  (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and>
                  (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and>
                  (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e))
            A' \<close>
        if \<open>graph A'\<close>
          \<open>morphism A' A c'\<close>
          \<open>morphism A' A b'\<close>
          \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>b \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>b \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close>
          \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>b \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>b \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close>
        for A' :: "('c,'d) ngraph" and b' c'
      proof -
        interpret a: bijective_morphism A A idM ..

        define u where \<open>u \<equiv> b'\<close>
        interpret u: morphism A' A u
          by (simp add: u_def \<open>morphism A' A b'\<close>)

        show ?thesis
        proof (rule_tac x = u in exI, intro conjI)
          show \<open>morphism A' A u\<close>
            using u.morphism_axioms by assumption
          show \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close>
            using           \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>b \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>b \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close>
            apply (simp add: morph_comp_def u_def)
            sorry
        qed (simp_all add: u_def morph_comp_def)

(*     interpret tf: pushout_diagram A A C' fr.A idM *)



  show ?thesis
    sorry

qed


end

end

