theory Pullback
  imports Pushout
begin

locale pullback_diagram =
  b: morphism A B b +
  c: morphism A C c +
  f: morphism B D f +
  g: morphism C D g for A B C D b c f g +
assumes
  node_commutativity: \<open>\<And>v. v \<in> V\<^bsub>A\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> and
  edge_commutativity: \<open>\<And>e. e \<in> E\<^bsub>A\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close> and
  universal_property: \<open>\<lbrakk>
    graph (A' :: ('c,'d) ngraph); 
    morphism A' C c'; 
    morphism A' B b';
     \<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v;
     \<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<rbrakk> 
    \<Longrightarrow> Ex1M (\<lambda>u. morphism A' A u \<and>
            (\<forall>v \<in> V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and>
            (\<forall>v \<in> V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e))
            A'\<close>
begin


lemma universal_property_exist_gen:
  fixes A'
  assumes \<open>graph A'\<close> \<open>morphism A' C c'\<close> \<open>morphism A' B b'\<close>
     \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close>
     \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close>
   shows \<open>Ex1M (\<lambda>u. morphism A' A u \<and>
            (\<forall>v \<in> V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and>
            (\<forall>v \<in> V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) \<and>
            (\<forall>e \<in> E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e))
            A'\<close>
proof -
  interpret A': graph A'
    using \<open>graph A'\<close> by assumption

  interpret nA': graph \<open>to_ngraph A'\<close>
    using \<open>graph A'\<close>
    by (simp add: graph_ngraph_corres_iff)

  interpret c': morphism A' C c'
    using \<open>morphism A' C c'\<close> 
    by assumption

  interpret b': morphism A' B b'
    using \<open>morphism A' B b'\<close>
    by assumption

  define nb' where \<open>nb' \<equiv> \<lparr>node_map = \<lambda>v. \<^bsub>b'\<^esub>\<^sub>V (from_nat v), edge_map = \<lambda>e. \<^bsub>b'\<^esub>\<^sub>E (from_nat e)\<rparr>\<close>
  define nc' where \<open>nc' \<equiv> \<lparr>node_map = \<lambda>v. \<^bsub>c'\<^esub>\<^sub>V (from_nat v), edge_map = \<lambda>e. \<^bsub>c'\<^esub>\<^sub>E (from_nat e)\<rparr>\<close>

  interpret nb: morphism \<open>to_ngraph A'\<close> B nb'
  proof
    show \<open>\<^bsub>nb'\<^esub>\<^sub>E e \<in> E\<^bsub>B\<^esub>\<close> if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
      using that
      by(auto simp add: nb'_def to_ngraph_def  b'.morph_edge_range)
  next
    show \<open>\<^bsub>nb'\<^esub>\<^sub>V v \<in> V\<^bsub>B\<^esub>\<close> if \<open>v \<in> V\<^bsub>to_ngraph A'\<^esub>\<close> for v
      using that
      by(auto simp add: nb'_def to_ngraph_def  b'.morph_node_range)
  next
    show \<open>\<^bsub>nb'\<^esub>\<^sub>V (s\<^bsub>to_ngraph A'\<^esub> e) = s\<^bsub>B\<^esub> (\<^bsub>nb'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
      using that
      by(auto simp add: nb'_def to_ngraph_def  b'.source_preserve)
  next
    show \<open>\<^bsub>nb'\<^esub>\<^sub>V (t\<^bsub>to_ngraph A'\<^esub> e) = t\<^bsub>B\<^esub> (\<^bsub>nb'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
      using that
      by(auto simp add: nb'_def to_ngraph_def  b'.target_preserve)
  qed (auto simp add: nb'_def to_ngraph_def  b'.label_preserve b'.mark_preserve)

  interpret nc: morphism \<open>to_ngraph A'\<close> C nc'
  proof
    show \<open>\<^bsub>nc'\<^esub>\<^sub>E e \<in> E\<^bsub>C\<^esub>\<close> if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
      using that
      by(auto simp add: nc'_def to_ngraph_def  c'.morph_edge_range)
  next
    show \<open>\<^bsub>nc'\<^esub>\<^sub>V v \<in> V\<^bsub>C\<^esub>\<close> if \<open>v \<in> V\<^bsub>to_ngraph A'\<^esub>\<close> for v
      using that
      by(auto simp add: nc'_def to_ngraph_def  c'.morph_node_range)
  next
    show \<open>\<^bsub>nc'\<^esub>\<^sub>V (s\<^bsub>to_ngraph A'\<^esub> e) = s\<^bsub>C\<^esub> (\<^bsub>nc'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
      using that
      by(auto simp add: nc'_def to_ngraph_def  c'.source_preserve)
  next
    show \<open>\<^bsub>nc'\<^esub>\<^sub>V (t\<^bsub>to_ngraph A'\<^esub> e) = t\<^bsub>C\<^esub> (\<^bsub>nc'\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
      using that
      by(auto simp add: nc'_def to_ngraph_def  c'.target_preserve)
  qed (auto simp add: nc'_def to_ngraph_def  c'.label_preserve c'.mark_preserve)

  have tr: \<open>\<And>v. v \<in> V\<^bsub>to_ngraph A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> nb'\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> nc'\<^esub>\<^sub>V v\<close> \<open>\<And>e. e \<in> E\<^bsub>to_ngraph A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> nb'\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> nc'\<^esub>\<^sub>E e\<close>
    using
      \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close>
     \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close>
    by (auto simp add: nb'_def nc'_def morph_comp_def to_ngraph_def)

  obtain u where \<open>morphism (to_ngraph A') A u\<close> \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>nb'\<^esub>\<^sub>V v\<close>
           \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>nb'\<^esub>\<^sub>E e\<close> \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>nc'\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>nc'\<^esub>\<^sub>E e\<close>
    using universal_property[OF nA'.graph_axioms nc.morphism_axioms nb.morphism_axioms tr]
    by fast

  interpret u: morphism \<open>to_ngraph A'\<close> A u
    using  \<open>morphism (to_ngraph A') A u\<close>  by assumption

  define nu :: "('k, 'a, 'l, 'b) pre_morph" 
    where \<open>nu \<equiv> \<lparr>node_map = \<lambda>v. \<^bsub>u\<^esub>\<^sub>V (to_nat v), edge_map = \<lambda>e. \<^bsub>u\<^esub>\<^sub>E (to_nat e)\<rparr>\<close>

  interpret nu: morphism A' A nu
  proof
    show \<open>\<^bsub>nu\<^esub>\<^sub>E e \<in> E\<^bsub>A\<^esub>\<close> if \<open>e \<in> E\<^bsub>A'\<^esub>\<close> for e
      by (simp add: nu_def to_ngraph_def u.morph_edge_range that)
  next
    show \<open>\<^bsub>nu\<^esub>\<^sub>V v \<in> V\<^bsub>A\<^esub>\<close> if \<open>v \<in> V\<^bsub>A'\<^esub>\<close> for v
      by (simp add: nu_def to_ngraph_def u.morph_node_range that)
  next
    show \<open>\<^bsub>nu\<^esub>\<^sub>V (s\<^bsub>A'\<^esub> e) = s\<^bsub>A\<^esub> (\<^bsub>nu\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>A'\<^esub>\<close> for e
      using u.source_preserve that
      unfolding nu_def to_ngraph_def
      by fastforce
  next
    show \<open>\<^bsub>nu\<^esub>\<^sub>V (t\<^bsub>A'\<^esub> e) = t\<^bsub>A\<^esub> (\<^bsub>nu\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>A'\<^esub>\<close> for e
      using u.target_preserve that
      unfolding nu_def to_ngraph_def
      by fastforce
  next
    show \<open>l\<^bsub>A'\<^esub> v = l\<^bsub>A\<^esub> (\<^bsub>nu\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>A'\<^esub>\<close> for v
      using u.label_preserve that
      unfolding nu_def to_ngraph_def
      by fastforce
  next
    show \<open>m\<^bsub>A'\<^esub> e = m\<^bsub>A\<^esub> (\<^bsub>nu\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>A'\<^esub>\<close> for e
      using u.mark_preserve that
      unfolding nu_def to_ngraph_def
      by fastforce
  qed

  show ?thesis
  proof (rule_tac x=nu in exI, intro conjI)
    show \<open>morphism A' A nu\<close>
      using nu.morphism_axioms by assumption
  next
    show \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> nu\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v\<close>
      using \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>nb'\<^esub>\<^sub>V v\<close>
      by (simp add: nu_def morph_comp_def to_ngraph_def nb'_def)
  next
    show \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> nu\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e\<close>
      using \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>nb'\<^esub>\<^sub>E e\<close>
      by (simp add: nu_def morph_comp_def to_ngraph_def nb'_def)
  next
    show \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> nu\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close>
      using \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>nc'\<^esub>\<^sub>V v\<close>
      by (simp add: nu_def morph_comp_def to_ngraph_def nc'_def)
  next
    show \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> nu\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close>
      using \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>nc'\<^esub>\<^sub>E e\<close>
      by (simp add: nu_def morph_comp_def to_ngraph_def nc'_def)
  next
    show \<open>\<forall>y. morphism A' A y \<and>
        (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e) \<longrightarrow>
        (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>y\<^esub>\<^sub>E e = \<^bsub>nu\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>y\<^esub>\<^sub>V v = \<^bsub>nu\<^esub>\<^sub>V v)\<close>
    proof safe
      show \<open>\<^bsub>y\<^esub>\<^sub>E e = \<^bsub>nu\<^esub>\<^sub>E e\<close>
        if \<open>morphism A' A y\<close> 
          \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v\<close> 
          \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e\<close>
          \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close>
          \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close>
          \<open>e \<in> E\<^bsub>A'\<^esub>\<close> for y e
      proof -
        interpret y: morphism A' A y
          using \<open>morphism A' A y\<close>  by assumption

        define ny where \<open>ny \<equiv> \<lparr>node_map = \<lambda>v. \<^bsub>y\<^esub>\<^sub>V (from_nat v), edge_map = \<lambda>e. \<^bsub>y\<^esub>\<^sub>E (from_nat e)\<rparr>\<close>
        interpret ny: morphism \<open>to_ngraph A'\<close> A ny
        proof
          show \<open>\<^bsub>ny\<^esub>\<^sub>E e \<in> E\<^bsub>A\<^esub>\<close> if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
            using that
            by (auto simp add: ny_def to_ngraph_def y.morph_edge_range)
        next
          show \<open>\<^bsub>ny\<^esub>\<^sub>V v \<in> V\<^bsub>A\<^esub>\<close> if \<open>v \<in> V\<^bsub>to_ngraph A'\<^esub>\<close> for v
            using that
            by (auto simp add: ny_def to_ngraph_def y.morph_node_range)
        next
          show \<open>\<^bsub>ny\<^esub>\<^sub>V (s\<^bsub>to_ngraph A'\<^esub> e) = s\<^bsub>A\<^esub> (\<^bsub>ny\<^esub>\<^sub>E e)\<close>
            if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
            using that
            by (auto simp add: ny_def to_ngraph_def y.source_preserve)
        next
          show \<open>\<^bsub>ny\<^esub>\<^sub>V (t\<^bsub>to_ngraph A'\<^esub> e) = t\<^bsub>A\<^esub> (\<^bsub>ny\<^esub>\<^sub>E e)\<close>
            if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
            using that
            by (auto simp add: ny_def to_ngraph_def y.target_preserve)
        next
          show \<open>l\<^bsub>to_ngraph A'\<^esub> v = l\<^bsub>A\<^esub> (\<^bsub>ny\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>to_ngraph A'\<^esub>\<close> for v
            using that
            by (auto simp add: ny_def to_ngraph_def y.label_preserve)
        next
          show \<open>m\<^bsub>to_ngraph A'\<^esub> e = m\<^bsub>A\<^esub> (\<^bsub>ny\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
            using that
            by (auto simp add: ny_def to_ngraph_def y.mark_preserve)
        qed

        have aa: \<open>morphism (to_ngraph A') A u \<and>
         (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>nb'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>nb'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>nc'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>nc'\<^esub>\<^sub>E e)\<close>
          using \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>nb'\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>nc'\<^esub>\<^sub>E e\<close> \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>nb'\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>nc'\<^esub>\<^sub>V v\<close> u.morphism_axioms by blast

        have a: \<open>morphism (to_ngraph A') A ny \<and>
          (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>V v = \<^bsub>nb'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>E e = \<^bsub>nb'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>V v = \<^bsub>nc'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>E e = \<^bsub>nc'\<^esub>\<^sub>E e)\<close>
        proof(intro conjI)
          show \<open>morphism (to_ngraph A') A ny\<close>
          using ny.morphism_axioms
          by simp
      next
        show \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>V v = \<^bsub>nb'\<^esub>\<^sub>V v\<close>
          using \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v\<close> 
          by (simp add: to_ngraph_def ny_def nb'_def morph_comp_def)
      next
        show \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>E e = \<^bsub>nb'\<^esub>\<^sub>E e\<close>
          using\<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e\<close>
          by (simp add: to_ngraph_def ny_def nb'_def morph_comp_def)
      next
        show \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>V v = \<^bsub>nc'\<^esub>\<^sub>V v\<close>
          using \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close>
          by (simp add: to_ngraph_def ny_def nc'_def morph_comp_def)
      next
        show \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>E e = \<^bsub>nc'\<^esub>\<^sub>E e\<close>
          using \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close>
          by (simp add: to_ngraph_def ny_def nc'_def morph_comp_def)
      qed

        from ex_eq[OF universal_property[OF nA'.graph_axioms nc.morphism_axioms nb.morphism_axioms tr] a aa]
        have \<open>\<^bsub>ny\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
          using that
          by fastforce

        thus ?thesis
          using that
          apply (simp add: to_ngraph_def ny_def nu_def)
          by (metis from_nat_to_nat imageI)
      qed
    next
      show \<open>\<^bsub>y\<^esub>\<^sub>V v = \<^bsub>nu\<^esub>\<^sub>V v\<close>
        if \<open>morphism A' A y\<close> 
          \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v\<close> 
          \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e\<close>
          \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close>
          \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close>
          \<open>v \<in> V\<^bsub>A'\<^esub>\<close> for y v
      proof -
        interpret y: morphism A' A y
          using \<open>morphism A' A y\<close>  by assumption

        define ny where \<open>ny \<equiv> \<lparr>node_map = \<lambda>v. \<^bsub>y\<^esub>\<^sub>V (from_nat v), edge_map = \<lambda>e. \<^bsub>y\<^esub>\<^sub>E (from_nat e)\<rparr>\<close>
        interpret ny: morphism \<open>to_ngraph A'\<close> A ny
        proof
          show \<open>\<^bsub>ny\<^esub>\<^sub>E e \<in> E\<^bsub>A\<^esub>\<close> if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
            using that
            by (auto simp add: ny_def to_ngraph_def y.morph_edge_range)
        next
          show \<open>\<^bsub>ny\<^esub>\<^sub>V v \<in> V\<^bsub>A\<^esub>\<close> if \<open>v \<in> V\<^bsub>to_ngraph A'\<^esub>\<close> for v
            using that
            by (auto simp add: ny_def to_ngraph_def y.morph_node_range)
        next
          show \<open>\<^bsub>ny\<^esub>\<^sub>V (s\<^bsub>to_ngraph A'\<^esub> e) = s\<^bsub>A\<^esub> (\<^bsub>ny\<^esub>\<^sub>E e)\<close>
            if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
            using that
            by (auto simp add: ny_def to_ngraph_def y.source_preserve)
        next
          show \<open>\<^bsub>ny\<^esub>\<^sub>V (t\<^bsub>to_ngraph A'\<^esub> e) = t\<^bsub>A\<^esub> (\<^bsub>ny\<^esub>\<^sub>E e)\<close>
            if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
            using that
            by (auto simp add: ny_def to_ngraph_def y.target_preserve)
        next
          show \<open>l\<^bsub>to_ngraph A'\<^esub> v = l\<^bsub>A\<^esub> (\<^bsub>ny\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>to_ngraph A'\<^esub>\<close> for v
            using that
            by (auto simp add: ny_def to_ngraph_def y.label_preserve)
        next
          show \<open>m\<^bsub>to_ngraph A'\<^esub> e = m\<^bsub>A\<^esub> (\<^bsub>ny\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>to_ngraph A'\<^esub>\<close> for e
            using that
            by (auto simp add: ny_def to_ngraph_def y.mark_preserve)
        qed

        have aa: \<open>morphism (to_ngraph A') A u \<and>
         (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>nb'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>nb'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>nc'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>nc'\<^esub>\<^sub>E e)\<close>
          using \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>nb'\<^esub>\<^sub>E e\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>nc'\<^esub>\<^sub>E e\<close> \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>nb'\<^esub>\<^sub>V v\<close> \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>nc'\<^esub>\<^sub>V v\<close> u.morphism_axioms by blast

        have a: \<open>morphism (to_ngraph A') A ny \<and>
          (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>V v = \<^bsub>nb'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>E e = \<^bsub>nb'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>V v = \<^bsub>nc'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>E e = \<^bsub>nc'\<^esub>\<^sub>E e)\<close>
        proof(intro conjI)
          show \<open>morphism (to_ngraph A') A ny\<close>
          using ny.morphism_axioms
          by simp
      next
        show \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>V v = \<^bsub>nb'\<^esub>\<^sub>V v\<close>
          using \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v\<close> 
          by (simp add: to_ngraph_def ny_def nb'_def morph_comp_def)
      next
        show \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>E e = \<^bsub>nb'\<^esub>\<^sub>E e\<close>
          using\<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e\<close>
          by (simp add: to_ngraph_def ny_def nb'_def morph_comp_def)
      next
        show \<open>\<forall>v\<in>V\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>V v = \<^bsub>nc'\<^esub>\<^sub>V v\<close>
          using \<open>\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close>
          by (simp add: to_ngraph_def ny_def nc'_def morph_comp_def)
      next
        show \<open>\<forall>e\<in>E\<^bsub>to_ngraph A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> ny\<^esub>\<^sub>E e = \<^bsub>nc'\<^esub>\<^sub>E e\<close>
          using \<open>\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close>
          by (simp add: to_ngraph_def ny_def nc'_def morph_comp_def)
      qed

        from ex_eq[OF universal_property[OF nA'.graph_axioms nc.morphism_axioms nb.morphism_axioms tr] a aa]
        have \<open>\<^bsub>ny\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph A'\<^esub>\<close> for v
          using that
          by fastforce

        thus ?thesis
          using that
          apply (simp add: to_ngraph_def ny_def nu_def)
          by (metis from_nat_to_nat imageI)
      qed
    qed
  qed
qed
end


lemma fun_algrtr_4_7_2:
  fixes C A m
  assumes \<open>injective_morphism C A m\<close>
  shows \<open>pullback_diagram C C C A idM idM m m\<close>
proof -
  interpret m: injective_morphism C A m
    using assms by assumption

  interpret idm: injective_morphism C C idM
    by (simp add: m.G.idm.injective_morphism_axioms)

  show ?thesis
  proof
    show \<open>\<^bsub>m \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v = \<^bsub>m \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>C\<^esub>\<close> for v
      by (simp add: morph_comp_def)
  next
    show \<open>\<^bsub>m \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e = \<^bsub>m \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>C\<^esub>\<close> for e
      by (simp add: morph_comp_def)
  next
    show \<open>Ex1M (\<lambda>x. morphism A' C x \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e)) A'\<close>
      if \<open>graph A'\<close> \<open>morphism A' C c'\<close> \<open>morphism A' C b'\<close> 
        \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>m \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>m \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close>
        \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>m \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>m \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close>
      for A':: "('c,'d) ngraph" and c' b'
    proof -


      interpret c': morphism A' C c'
        using  \<open>morphism A' C c'\<close> by assumption

      interpret b': morphism A' C b'
        using  \<open>morphism A' C b'\<close> by assumption

      have \<open>\<^bsub>b'\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A'\<^esub>\<close>for v
        using that m.inj_nodes c'.morph_node_range b'.morph_node_range
          \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>m \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>m \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close>
        by(simp add: morph_comp_def inj_onD)

      moreover have \<open>\<^bsub>b'\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A'\<^esub>\<close> for e
        using that m.inj_edges c'.morph_edge_range b'.morph_edge_range
          \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>m \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>m \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close>
        by(simp add: morph_comp_def inj_onD)

      ultimately show ?thesis
        using c'.morphism_axioms by auto
    qed
  qed
qed
(* 
context pushout_diagram begin
lemma
  assumes \<open>injective_morphism A B b\<close>
  shows \<open>pullback_diagram A B C D b c f g\<close>
proof
  show \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
    using that node_commutativity
    by simp
next
  show \<open>\<^bsub>f \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
    using that edge_commutativity
    by simp
next
  show \<open>Ex1M (\<lambda>x. morphism A' A x \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>b \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>c \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e)) A'\<close>
    if \<open>graph A'\<close> \<open>morphism A' C c'\<close> 
      \<open>morphism A' B b'\<close> 
      \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close>
      \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close> for A' :: "('c,'d) ngraph" and c' b'
  proof -
    interpret b: injective_morphism A B b
      using assms by assumption

    show ?thesis
      using fact_2_17_2_nodes fact_2_17_2_edges that
      sorry
  qed
qed
end *)



(*
Fundamentals of Algebraic Graph Transformation
Fact 2.27, Pullback composition (PDF P 45)
https://link.springer.com/content/pdf/10.1007/3-540-31188-2.pdf
 *)
lemma pullback_composition:
  assumes 
    1: \<open>pullback_diagram A B C D f g g' f'\<close> and
    2: \<open>pullback_diagram B E D F e g' e'' e'\<close>
  shows \<open>pullback_diagram A E C F (e \<circ>\<^sub>\<rightarrow> f) g e'' (e' \<circ>\<^sub>\<rightarrow> f')\<close>
proof -
  interpret 1: pullback_diagram A B C D f g g' f'
    using 1 by assumption

  interpret 2: pullback_diagram B E D F e g' e'' e'
    using 2 by assumption

  interpret b: morphism A E \<open>e \<circ>\<^sub>\<rightarrow> f\<close>
    using wf_morph_comp[OF "1.b.morphism_axioms" "2.b.morphism_axioms"]
    by assumption

  interpret b: morphism C F \<open>e' \<circ>\<^sub>\<rightarrow> f'\<close>
    using wf_morph_comp[OF "1.g.morphism_axioms" "2.g.morphism_axioms"]
    by assumption

  show ?thesis
  proof
    show \<open>\<^bsub>e'' \<circ>\<^sub>\<rightarrow> (e \<circ>\<^sub>\<rightarrow> f)\<^esub>\<^sub>V v = \<^bsub>e' \<circ>\<^sub>\<rightarrow> f' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
      using that "1.node_commutativity" "2.node_commutativity"
      by (auto simp add: morph_comp_def "1.b.morph_node_range")
  next
    show \<open>\<^bsub>e'' \<circ>\<^sub>\<rightarrow> (e \<circ>\<^sub>\<rightarrow> f)\<^esub>\<^sub>E ea = \<^bsub>e' \<circ>\<^sub>\<rightarrow> f' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E ea\<close> if \<open>ea \<in> E\<^bsub>A\<^esub>\<close> for ea
      using that "1.edge_commutativity" "2.edge_commutativity"
      by (auto simp add: morph_comp_def "1.b.morph_edge_range")
  next
    show \<open>Ex1M
        (\<lambda>x. morphism X A x \<and>
             (\<forall>v \<in>V\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v) \<and>
             (\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>k\<^esub>\<^sub>E ea) \<and>
             (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v) \<and> (\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea))
        X \<close>
      if \<open>graph X\<close> \<open>morphism X C h\<close> \<open>morphism X E k\<close>
        \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>e'' \<circ>\<^sub>\<rightarrow> k\<^esub>\<^sub>V v = \<^bsub>e' \<circ>\<^sub>\<rightarrow> f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close>
        \<open>\<And>e. e \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>e'' \<circ>\<^sub>\<rightarrow> k\<^esub>\<^sub>E e = \<^bsub>e' \<circ>\<^sub>\<rightarrow> f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e\<close>
      for X :: "('c,'d) ngraph" and h k
    proof -

      interpret f'h: morphism X D \<open>f' \<circ>\<^sub>\<rightarrow> h\<close>
        using "1.g.morphism_axioms" that(2) wf_morph_comp by blast

      have a: \<open>\<^bsub>e'' \<circ>\<^sub>\<rightarrow> k\<^esub>\<^sub>V v = \<^bsub>e' \<circ>\<^sub>\<rightarrow> (f' \<circ>\<^sub>\<rightarrow> h)\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>X\<^esub>\<close> for v
        using that \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>e'' \<circ>\<^sub>\<rightarrow> k\<^esub>\<^sub>V v = \<^bsub>e' \<circ>\<^sub>\<rightarrow> f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close>
        by (simp add: morph_comp_def)

      have b: \<open>\<^bsub>e'' \<circ>\<^sub>\<rightarrow> k\<^esub>\<^sub>E ea = \<^bsub>e' \<circ>\<^sub>\<rightarrow> (f' \<circ>\<^sub>\<rightarrow> h)\<^esub>\<^sub>E ea\<close> if \<open>ea \<in> E\<^bsub>X\<^esub>\<close> for ea
        using that \<open>\<And>e. e \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>e'' \<circ>\<^sub>\<rightarrow> k\<^esub>\<^sub>E e = \<^bsub>e' \<circ>\<^sub>\<rightarrow> f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e\<close>
        by (simp add: morph_comp_def)

      obtain y where \<open>morphism X B y\<close> 
        and \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>k\<^esub>\<^sub>V v = \<^bsub> e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v\<close>
        and \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>k\<^esub>\<^sub>E ea = \<^bsub> e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea\<close>
        and \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g' \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close>
        and \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g' \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E ea\<close>
        using "2.universal_property"[OF \<open>graph X\<close> f'h.morphism_axioms \<open>morphism X E k\<close> a b]
        by force

      have a': \<open>\<^bsub>g' \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>X\<^esub>\<close> for v
        using that \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g' \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close>
        by (simp add: morph_comp_def)

      have b': \<open>\<^bsub>g' \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E ea\<close> if \<open>ea \<in> E\<^bsub>X\<^esub>\<close> for ea
        using that \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g' \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E ea\<close>
        by (simp add: morph_comp_def)

      obtain x where \<open>morphism X A x\<close>
        and \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
        and \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close>
        and \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
        and \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>y\<^esub>\<^sub>E ea\<close>
        using "1.universal_property"[OF \<open>graph X\<close> \<open>morphism X C h\<close> \<open>morphism X B y\<close> a' b']
        by fast

      have trv: \<open>\<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>X\<^esub>\<close> for v
      proof -
        have \<open>\<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v\<close>
          using that \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
          by (simp add: morph_comp_def)
        also have \<open>\<dots> = \<^bsub>k\<^esub>\<^sub>V v\<close>
          by (simp add: \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>k\<^esub>\<^sub>V v = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v\<close> that)
        finally show ?thesis .
      qed

      have tre: \<open>\<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>k\<^esub>\<^sub>E ea\<close> if \<open>ea \<in> E\<^bsub>X\<^esub>\<close> for ea
      proof -
        have \<open>\<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea\<close>
          using that \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>y\<^esub>\<^sub>E ea\<close>
          by (simp add: morph_comp_def)
        also have \<open>\<dots> = \<^bsub>k\<^esub>\<^sub>E ea\<close>
          by (simp add: \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>k\<^esub>\<^sub>E ea = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea\<close> that)
        finally show ?thesis .
      qed

      have uniq_y: \<open>(\<forall>v \<in> V\<^bsub>X\<^esub>. \<^bsub>uy\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e \<in> E\<^bsub>X\<^esub>. \<^bsub>uy\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)\<close>
            if \<open>morphism X B uy\<close>
            \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> uy\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v\<close>
            \<open>\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> uy\<^esub>\<^sub>E ea = \<^bsub>k\<^esub>\<^sub>E ea\<close>
            \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g' \<circ>\<^sub>\<rightarrow> uy\<^esub>\<^sub>V v = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close>
            \<open>\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g' \<circ>\<^sub>\<rightarrow> uy\<^esub>\<^sub>E e = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e\<close> for uy
        using that ex_eq[OF "2.universal_property"[OF \<open>graph X\<close> f'h.morphism_axioms \<open>morphism X E k\<close> a b], of uy y]
          \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>k\<^esub>\<^sub>E ea = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea\<close> \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>k\<^esub>\<^sub>V v = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v\<close> \<open>morphism X B y\<close> a' b'
        by fastforce


      have uniq: \<open>(\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>ux\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>ux\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v)\<close>
        if \<open>morphism X A ux\<close> 
           \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v\<close> 
           \<open>\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>E ea = \<^bsub>k\<^esub>\<^sub>E ea\<close>
           \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close> 
           \<open>\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close> for ux
      proof -
        interpret ux: morphism X A ux
          using \<open>morphism X A ux\<close>
          by assumption

            interpret fux: morphism X B \<open>f \<circ>\<^sub>\<rightarrow> ux\<close>
              using \<open>morphism X A ux\<close> 
              by (simp add: "1.b.morphism_axioms" wf_morph_comp)

            have aa: \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> (f \<circ>\<^sub>\<rightarrow> ux)\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v\<close>
              by (simp add: morph_assoc_nodes that(2))

            have bb: \<open>\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> (f \<circ>\<^sub>\<rightarrow> ux)\<^esub>\<^sub>E ea = \<^bsub>k\<^esub>\<^sub>E ea\<close>
              by (simp add: morph_assoc_edges that(3))

            have cc: \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g' \<circ>\<^sub>\<rightarrow> (f \<circ>\<^sub>\<rightarrow> ux)\<^esub>\<^sub>V v = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close>
              using \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>  "1.node_commutativity" ux.morph_node_range
              by (simp add: morph_comp_def)

            have dd: \<open>\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g' \<circ>\<^sub>\<rightarrow> (f \<circ>\<^sub>\<rightarrow> ux)\<^esub>\<^sub>E e = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e\<close>
              using \<open>\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close> "1.edge_commutativity" ux.morph_edge_range
              by (simp add: morph_comp_def)


        have a''': \<open>morphism X A x \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e)\<close>
          by (simp add: \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>y\<^esub>\<^sub>E ea\<close> \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close> \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close> \<open>morphism X A x\<close>)

        have b''': \<open>morphism X A ux \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e)\<close>
        proof (intro conjI)
          show \<open>morphism X A ux\<close>
            using \<open>morphism X A ux\<close>
            by assumption
        next
          show \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
          proof -

            show ?thesis
              using uniq_y[OF fux.morphism_axioms aa bb cc dd]
              by simp
          qed
        next
          show \<open>\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
            using uniq_y[OF fux.morphism_axioms aa bb cc dd]
            by simp
        next
          show \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
            using that(4) 
            by assumption
        next
          show \<open>\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e \<close>
            using that(5) 
            by assumption
        qed

          show ?thesis
            using ex_eq[OF "1.universal_property"[OF \<open>graph X\<close> \<open>morphism X C h\<close> \<open>morphism X B y\<close> a' b'] a''' b''']
            by simp
      qed

      show ?thesis
      proof (rule_tac x = x in exI, intro conjI)
        show \<open>morphism X A x\<close>
          using  \<open>morphism X A x\<close> 
          by assumption
      next
        show \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v\<close>
          by (simp add: trv)
      next
        show \<open>\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>k\<^esub>\<^sub>E ea\<close>
          by (simp add: tre)
      next
        show \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
          by (simp add: \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>)
      next
        show \<open>\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close>
          by (simp add: \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close>)
      next
        show \<open>\<forall>y. morphism X A y \<and>
        (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>k\<^esub>\<^sub>V v) \<and>
        (\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea = \<^bsub>k\<^esub>\<^sub>E ea) \<and>
        (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v) \<and> (\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea) \<longrightarrow>
        (\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>y\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>y\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v)\<close>
          by (simp add: uniq)
      qed
    qed
  qed
qed



lemma pullback_decomposition:
  assumes
    f:  \<open>morphism A B f\<close> and
    f': \<open>morphism C D f'\<close> and
    2: \<open>pullback_diagram B E D F e g' e'' e'\<close> and
    "1+2":  \<open>pullback_diagram A E C F (e \<circ>\<^sub>\<rightarrow> f) g  e'' (e' \<circ>\<^sub>\<rightarrow> f')\<close> and
    "1cv": \<open>\<And>v. v \<in> V\<^bsub>A\<^esub> \<Longrightarrow> \<^bsub>g' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v\<close> and
    "1ce": \<open>\<And>ea. ea \<in> E\<^bsub>A\<^esub> \<Longrightarrow> \<^bsub>g' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E ea = \<^bsub>f' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E ea\<close>
 

  shows \<open>pullback_diagram A B C D f g g' f'\<close>
proof -
  interpret 2: pullback_diagram B E D F e g' e'' e'
    using 2 by assumption

  interpret "1+2": pullback_diagram A E C F \<open>e \<circ>\<^sub>\<rightarrow> f\<close> g  e'' \<open>e' \<circ>\<^sub>\<rightarrow> f'\<close>
    using "1+2" by assumption

  interpret f: morphism A B f
    using f by assumption

  interpret f': morphism C D f'
    using f' by assumption

  show ?thesis
  proof
    show \<open>\<^bsub>g' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A\<^esub>\<close> for v
      using "1cv"[OF that] by assumption
  next
    show \<open>\<^bsub>g' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f' \<circ>\<^sub>\<rightarrow> g\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A\<^esub>\<close> for e
      using "1ce"[OF that] by assumption
  next
    show \<open>Ex1M
        (\<lambda>x. morphism X A x \<and>
             (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
             (\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<and> 
             (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v) \<and> 
             (\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e))
        X\<close>
      if \<open>graph X\<close>
      \<open>morphism X C h\<close>
      \<open>morphism X B y\<close>
      \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g' \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close>
      \<open>\<And>e. e \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g' \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e\<close>
    for X :: "('c,'d) ngraph" and h y
    proof -

      interpret X: graph X
        using \<open>graph X\<close> by assumption

      interpret h: morphism X C h
        using \<open>morphism X C h\<close> by assumption

      interpret y: morphism X B y
        using \<open>morphism X B y\<close> by assumption

      interpret k: morphism X E \<open>e \<circ>\<^sub>\<rightarrow> y\<close>
        using wf_morph_comp[OF y.morphism_axioms "2.b.morphism_axioms"]
        by assumption

      have a: \<open>\<^bsub>e'' \<circ>\<^sub>\<rightarrow> (e \<circ>\<^sub>\<rightarrow> y)\<^esub>\<^sub>V v = \<^bsub>e' \<circ>\<^sub>\<rightarrow> f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>X\<^esub>\<close> for v
        using that "2.node_commutativity" \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g' \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close> y.morph_node_range
        by (simp add: morph_assoc_nodes morph_comp_def)

      have b: \<open>\<^bsub>e'' \<circ>\<^sub>\<rightarrow> (e \<circ>\<^sub>\<rightarrow> y)\<^esub>\<^sub>E ea = \<^bsub>e' \<circ>\<^sub>\<rightarrow> f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E ea\<close> if \<open>ea \<in> E\<^bsub>X\<^esub>\<close> for ea
         using that "2.edge_commutativity" \<open>\<And>e. e \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g' \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e\<close> y.morph_edge_range
        by (simp add: morph_assoc_edges morph_comp_def)

      obtain x where \<open>morphism X A x\<close>
        and \<open>\<And>v .  v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
        and \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close>
        and \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v\<close>
        and \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea\<close>
        using "1+2.universal_property"[OF X.graph_axioms h.morphism_axioms k.morphism_axioms a b]
        by fast

      interpret x: morphism X A x
        using \<open>morphism X A x\<close> by assumption

      interpret f'h: morphism X D \<open>f' \<circ>\<^sub>\<rightarrow> h\<close>
        using wf_morph_comp[OF h.morphism_axioms f'.morphism_axioms]
        by assumption

      have a': \<open>\<^bsub>e'' \<circ>\<^sub>\<rightarrow> (e \<circ>\<^sub>\<rightarrow> y)\<^esub>\<^sub>V v = \<^bsub>e' \<circ>\<^sub>\<rightarrow> (f' \<circ>\<^sub>\<rightarrow> h)\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>X\<^esub>\<close> for v
        using that a
        by (simp add: morph_assoc_nodes)
      have b': \<open>\<^bsub>e'' \<circ>\<^sub>\<rightarrow> (e \<circ>\<^sub>\<rightarrow> y)\<^esub>\<^sub>E ea = \<^bsub>e' \<circ>\<^sub>\<rightarrow> (f' \<circ>\<^sub>\<rightarrow> h)\<^esub>\<^sub>E ea\<close> if \<open>ea \<in> E\<^bsub>X\<^esub>\<close> for ea
        using that b       
        by (simp add: morph_assoc_edges)

      have aa: \<open>morphism X B y \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v) \<and> (\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea) \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g' \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g' \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E e = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e)\<close>
        using that(4) that(5) y.morphism_axioms 
        by simp

      have bb: \<open>morphism X B (f \<circ>\<^sub>\<rightarrow> x) 
                \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> (f \<circ>\<^sub>\<rightarrow> x)\<^esub>\<^sub>V v = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v) 
                \<and> (\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> (f \<circ>\<^sub>\<rightarrow> x)\<^esub>\<^sub>E ea = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea) 
                \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g' \<circ>\<^sub>\<rightarrow> (f \<circ>\<^sub>\<rightarrow> x)\<^esub>\<^sub>V v = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v) 
                \<and> (\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g' \<circ>\<^sub>\<rightarrow> (f \<circ>\<^sub>\<rightarrow> x)\<^esub>\<^sub>E e = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e)\<close>
       proof (intro conjI)
        show \<open>morphism X B (f \<circ>\<^sub>\<rightarrow> x)\<close>
          using wf_morph_comp[OF \<open>morphism X A x\<close> f]
          by assumption
        next
          show \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> (f \<circ>\<^sub>\<rightarrow> x)\<^esub>\<^sub>V v = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v\<close>
          using \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v\<close>
          by (simp add: morph_assoc_nodes)
      next
        show \<open>\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> (f \<circ>\<^sub>\<rightarrow> x)\<^esub>\<^sub>E ea = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea\<close>
          using \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea\<close>
          by (simp add: morph_assoc_edges)
      next
        show \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g' \<circ>\<^sub>\<rightarrow> (f \<circ>\<^sub>\<rightarrow> x)\<^esub>\<^sub>V v = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close>
          using "1cv" \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
          by (simp add: morph_assoc_nodes morph_comp_def x.morph_node_range)
      next
        show \<open>\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g' \<circ>\<^sub>\<rightarrow> (f \<circ>\<^sub>\<rightarrow> x)\<^esub>\<^sub>E e = \<^bsub>f' \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e \<close>
          using "1ce" \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close>
          by (simp add: morph_assoc_edges morph_comp_def x.morph_edge_range)
      qed    


      have uniq: \<open>(\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>ux\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>ux\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v)\<close>
        if \<open>morphism X A ux\<close>
           \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
           \<open>\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
           \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
           \<open>\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e\<close>
        for ux
      proof -
        have bbb: \<open>morphism X A x 
                    \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v) 
                    \<and> (\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea) 
                    \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v) 
                    \<and> (\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e)\<close>
          by (simp add: \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea\<close> 
                        \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close> 
                        \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v\<close>
                        \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close> x.morphism_axioms)
    
        have aaa: \<open>morphism X A ux 
                    \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>V v = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v) 
                    \<and> (\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>E ea = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea) 
                    \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v) 
                    \<and> (\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e)\<close>
        proof (intro conjI)
          show \<open>morphism X A ux\<close>
            using \<open>morphism X A ux\<close> by assumption
        next
          show \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>V v = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>V v\<close>
            using  \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
            by (simp add: morph_comp_def)
        next
          show \<open>\<forall>ea\<in>E\<^bsub>X\<^esub>. \<^bsub>e \<circ>\<^sub>\<rightarrow> f \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>E ea = \<^bsub>e \<circ>\<^sub>\<rightarrow> y\<^esub>\<^sub>E ea\<close>
            using \<open>\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close> 
            by (simp add: morph_comp_def)
        next
          show \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
            using \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close> by assumption
        next
          show \<open>\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e\<close>
            using \<open>\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ux\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e\<close> by assumption
        qed


        show ?thesis
          using ex_eq[OF "1+2.universal_property"[OF X.graph_axioms h.morphism_axioms k.morphism_axioms a b] aaa bbb]
          by simp
      qed

      show ?thesis
      proof (rule_tac x=x in exI, intro conjI)
        show \<open>morphism X A x\<close>
          using \<open>morphism X A x\<close> by assumption
      next
        show \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
          using ex_eq[OF "2.universal_property"[OF X.graph_axioms f'h.morphism_axioms k.morphism_axioms a' b'] bb aa]
          by simp
      next
        show \<open>\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
          using ex_eq[OF "2.universal_property"[OF X.graph_axioms f'h.morphism_axioms k.morphism_axioms a' b'] bb aa]
          by simp
      next
        show \<open>\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>
          by (simp add: \<open>\<And>v. v \<in> V\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v\<close>)
      next
        show \<open>\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e\<close>
          by (simp add: \<open>\<And>ea. ea \<in> E\<^bsub>X\<^esub> \<Longrightarrow> \<^bsub>g \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E ea = \<^bsub>h\<^esub>\<^sub>E ea\<close>)
      next
        show \<open>\<forall>ya. morphism X A ya \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> ya\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> ya\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ya\<^esub>\<^sub>V v = \<^bsub>h\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>g \<circ>\<^sub>\<rightarrow> ya\<^esub>\<^sub>E e = \<^bsub>h\<^esub>\<^sub>E e) \<longrightarrow> (\<forall>e\<in>E\<^bsub>X\<^esub>. \<^bsub>ya\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>X\<^esub>. \<^bsub>ya\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v)\<close>
          using uniq
          by simp
    qed
  qed
qed
qed
end