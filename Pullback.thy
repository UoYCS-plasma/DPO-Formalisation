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

lemma pb_bij:
  fixes A' u
  assumes 
    A': \<open>graph A'\<close> and
    u:  \<open>bijective_morphism A A' u\<close> 
  obtains b' and c' where \<open>pullback_diagram A' B C D b' c' f g\<close>
  sorry


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
    sorry
qed

end

end