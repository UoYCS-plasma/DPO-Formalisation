theory DirectDerivation
  imports Rule Gluing Deletion
begin


(* GRAT PDF P. 114 *)
locale direct_derivation = 
  r: rule r b b' +
  gi: injective_morphism "lhs r" G g  + 
  po1: pushout_diagram "interf r" "lhs r" D G b d g c +
  po2: pushout_diagram "interf r" "rhs r" D H b' d f c'
  for r b b' G g D d c H f c'
begin

  sublocale d_inj: injective_morphism "interf r" D d
    using po1.b_f_inj_imp_c_inj[OF r.k.injective_morphism_axioms gi.injective_morphism_axioms]
    by assumption

  sublocale pb1: pullback_diagram "interf r" "lhs r" D G b d g c
    using po1.pushout_pullback_inj_b[OF r.k.injective_morphism_axioms d_inj.injective_morphism_axioms]
    by assumption


sublocale pb2: pullback_diagram "interf r" "rhs r" D H b' d f c'
  using po2.pushout_pullback_inj_b[OF r.r.injective_morphism_axioms d_inj.injective_morphism_axioms]
  by assumption

theorem uniqueness_direct_derivation:
  assumes 
    dd2: \<open>direct_derivation r b b' G g D' d' m H' f' m'\<close>
  shows \<open>(\<exists>u. bijective_morphism D D' u) \<and> 
          (\<exists>u. bijective_morphism H H' u)\<close>
proof -
  interpret dd2: direct_derivation r b b' G g D' d' m H' f' m'
    using dd2 by assumption


  interpret g: injective_morphism "lhs r" G g
    using gi.injective_morphism_axioms 
    by assumption

  interpret dd_inj: injective_morphism "interf r" D' d'
    using dd2.po1.b_f_inj_imp_c_inj[OF r.k.injective_morphism_axioms gi.injective_morphism_axioms]
    by assumption

    (*   front left face
           po1
         bottom face
           dd2.po1
     *)

    (* front right *)      
  interpret fr: pullback_construction D G D' c m ..

    (* back left *)
interpret bl: pullback_diagram "interf r" "interf r" 
                "interf r" "lhs r" idM idM b b
  using fun_algrtr_4_7_2[OF r.k.injective_morphism_axioms]
  by assumption

    (* back right *)
    interpret pb_frontleft: pullback_diagram "interf r" "lhs r" D' G b d' g m
      using dd2.pb1.pullback_diagram_axioms
      by assumption

interpret backside: pullback_diagram "interf r" D' "interf r" G 
                      \<open>d' \<circ>\<^sub>\<rightarrow> idM\<close> idM m \<open>g \<circ>\<^sub>\<rightarrow> b\<close>
  using pullback_composition[OF bl.pullback_diagram_axioms 
                                dd2.pb1.flip_diagram] 
  by assumption

  define h where
    \<open>h \<equiv> \<lparr>node_map = \<lambda>v. (\<^bsub>d\<^esub>\<^sub>V v, \<^bsub>d'\<^esub>\<^sub>V v)
         ,edge_map = \<lambda>e. (\<^bsub>d\<^esub>\<^sub>E e, \<^bsub>d'\<^esub>\<^sub>E e)\<rparr>\<close>

    interpret h: morphism "interf r" fr.A h
    proof
      show \<open>\<^bsub>h\<^esub>\<^sub>E e \<in> E\<^bsub>fr.A\<^esub>\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
        using that fr.pb.edge_commutativity po1.c.morph_edge_range po1.edge_commutativity 
              dd2.po1.edge_commutativity dd2.po1.c.morph_edge_range
        by(simp add: fr.A_def h_def fr.b_def morph_comp_def fr.c_def)
    next
      show \<open>\<^bsub>h\<^esub>\<^sub>V v \<in> V\<^bsub>fr.A\<^esub>\<close> if \<open>v \<in> V\<^bsub>interf r\<^esub>\<close> for v
        using that fr.pb.node_commutativity po1.c.morph_node_range po1.node_commutativity dd2.po1.node_commutativity dd2.po1.c.morph_node_range
        by (simp add: fr.A_def h_def fr.b_def morph_comp_def fr.c_def)
    next
      show \<open>\<^bsub>h\<^esub>\<^sub>V (s\<^bsub>interf r\<^esub> e) = s\<^bsub>fr.A\<^esub> (\<^bsub>h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
        using that
        by (simp add: po1.c.source_preserve dd2.po1.c.source_preserve fr.A_def h_def)
    next
      show \<open>\<^bsub>h\<^esub>\<^sub>V (t\<^bsub>interf r\<^esub> e) = t\<^bsub>fr.A\<^esub> (\<^bsub>h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
        using that
        by (simp add: po1.c.target_preserve dd2.po1.c.target_preserve fr.A_def h_def)
    next
      show \<open>l\<^bsub>interf r\<^esub> v = l\<^bsub>fr.A\<^esub> (\<^bsub>h\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>interf r\<^esub>\<close> for v
        using that
        by (simp add: fr.A_def h_def po1.c.label_preserve)
    next
      show \<open>m\<^bsub>interf r\<^esub> e = m\<^bsub>fr.A\<^esub> (\<^bsub>h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
        using that
        by (simp add: fr.A_def h_def po1.c.mark_preserve)
    qed

   (*  k: U \<rightarrow> C' = fr.c*)
  (* top square commutativity *)
    have a: \<open>\<^bsub>d' \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v = \<^bsub>fr.c \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^esub>\<close> for v
      using that
      by (simp add: h_def fr.c_def morph_comp_def)

    have b: \<open>\<^bsub>d' \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e = \<^bsub>fr.c \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
      using that
      by (simp add: h_def fr.c_def morph_comp_def)
(* bottom square commutes is assumption *)
    have \<open>\<^bsub>g \<circ>\<^sub>\<rightarrow> b\<^esub>\<^sub>V v = \<^bsub>c \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^esub>\<close> for v
      using po1.node_commutativity that by blast
    have *: \<open>d' \<circ>\<^sub>\<rightarrow> idM = fr.c \<circ>\<^sub>\<rightarrow> h\<close>
      by (simp add: h_def fr.c_def morph_comp_def comp_def)

   interpret frontside: pullback_diagram "interf r" D' "interf r" G \<open>fr.c \<circ>\<^sub>\<rightarrow> h\<close> idM m \<open>c \<circ>\<^sub>\<rightarrow> d\<close>
    proof intro_locales
      show \<open>morphism_axioms (interf r) D' (fr.c \<circ>\<^sub>\<rightarrow> h)\<close>
        using \<open>d' \<circ>\<^sub>\<rightarrow> idM = fr.c \<circ>\<^sub>\<rightarrow> h\<close> backside.b.morphism_axioms morphism.axioms(3) by auto
    next
      show \<open>morphism_axioms (interf r) G (c \<circ>\<^sub>\<rightarrow> d)\<close>
        using po1.c.morphism_axioms po1.g.morphism_axioms morphism_def wf_morph_comp by blast
    next
      show \<open>pullback_diagram_axioms (interf r) D' (interf r) (fr.c \<circ>\<^sub>\<rightarrow> h) idM m (c \<circ>\<^sub>\<rightarrow> d)\<close>
      proof
        show \<open>\<^bsub>m \<circ>\<^sub>\<rightarrow> (fr.c \<circ>\<^sub>\<rightarrow> h)\<^esub>\<^sub>V v = \<^bsub>c \<circ>\<^sub>\<rightarrow> d \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^esub>\<close> for v
          using that backside.node_commutativity po1.node_commutativity
          by (simp add: morph_assoc_nodes fr.c_def morph_comp_def h_def)
      next
        show \<open>\<^bsub>m \<circ>\<^sub>\<rightarrow> (fr.c \<circ>\<^sub>\<rightarrow> h)\<^esub>\<^sub>E e = \<^bsub>c \<circ>\<^sub>\<rightarrow> d \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
          using that backside.edge_commutativity po1.edge_commutativity
          by (simp add: morph_assoc_nodes fr.c_def morph_comp_def h_def)
      next
        show \<open>Ex1M
        (\<lambda>x. morphism A' (interf r) x \<and>
             (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>fr.c \<circ>\<^sub>\<rightarrow> h \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and>
             (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>fr.c \<circ>\<^sub>\<rightarrow> h \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and>
             (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e))
        A'\<close> 
          if \<open>graph A'\<close> \<open>morphism A' (interf r) c'\<close> \<open>morphism A' D' b'\<close>
             \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>m \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>c \<circ>\<^sub>\<rightarrow> d \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close>
             \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>m \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>c \<circ>\<^sub>\<rightarrow> d \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close> for A' :: "('g,'h) ngraph" and c' b'
        proof -
          interpret c': morphism A' "interf r" c'
            using \<open>morphism A' (interf r) c'\<close> by assumption

          have \<open>\<^bsub>m \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> b \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A'\<^esub>\<close> for v
            using that \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>m \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>c \<circ>\<^sub>\<rightarrow> d \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close> backside.node_commutativity
              c'.morph_node_range h.morph_node_range
            by (simp add: morph_comp_def h_def fr.A_def)

          moreover have \<open>\<^bsub>m \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> b \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A'\<^esub>\<close> for e
            using that \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>m \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>c \<circ>\<^sub>\<rightarrow> d \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close> backside.edge_commutativity
              c'.morph_edge_range h.morph_edge_range
            by (simp add: morph_comp_def h_def fr.A_def)


          ultimately show ?thesis
          using backside.universal_property[OF \<open>graph A'\<close> \<open>morphism A' (interf r) c'\<close> \<open>morphism A' D' b'\<close> ] *
          by auto
      qed
    qed
  qed

   interpret back_right: pullback_diagram "interf r" fr.A "interf r" D h idM fr.b d
    proof -
    have \<open>\<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v = \<^bsub>d \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^esub>\<close> for v
      using that
      by (simp add: fr.b_def h_def morph_comp_def)
    moreover have \<open>\<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e = \<^bsub>d \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
      using that
      by (simp add: fr.b_def h_def morph_comp_def)

    ultimately show \<open>pullback_diagram (interf r) fr.A (interf r) D h idM fr.b d\<close>
        using pullback_decomposition[OF h.morphism_axioms po1.c.morphism_axioms fr.pb.flip_diagram frontside.pullback_diagram_axioms]
        by simp
    qed


    (* top face *)
    interpret top: pushout_diagram "interf r" "interf r" fr.A D' idM h d' fr.c
    proof -
(* 
      interpret bottom: pullback_diagram "interf r" "lhs r" D G b d g c
        using po1.pushout_pullback_inj_b[OF r.k.injective_morphism_axioms d.injective_morphism_axioms]
        by assumption
 *)
      interpret bls: pullback_diagram "interf r" D "interf r" G \<open>d \<circ>\<^sub>\<rightarrow> idM\<close> idM c \<open>g \<circ>\<^sub>\<rightarrow> b\<close>
        using pullback_composition[OF bl.pullback_diagram_axioms  pb1.flip_diagram]
        by assumption

(* righthand commutative square *)
      have a: \<open>\<^bsub>d \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v = \<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^esub>\<close> for v
        by (simp add: fr.b_def h_def morph_comp_def)
      have b: \<open>\<^bsub>d \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e = \<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
        by (simp add: fr.b_def h_def morph_comp_def)

    interpret brs: pullback_diagram "interf r" D "interf r" G \<open>fr.b \<circ>\<^sub>\<rightarrow> h\<close> idM c \<open>m \<circ>\<^sub>\<rightarrow> d'\<close>
      proof intro_locales
        show \<open>morphism_axioms (interf r) D (fr.b \<circ>\<^sub>\<rightarrow> h)\<close>
          using fr.b.morphism_axioms h.morphism_axioms morphism_def wf_morph_comp by blast
      next
        show \<open>morphism_axioms (interf r) G (m \<circ>\<^sub>\<rightarrow> d')\<close>
          using  morphism.axioms(3)[OF wf_morph_comp[OF dd2.po1.c.morphism_axioms dd2.po1.g.morphism_axioms]]
          by assumption
      next
        show \<open>pullback_diagram_axioms (interf r) D (interf r) (fr.b \<circ>\<^sub>\<rightarrow> h) idM c (m \<circ>\<^sub>\<rightarrow> d')\<close>
        proof
          show \<open>\<^bsub>c \<circ>\<^sub>\<rightarrow> (fr.b \<circ>\<^sub>\<rightarrow> h)\<^esub>\<^sub>V v = \<^bsub>m \<circ>\<^sub>\<rightarrow> d' \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^esub>\<close> for v
            using that dd2.po1.node_commutativity bls.node_commutativity
            by (simp add: morph_comp_def morph_assoc_nodes fr.b_def h_def)
        next
          show \<open>\<^bsub>c \<circ>\<^sub>\<rightarrow> (fr.b \<circ>\<^sub>\<rightarrow> h)\<^esub>\<^sub>E e = \<^bsub>m \<circ>\<^sub>\<rightarrow> d' \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
            using that dd2.po1.edge_commutativity bls.edge_commutativity
            by (simp add: morph_comp_def morph_assoc_nodes fr.b_def h_def)
        next
          show \<open>Ex1M (\<lambda>x. morphism A' (interf r) x 
                  \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) 
                  \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) 
                  \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>c'a\<^esub>\<^sub>V v) 
                  \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>c'a\<^esub>\<^sub>E e)) A'\<close>
            if \<open>graph A'\<close> \<open>morphism A' (interf r) c'a\<close> \<open>morphism A' D b'\<close> 
               \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>c \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>m \<circ>\<^sub>\<rightarrow> d' \<circ>\<^sub>\<rightarrow> c'a\<^esub>\<^sub>V v\<close>
               \<open>\<And>e. e \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>c \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>m \<circ>\<^sub>\<rightarrow> d' \<circ>\<^sub>\<rightarrow> c'a\<^esub>\<^sub>E e\<close>
            for A' :: "('g,'h) ngraph" and c'a b'
          proof -
            interpret c'a: morphism A' "interf r" c'a
              using \<open>morphism A' (interf r) c'a\<close> by assumption

            interpret b': morphism A' D b'
              using \<open>morphism A' D b'\<close> by assumption

            have a: \<open>\<^bsub>c \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>g \<circ>\<^sub>\<rightarrow> b \<circ>\<^sub>\<rightarrow> c'a\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>A'\<^esub>\<close> for v
              using that \<open>\<And>v. v \<in> V\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>c \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>m \<circ>\<^sub>\<rightarrow> d' \<circ>\<^sub>\<rightarrow> c'a\<^esub>\<^sub>V v\<close> dd2.po1.node_commutativity
              by (simp add: morph_comp_def c'a.morph_node_range)

            have b: \<open>\<^bsub>c \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>g \<circ>\<^sub>\<rightarrow> b \<circ>\<^sub>\<rightarrow> c'a\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>A'\<^esub>\<close> for e
              using that  \<open>\<And>ea. ea \<in> E\<^bsub>A'\<^esub> \<Longrightarrow> \<^bsub>c \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E ea = \<^bsub>m \<circ>\<^sub>\<rightarrow> d' \<circ>\<^sub>\<rightarrow> c'a\<^esub>\<^sub>E ea\<close> dd2.po1.edge_commutativity
              by (simp add: morph_comp_def c'a.morph_edge_range)
            
            have s: \<open>(\<lambda>x. morphism A' (interf r) x \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>d \<circ>\<^sub>\<rightarrow> idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) 
                    \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>d \<circ>\<^sub>\<rightarrow> idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>c'a\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>c'a\<^esub>\<^sub>E e)) = (\<lambda>x. morphism A' (interf r) x \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>b'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>fr.b \<circ>\<^sub>\<rightarrow> h \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>b'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>V v = \<^bsub>c'a\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>A'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> x\<^esub>\<^sub>E e = \<^bsub>c'a\<^esub>\<^sub>E e))\<close>
              by (simp add: morph_comp_def fr.b_def h_def)

            show  ?thesis
              using ex1m_eq_surrogate[OF s bls.universal_property[OF \<open>graph A'\<close> \<open>morphism A' (interf r) c'a\<close> \<open>morphism A' D b'\<close> a b]]
              by simp
          qed
        qed
      qed


      interpret top_pb: pullback_diagram "interf r" "interf r" fr.A D' idM h d' fr.c
        using pullback_decomposition[OF _ _ fr.pb.pullback_diagram_axioms brs.pullback_diagram_axioms]
        using "*" h.morphism_axioms dd2.po1.c.morphism_axioms pullback_diagram.flip_diagram by force

      interpret h: injective_morphism "interf r" fr.A h
      proof
        show \<open>inj_on \<^bsub>h\<^esub>\<^sub>V V\<^bsub>interf r\<^esub>\<close>
          using d_inj.inj_nodes
          by (simp add: h_def inj_on_def)
      next
        show \<open>inj_on \<^bsub>h\<^esub>\<^sub>E E\<^bsub>interf r\<^esub>\<close>
          using d_inj.inj_edges
          by (simp add: h_def inj_on_def)
      qed


      have a:\<open>(\<exists>v\<in>V\<^bsub>interf r\<^esub>. \<^bsub>d'\<^esub>\<^sub>V v = x) \<or> (\<exists>v\<in>V\<^bsub>fr.A\<^esub>. \<^bsub>fr.c\<^esub>\<^sub>V v = x)\<close> if \<open>x \<in> V\<^bsub>D'\<^esub>\<close> for x
        using that
        apply (simp add: fr.A_def fr.c_def)
        using r.k.injective_morphism_axioms dd2.d_inj.injective_morphism_axioms po1.joint_surjectivity_nodes dd2.po1.g.morph_node_range dd2.po1.reduced_chain_condition_nodes by blast

      have b: \<open>(\<exists>e\<in>E\<^bsub>interf r\<^esub>. \<^bsub>d'\<^esub>\<^sub>E e = x) \<or> (\<exists>e\<in>E\<^bsub>fr.A\<^esub>. \<^bsub>fr.c\<^esub>\<^sub>E e = x)\<close> if \<open>x \<in> E\<^bsub>D'\<^esub>\<close> for x
        using that
        apply (simp add: fr.A_def fr.c_def)
        using r.k.injective_morphism_axioms dd2.d_inj.injective_morphism_axioms dd2.po1.g.morph_edge_range po1.joint_surjectivity_edges morphism.morph_edge_range dd2.po1.reduced_chain_condition_edges 
        by blast

      interpret k_inj: injective_morphism fr.A D' fr.c
        using pullback_diagram.g_inj_imp_b_inj[OF fr.pb.flip_diagram po1.b_inj_imp_g_inj[OF r.k.injective_morphism_axioms]]
        by assumption


      have a': \<open>(\<exists>v\<in>V\<^bsub>fr.A\<^esub>. \<^bsub>fr.c\<^esub>\<^sub>V v = x) \<or> (\<exists>v\<in>V\<^bsub>interf r\<^esub>. \<^bsub>d'\<^esub>\<^sub>V v = x)\<close> if \<open>x \<in> V\<^bsub>D'\<^esub>\<close> for x
        using that a by auto
      have b': \<open>(\<exists>e\<in>E\<^bsub>fr.A\<^esub>. \<^bsub>fr.c\<^esub>\<^sub>E e = x) \<or> (\<exists>e\<in>E\<^bsub>interf r\<^esub>. \<^bsub>d'\<^esub>\<^sub>E e = x)\<close> if \<open>x \<in> E\<^bsub>D'\<^esub>\<close> for x
        using that b by auto 

      show \<open>pushout_diagram (interf r) (interf r) fr.A D' idM h d' fr.c\<close>
        using po_characterization[of "interf r" "interf r" idM fr.A h D' d' fr.c]
        using a' b' r.k.G.idm.injective_morphism_axioms dd2.d_inj.injective_morphism_axioms 
          h.injective_morphism_axioms k_inj.injective_morphism_axioms 
          top_pb.edge_commutativity top_pb.node_commutativity top_pb.reduced_chain_condition_edges
          top_pb.reduced_chain_condition_nodes 
        by fastforce
    qed

interpret k_bij: bijective_morphism fr.A D' fr.c
  using top.b_bij_imp_g_bij[OF r.k.G.idm.bijective_morphism_axioms]
  by assumption

    obtain kinv where kinv: \<open>bijective_morphism D' fr.A kinv\<close>
      and \<open>\<And>v. v \<in> V\<^bsub>fr.A\<^esub> \<Longrightarrow> \<^bsub>kinv \<circ>\<^sub>\<rightarrow> fr.c\<^esub>\<^sub>V v = v\<close> \<open>\<And>e. e \<in> E\<^bsub>fr.A\<^esub> \<Longrightarrow> \<^bsub>kinv \<circ>\<^sub>\<rightarrow> fr.c\<^esub>\<^sub>E e = e\<close>
      and \<open>\<And>v. v \<in> V\<^bsub>D'\<^esub> \<Longrightarrow> \<^bsub>fr.c \<circ>\<^sub>\<rightarrow> kinv\<^esub>\<^sub>V v = v\<close> \<open>\<And>e. e \<in> E\<^bsub>D'\<^esub> \<Longrightarrow> \<^bsub>fr.c \<circ>\<^sub>\<rightarrow> kinv\<^esub>\<^sub>E e = e\<close>
      by (metis k_bij.ex_inv)

    interpret kinv: bijective_morphism D' fr.A kinv
      using kinv by assumption

    (* here starts l *)
    interpret h: injective_morphism fr.A D fr.b
      using fr.pb.g_inj_imp_b_inj[OF dd2.po1.b_inj_imp_g_inj[OF r.k.injective_morphism_axioms]]
      by assumption

    interpret br: pushout_diagram "interf r" fr.A "interf r" D h idM fr.b d
    proof -
      have a: \<open>\<exists>a\<in>V\<^bsub>interf r\<^esub>. (\<^bsub>h\<^esub>\<^sub>V a = x \<and>  \<^bsub>idM\<^esub>\<^sub>V a = y)\<close> 
        if \<open>x \<in> V\<^bsub>fr.A\<^esub>\<close> \<open> y \<in> V\<^bsub>interf r\<^esub>\<close> \<open>\<^bsub>fr.b\<^esub>\<^sub>V x = \<^bsub>d\<^esub>\<^sub>V y \<close> for x y
        using back_right.reduced_chain_condition_nodes[OF that] by simp
      
      have b: \<open>\<exists>a\<in>E\<^bsub>interf r\<^esub>. (\<^bsub>h\<^esub>\<^sub>E a = x \<and> \<^bsub>idM\<^esub>\<^sub>E a = y)\<close> 
        if \<open>x \<in> E\<^bsub>fr.A\<^esub>\<close> \<open> y \<in> E\<^bsub>interf r\<^esub>\<close> \<open> \<^bsub>fr.b\<^esub>\<^sub>E x = \<^bsub>d\<^esub>\<^sub>E y \<close> for x y
        using back_right.reduced_chain_condition_edges[OF that] by simp

      have cc: \<open>(\<exists>v\<in>V\<^bsub>interf r\<^esub>. \<^bsub>d\<^esub>\<^sub>V v = x) \<or> (\<exists>v\<in>V\<^bsub>fr.A\<^esub>. \<^bsub>fr.b\<^esub>\<^sub>V v = x)\<close> if \<open>x \<in> V\<^bsub>D\<^esub> \<close> for x
        using that
        using  r.k.injective_morphism_axioms fr.reduced_chain_condition_nodes 
          po1.g.morph_node_range dd2.po1.joint_surjectivity_nodes 
          po1.reduced_chain_condition_nodes
        by (metis d_inj.injective_morphism_axioms)

      have dd: \<open>(\<exists>e\<in>E\<^bsub>interf r\<^esub>. \<^bsub>d\<^esub>\<^sub>E e = x) \<or> (\<exists>e\<in>E\<^bsub>fr.A\<^esub>. \<^bsub>fr.b\<^esub>\<^sub>E e = x)\<close> if \<open>x \<in> E\<^bsub>D\<^esub> \<close> for x
        using that
        by (metis r.k.injective_morphism_axioms d_inj.injective_morphism_axioms 
            fr.reduced_chain_condition_edges po1.g.morph_edge_range 
            dd2.po1.joint_surjectivity_edges po1.reduced_chain_condition_edges)

      show \<open>pushout_diagram (interf r) fr.A (interf r) D h idM fr.b d\<close>
        using po_characterization[
            OF back_right.g_inj_imp_b_inj[OF d_inj.injective_morphism_axioms] r.k.G.idm.injective_morphism_axioms h.injective_morphism_axioms
            d_inj.injective_morphism_axioms back_right.node_commutativity back_right.edge_commutativity a b cc dd]
        by blast
    qed

    interpret l_bij: bijective_morphism fr.A D fr.b
    proof -
      interpret pushout_diagram "interf r" "interf r" fr.A D idM h d fr.b
        using br.flip_diagram by assumption

      show \<open>bijective_morphism fr.A D fr.b\<close>
        using b_bij_imp_g_bij[OF r.k.G.idm.bijective_morphism_axioms]
        by assumption
    qed

obtain linv where linv:\<open>bijective_morphism D fr.A linv\<close>
  and \<open>\<And>v. v \<in> V\<^bsub>D\<^esub>\<Longrightarrow> \<^bsub>fr.b \<circ>\<^sub>\<rightarrow>linv\<^esub>\<^sub>V v = v\<close> 
      \<open>\<And>e. e \<in> E\<^bsub>D\<^esub>\<Longrightarrow> \<^bsub>fr.b \<circ>\<^sub>\<rightarrow>linv\<^esub>\<^sub>E e = e\<close>
  and \<open>\<And>v. v \<in> V\<^bsub>fr.A\<^esub>\<Longrightarrow> \<^bsub>linv \<circ>\<^sub>\<rightarrow> fr.b \<^esub>\<^sub>V v = v\<close> 
      \<open>\<And>e. e \<in> E\<^bsub>fr.A\<^esub>\<Longrightarrow> \<^bsub>linv \<circ>\<^sub>\<rightarrow> fr.b \<^esub>\<^sub>E e= e\<close>
  by (metis l_bij.ex_inv)

    interpret linv: bijective_morphism D fr.A linv
      using linv by assumption

define u where \<open>u \<equiv> fr.c \<circ>\<^sub>\<rightarrow> linv\<close>

  interpret u: bijective_morphism D D' u
  using bij_comp_bij_is_bij[OF linv k_bij.bijective_morphism_axioms]
  by (simp add: u_def)

    obtain uinv where uinv:\<open>bijective_morphism D' D uinv\<close>
      and \<open>\<And>v. v\<in>V\<^bsub>D\<^esub> \<Longrightarrow> \<^bsub>uinv \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = v\<close> \<open>\<And>e. e\<in>E\<^bsub>D\<^esub> \<Longrightarrow> \<^bsub>uinv \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = e\<close>
      \<open>\<And>v. v\<in>V\<^bsub>D'\<^esub> \<Longrightarrow> \<^bsub>u \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>V v = v\<close> \<open>\<And>e. e\<in>E\<^bsub>D'\<^esub> \<Longrightarrow> \<^bsub>u \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>E e = e\<close>
      using u.ex_inv 
      by metis

    interpret uinv: bijective_morphism D' D uinv
      using uinv by assumption


(* here starts bijection of H *)
(* triangle (1) *)
    have aa: \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v = \<^bsub>d'\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^esub>\<close> for v
    proof -
      have \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v = \<^bsub>fr.c \<circ>\<^sub>\<rightarrow> linv \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v\<close>
        by (simp add: u_def)
      also have \<open>\<dots> = \<^bsub>fr.c \<circ>\<^sub>\<rightarrow> linv \<circ>\<^sub>\<rightarrow> fr.b  \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close>
        by (simp add: morph_comp_def fr.b_def h_def)
      also have \<open>\<dots> = \<^bsub>fr.c  \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>V v\<close>
        using  \<open>\<And>v. v\<in> V\<^bsub>fr.A\<^esub>\<Longrightarrow> \<^bsub>linv \<circ>\<^sub>\<rightarrow> fr.b \<^esub>\<^sub>V v = v \<close> h.morph_node_range that
        by (simp add: morph_comp_def  h_def)
      also have \<open>\<dots> = \<^bsub>d'\<^esub>\<^sub>V v\<close>
        using "*"[symmetric] morph_comp_id(1)
        by simp
      finally show ?thesis .
    qed

    have bb:\<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>E e = \<^bsub>d'\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
    proof -
      have \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>E e = \<^bsub>fr.c \<circ>\<^sub>\<rightarrow> linv \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>E e\<close>
        by (simp add: u_def)
      also have \<open>\<dots> = \<^bsub>fr.c \<circ>\<^sub>\<rightarrow> linv \<circ>\<^sub>\<rightarrow> fr.b  \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e\<close>
        by (simp add: morph_comp_def fr.c_def fr.b_def h_def)
      also have \<open>\<dots> = \<^bsub>fr.c  \<circ>\<^sub>\<rightarrow> h\<^esub>\<^sub>E e\<close>
        using  \<open>\<And>e. e \<in> E\<^bsub>fr.A\<^esub>\<Longrightarrow> \<^bsub>linv \<circ>\<^sub>\<rightarrow> fr.b \<^esub>\<^sub>E e = e \<close> h.morph_edge_range that
        by (simp add: morph_comp_def  h_def)
      also have \<open>\<dots> = \<^bsub>d'\<^esub>\<^sub>E e\<close>
        using "*"[symmetric] morph_comp_id(1)
        by simp
      finally show ?thesis .
    qed

(* triangle (2) *)

    have cc:\<open>\<^bsub>uinv \<circ>\<^sub>\<rightarrow> d'\<^esub>\<^sub>V v = \<^bsub>d\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^esub>\<close> for v
    proof -
      have \<open>\<^bsub>uinv \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v = \<^bsub>uinv \<circ>\<^sub>\<rightarrow> d'\<^esub>\<^sub>V v\<close>
        using aa that
        by (simp add: morph_comp_def)
      then have \<open>\<^bsub>d\<^esub>\<^sub>V v = \<^bsub>uinv \<circ>\<^sub>\<rightarrow> d'\<^esub>\<^sub>V v\<close>
       using that \<open>\<And>v. v\<in>V\<^bsub>D\<^esub> \<Longrightarrow> \<^bsub>uinv \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = v\<close> po1.c.morph_node_range
       by (simp add: morph_comp_def)

     thus ?thesis
       by simp
   qed

    have dd:\<open>\<^bsub>uinv \<circ>\<^sub>\<rightarrow> d'\<^esub>\<^sub>E e = \<^bsub>d\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^esub>\<close> for e
    proof -
      have \<open>\<^bsub>uinv \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>E e = \<^bsub>uinv \<circ>\<^sub>\<rightarrow> d'\<^esub>\<^sub>E e\<close>
        using bb that
        by (simp add: morph_comp_def)
      then have \<open>\<^bsub>d\<^esub>\<^sub>E e = \<^bsub>uinv \<circ>\<^sub>\<rightarrow> d'\<^esub>\<^sub>E e\<close>
       using that \<open>\<And>e. e\<in>E\<^bsub>D\<^esub> \<Longrightarrow> \<^bsub>uinv \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = e\<close> po1.c.morph_edge_range
       by (simp add: morph_comp_def)

     thus ?thesis
       by simp
    qed


(* u' *)
    thm  po2.pushout_diagram_axioms
    interpret m'u: morphism D H' "m' \<circ>\<^sub>\<rightarrow> u"
      using wf_morph_comp[OF u.morphism_axioms dd2.po2.g.morphism_axioms] 
      by assumption

    have "**a": \<open>\<forall>v\<in>V\<^bsub>interf r\<^esub>. \<^bsub>f' \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>m' \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v\<close>
                \<open>\<forall>e\<in>E\<^bsub>interf r\<^esub>. \<^bsub>f' \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>m' \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>E e\<close>
      using aa bb dd2.po2.node_commutativity dd2.po2.edge_commutativity
      by (simp_all add: morph_comp_def)
      
    obtain u' where u': \<open>morphism H H' u'\<close>
      and \<open>\<And>v. v\<in>V\<^bsub>rhs r\<^esub> \<Longrightarrow> \<^bsub>u' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v\<close> \<open>\<And>e. e\<in>E\<^bsub>rhs r\<^esub> \<Longrightarrow> \<^bsub>u' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e\<close>
      and \<open>\<And>v. v\<in>V\<^bsub>D\<^esub> \<Longrightarrow> \<^bsub>u' \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v = \<^bsub>m' \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v\<close> \<open>\<And>e. e\<in>E\<^bsub>D\<^esub> \<Longrightarrow> \<^bsub>u' \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e = \<^bsub>m' \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e\<close>
        using po2.universal_property_exist_gen[OF dd2.po2.f.H.graph_axioms dd2.po2.f.morphism_axioms
            m'u.morphism_axioms "**a"]
        by fast
      interpret u': morphism H H' u'
        using u' by assumption

      interpret muinv: morphism D' H "c' \<circ>\<^sub>\<rightarrow> uinv"
        using wf_morph_comp[OF uinv.morphism_axioms po2.g.morphism_axioms] 
        by assumption


      have "**b": \<open>\<forall>v\<in>V\<^bsub>interf r\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>c' \<circ>\<^sub>\<rightarrow> uinv \<circ>\<^sub>\<rightarrow> d'\<^esub>\<^sub>V v\<close>
           \<open>\<forall>e\<in>E\<^bsub>interf r\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>c' \<circ>\<^sub>\<rightarrow> uinv \<circ>\<^sub>\<rightarrow> d'\<^esub>\<^sub>E e\<close>
        using cc dd po2.node_commutativity po2.edge_commutativity
        by (simp_all add: morph_comp_def)

      obtain u'' where u'': \<open>morphism H' H u''\<close>
        and \<open>\<And>v. v\<in>V\<^bsub>rhs r\<^esub> \<Longrightarrow> \<^bsub>u'' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close> \<open>\<And>e. e\<in>E\<^bsub>rhs r\<^esub> \<Longrightarrow> \<^bsub>u'' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close>
        and \<open>\<And>v. v\<in>V\<^bsub>D'\<^esub> \<Longrightarrow> \<^bsub>u'' \<circ>\<^sub>\<rightarrow> m'\<^esub>\<^sub>V v = \<^bsub>c' \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>V v\<close> \<open>\<And>e. e\<in>E\<^bsub>D'\<^esub> \<Longrightarrow> \<^bsub>u'' \<circ>\<^sub>\<rightarrow> m'\<^esub>\<^sub>E e = \<^bsub>c' \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>E e\<close>
        using dd2.po2.universal_property_exist_gen[OF po2.f.H.graph_axioms po2.f.morphism_axioms
              muinv.morphism_axioms "**b"]
        by fast
      interpret u'': morphism H' H u''
        using u'' by assumption


      have u'u'': \<open>(\<forall>v\<in>V\<^bsub>H'\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u''\<^esub>\<^sub>V v = v) \<and> (\<forall>e\<in>E\<^bsub>H'\<^esub>. \<^bsub>u' \<circ>\<^sub>\<rightarrow> u''\<^esub>\<^sub>E e = e)\<close>
      proof -
        have a'v: \<open>\<^bsub>f'\<^esub>\<^sub>V v = \<^bsub>u' \<circ>\<^sub>\<rightarrow> u'' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>rhs r\<^esub>\<close> for v
          using \<open>\<And>v. v\<in>V\<^bsub>rhs r\<^esub> \<Longrightarrow> \<^bsub>u'' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close> 
                \<open>\<And>v. v\<in>V\<^bsub>rhs r\<^esub> \<Longrightarrow> \<^bsub>u' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v\<close> that
          by (simp add: morph_comp_def)
        have a'e: \<open>\<^bsub>f'\<^esub>\<^sub>E e = \<^bsub>u' \<circ>\<^sub>\<rightarrow> u'' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>rhs r\<^esub>\<close> for e
          using \<open>\<And>e. e\<in>E\<^bsub>rhs r\<^esub> \<Longrightarrow> \<^bsub>u'' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close> \<open>\<And>e. e\<in>E\<^bsub>rhs r\<^esub> \<Longrightarrow> \<^bsub>u' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e\<close> that
          by (simp add: morph_comp_def)

        have b'v: \<open>\<^bsub>m'\<^esub>\<^sub>V v = \<^bsub>u' \<circ>\<^sub>\<rightarrow> u'' \<circ>\<^sub>\<rightarrow> m'\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>D'\<^esub>\<close> for v
        proof -
          have \<open>\<^bsub>u' \<circ>\<^sub>\<rightarrow> c' \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>V v = \<^bsub>m' \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>D'\<^esub>\<close>
            using \<open>\<And>v. v\<in>V\<^bsub>D\<^esub> \<Longrightarrow> \<^bsub>u' \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v = \<^bsub>m' \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v\<close>  that 
              \<open>\<And>v. v\<in>V\<^bsub>D'\<^esub> \<Longrightarrow> \<^bsub>u \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>V v = v\<close> uinv.morph_node_range
            by (simp add:  morph_comp_def)

          then have \<open>\<^bsub>u' \<circ>\<^sub>\<rightarrow> c' \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>V v = \<^bsub>m'\<^esub>\<^sub>V v\<close>
            using \<open>\<And>v. v\<in>V\<^bsub>D'\<^esub> \<Longrightarrow> \<^bsub>u \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>V v = v\<close> that
            by(simp add:  morph_comp_def)
          thus ?thesis
            using \<open>\<And>v. v \<in> V\<^bsub>D'\<^esub> \<Longrightarrow> \<^bsub>u'' \<circ>\<^sub>\<rightarrow> m'\<^esub>\<^sub>V v = \<^bsub>c' \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>V v\<close> that
            by (simp add: morph_comp_def)
        qed

        have b'e: \<open>\<^bsub>m'\<^esub>\<^sub>E e = \<^bsub>u' \<circ>\<^sub>\<rightarrow> u'' \<circ>\<^sub>\<rightarrow> m'\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>D'\<^esub>\<close> for e
        proof -
          have \<open>\<^bsub>u' \<circ>\<^sub>\<rightarrow> c' \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>E e = \<^bsub>m' \<circ>\<^sub>\<rightarrow> u \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>D'\<^esub>\<close>
            using \<open>\<And>e. e\<in>E\<^bsub>D\<^esub> \<Longrightarrow> \<^bsub>u' \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e = \<^bsub>m' \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e\<close>  that 
              \<open>\<And>e. e\<in>E\<^bsub>D'\<^esub> \<Longrightarrow> \<^bsub>u \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>E e = e\<close> uinv.morph_edge_range
            by (simp add:  morph_comp_def)

          then have \<open>\<^bsub>u' \<circ>\<^sub>\<rightarrow> c' \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>E e = \<^bsub>m'\<^esub>\<^sub>E e\<close>
            using \<open>\<And>e. e\<in>E\<^bsub>D'\<^esub> \<Longrightarrow> \<^bsub>u \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>E e = e\<close> that
            by(simp add:  morph_comp_def)
          thus ?thesis
            using \<open>\<And>e. e \<in> E\<^bsub>D'\<^esub> \<Longrightarrow> \<^bsub>u'' \<circ>\<^sub>\<rightarrow> m'\<^esub>\<^sub>E e = \<^bsub>c' \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>E e\<close> that
            by (simp add: morph_comp_def)
        qed
         
        have zz1: \<open>\<forall>v\<in>V\<^bsub>interf r\<^esub>. \<^bsub>f' \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>m' \<circ>\<^sub>\<rightarrow> d'\<^esub>\<^sub>V v\<close>
          by (simp add: dd2.po2.node_commutativity)
        have zz2: \<open>\<forall>e\<in>E\<^bsub>interf r\<^esub>. \<^bsub>f' \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>m' \<circ>\<^sub>\<rightarrow> d'\<^esub>\<^sub>E e\<close>
          by (simp add: dd2.po2.edge_commutativity)
        have zz3: \<open> morphism H' H' (u' \<circ>\<^sub>\<rightarrow> u'') \<and> (\<forall>v\<in>V\<^bsub>rhs r\<^esub>. \<^bsub>(u' \<circ>\<^sub>\<rightarrow> u'') \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>rhs r\<^esub>. \<^bsub>(u' \<circ>\<^sub>\<rightarrow> u'') \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e) 
\<and> (\<forall>v\<in>V\<^bsub>D'\<^esub>. \<^bsub>(u' \<circ>\<^sub>\<rightarrow> u'') \<circ>\<^sub>\<rightarrow> m'\<^esub>\<^sub>V v = \<^bsub>m'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>D'\<^esub>. \<^bsub>(u' \<circ>\<^sub>\<rightarrow> u'') \<circ>\<^sub>\<rightarrow> m'\<^esub>\<^sub>E e = \<^bsub>m'\<^esub>\<^sub>E e)\<close>
          using a'e a'v b'e b'v u' u'' wf_morph_comp by fastforce
        have zz4: \<open>morphism H' H' idM \<and> (\<forall>v\<in>V\<^bsub>rhs r\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>rhs r\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>D'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> m'\<^esub>\<^sub>V v = \<^bsub>m'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>D'\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> m'\<^esub>\<^sub>E e = \<^bsub>m'\<^esub>\<^sub>E e)\<close>
          using dd2.po2.f.H.idm.morphism_axioms by force

        show ?thesis
          using ex_eq[OF dd2.po2.universal_property_exist_gen[OF dd2.po2.f.H.graph_axioms dd2.po2.f.morphism_axioms
            dd2.po2.g.morphism_axioms zz1 zz2] zz3 zz4]
          by simp
      qed



      have u''u': \<open>(\<forall>v\<in>V\<^bsub>H\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>V v = v) \<and> (\<forall>e\<in>E\<^bsub>H\<^esub>. \<^bsub>u'' \<circ>\<^sub>\<rightarrow> u'\<^esub>\<^sub>E e = e)\<close>
      proof -
        have a'v: \<open>\<^bsub>f\<^esub>\<^sub>V v = \<^bsub>u'' \<circ>\<^sub>\<rightarrow> u' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>rhs r\<^esub>\<close> for v
          using \<open>\<And>v. v\<in>V\<^bsub>rhs r\<^esub> \<Longrightarrow> \<^bsub>u'' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v\<close> \<open>\<And>v. v\<in>V\<^bsub>rhs r\<^esub> \<Longrightarrow> \<^bsub>u' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f'\<^esub>\<^sub>V v\<close> that
          by (simp add: morph_comp_def)
        have a'e: \<open>\<^bsub>f\<^esub>\<^sub>E e = \<^bsub>u'' \<circ>\<^sub>\<rightarrow> u' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>rhs r\<^esub>\<close> for e
          using \<open>\<And>e. e\<in>E\<^bsub>rhs r\<^esub> \<Longrightarrow> \<^bsub>u'' \<circ>\<^sub>\<rightarrow> f'\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e\<close> \<open>\<And>e. e\<in>E\<^bsub>rhs r\<^esub> \<Longrightarrow> \<^bsub>u' \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f'\<^esub>\<^sub>E e\<close> that
          by (simp add: morph_comp_def)
        
        have b'v: \<open>\<^bsub>c'\<^esub>\<^sub>V v = \<^bsub>u'' \<circ>\<^sub>\<rightarrow> u' \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>D\<^esub>\<close> for v
        proof -
          have \<open>\<^bsub>u'' \<circ>\<^sub>\<rightarrow> m' \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>c' \<circ>\<^sub>\<rightarrow> uinv \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v\<close>
            using that \<open>\<And>v. v\<in>V\<^bsub>D'\<^esub> \<Longrightarrow> \<^bsub>u'' \<circ>\<^sub>\<rightarrow> m'\<^esub>\<^sub>V v = \<^bsub>c' \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>V v\<close> u.morph_node_range
            by (simp add: morph_comp_def)
          then have \<open>\<^bsub>u'' \<circ>\<^sub>\<rightarrow> m' \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v\<close>
            using that  \<open>\<And>v. v\<in>V\<^bsub>D\<^esub> \<Longrightarrow> \<^bsub>uinv \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v = v\<close>
            by (simp add: morph_comp_def)
          thus ?thesis
            using \<open>\<And>v. v\<in>V\<^bsub>D\<^esub> \<Longrightarrow> \<^bsub>u' \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v = \<^bsub>m' \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>V v\<close> that
            by (simp add: morph_comp_def)
        qed
        have b'e: \<open>\<^bsub>c'\<^esub>\<^sub>E e = \<^bsub>u'' \<circ>\<^sub>\<rightarrow> u' \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>D\<^esub>\<close> for e
        proof -
          have \<open>\<^bsub>u'' \<circ>\<^sub>\<rightarrow> m' \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>c' \<circ>\<^sub>\<rightarrow> uinv \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e\<close>
            using that \<open>\<And>e. e\<in>E\<^bsub>D'\<^esub> \<Longrightarrow> \<^bsub>u'' \<circ>\<^sub>\<rightarrow> m'\<^esub>\<^sub>E e = \<^bsub>c' \<circ>\<^sub>\<rightarrow> uinv\<^esub>\<^sub>E e\<close> u.morph_edge_range
            by (simp add: morph_comp_def)
          then have \<open>\<^bsub>u'' \<circ>\<^sub>\<rightarrow> m' \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e\<close>
            using that  \<open>\<And>e. e\<in>E\<^bsub>D\<^esub> \<Longrightarrow> \<^bsub>uinv \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e = e\<close>
            by (simp add: morph_comp_def)
          thus ?thesis
            using \<open>\<And>e. e\<in>E\<^bsub>D\<^esub> \<Longrightarrow> \<^bsub>u' \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e = \<^bsub>m' \<circ>\<^sub>\<rightarrow> u\<^esub>\<^sub>E e\<close> that
            by (simp add: morph_comp_def)
        qed

        have zz1: \<open>\<forall>v\<in>V\<^bsub>interf r\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>V v = \<^bsub>c' \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>V v\<close>
          using po2.node_commutativity
          by blast

        have zz2: \<open>\<forall>e\<in>E\<^bsub>interf r\<^esub>. \<^bsub>f \<circ>\<^sub>\<rightarrow> b'\<^esub>\<^sub>E e = \<^bsub>c' \<circ>\<^sub>\<rightarrow> d\<^esub>\<^sub>E e\<close>
          using po2.edge_commutativity
          by blast

        have zz3: \<open>morphism H H (u'' \<circ>\<^sub>\<rightarrow> u') \<and> (\<forall>v\<in>V\<^bsub>rhs r\<^esub>. \<^bsub>(u'' \<circ>\<^sub>\<rightarrow> u') \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>rhs r\<^esub>. \<^bsub>(u'' \<circ>\<^sub>\<rightarrow> u') \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>(u'' \<circ>\<^sub>\<rightarrow> u') \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>(u'' \<circ>\<^sub>\<rightarrow> u') \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e)\<close>
          using a'e a'v b'e b'v u' u'' wf_morph_comp by force

        have zz4: \<open>morphism H H idM \<and> (\<forall>v\<in>V\<^bsub>rhs r\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>V v = \<^bsub>f\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>rhs r\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> f\<^esub>\<^sub>E e = \<^bsub>f\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>D\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>V v = \<^bsub>c'\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>D\<^esub>. \<^bsub>idM \<circ>\<^sub>\<rightarrow> c'\<^esub>\<^sub>E e = \<^bsub>c'\<^esub>\<^sub>E e)\<close>
          using po2.f.H.idm.morphism_axioms by force

        show ?thesis
          using ex_eq[OF po2.universal_property_exist_gen[OF po2.f.H.graph_axioms po2.f.morphism_axioms
            po2.g.morphism_axioms zz1 zz2] zz3 zz4]
          by simp
     qed


      interpret bij_u': bijective_morphism H H' u'
        using comp_id_bij[OF u' u''] u''u' u'u''
        by blast
      
      show ?thesis
        using bij_u'.bijective_morphism_axioms u.bijective_morphism_axioms
        by blast
qed
end

corollary (in pushout_diagram) uniqueness_pc:
  assumes po2: \<open>pushout_diagram A B C' D b c' f g'\<close>
  and       b': \<open>injective_morphism A B b\<close>
  and       f': \<open>injective_morphism B D f\<close>
shows \<open>\<exists>u. bijective_morphism C C' u\<close>
proof -
  interpret po2: pushout_diagram A B C' D b c' f g'
    using po2 by assumption
  interpret b': injective_morphism A B b
    using b' by assumption

  interpret f': injective_morphism B D f
    using f' by assumption

  define r where \<open>r \<equiv> \<lparr>lhs = B, interf = A, rhs = A\<rparr>\<close>
  interpret b': injective_morphism "interf r" "lhs r" b
    by (simp add: r_def b')

  interpret A: graph A
    using c.morphism_axioms morphism.axioms(1) by blast
 
  interpret injective_morphism "interf r" "rhs r" idM
    by (standard)
       (simp_all add: r_def b.G.graph_axioms b.G.idm.injective_morphism_axioms 
                      b.G.finite_nodes b.G.finite_edges 
                      b.G.source_integrity b.G.target_integrity)
    
  interpret rule r b idM ..

  interpret injective_morphism "lhs r" D f
    by(simp add: r_def f')
  interpret morphism "interf r" C c
    by (simp add: r_def c.morphism_axioms)
  interpret pushout_diagram "interf r" "lhs r" C D b c f g
    by (simp add: r_def pushout_diagram_axioms)
  interpret morphism "rhs r" C c
    by (simp add: r_def c.morphism_axioms)

  
  interpret dd1: direct_derivation r b idM D f C c g C c idM 
    by standard (auto simp add: morph_comp_def to_ngraph_def to_nmorph_def r_def)

  interpret morphism "interf r" C' c'
    by (simp add: r_def po2.c.morphism_axioms)
  interpret pushout_diagram "interf r" "lhs r" C' D b c' f g'
    by (simp add: r_def po2.pushout_diagram_axioms)
  interpret morphism "rhs r" C' c'
    by (simp add: r_def po2.c.morphism_axioms)
    
  interpret dd2: direct_derivation r b idM D f C' c' g' C' c' idM 
    by standard (auto simp add: morph_comp_def to_ngraph_def to_nmorph_def r_def)

  show ?thesis
    using dd1.uniqueness_direct_derivation[OF dd2.direct_derivation_axioms]
    by simp
qed

locale direct_derivation_construction =
  r: rule r b b' +
  d: deletion "interf r" G "lhs r" g b +
  g: gluing "interf r" d.D "rhs r" d.d b' for G r b b' g H +
assumes a: \<open>H = g.H\<close>
begin

corollary
    \<open>pushout_diagram (interf r) (lhs r) d.D G b d.d g d.c'\<close> and \<open>pushout_diagram (interf r) (rhs r) d.D g.H b' d.d g.h g.c\<close> 
  using 
    d.po.pushout_diagram_axioms
    g.po.pushout_diagram_axioms
  by simp_all


sublocale direct_derivation:
  direct_derivation r b b' G g d.D d.d d.c' g.H g.h g.c ..
  
end

end