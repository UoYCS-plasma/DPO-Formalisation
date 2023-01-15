theory LocalChurchRosser
  imports DirectDerivation
begin
(* Fund. Alg. GT, PDF. P. 117
https://link.springer.com/content/pdf/10.1007/3-540-31188-2.pdf?pdf=button
 *)
(* declare [[show_sorts]]
 *)
(* declare [[unify_trace_failure]] 
 *)
locale parallel_independence =
  p\<^sub>1: direct_derivation r\<^sub>1 G g\<^sub>1 D\<^sub>1 m\<^sub>1 c\<^sub>1 H\<^sub>1 f\<^sub>1 h\<^sub>1 +
  p\<^sub>2: direct_derivation r\<^sub>2 G g\<^sub>2 D\<^sub>2 m\<^sub>2 c\<^sub>2 H\<^sub>2 f\<^sub>2 h\<^sub>2
  for r\<^sub>1 G g\<^sub>1 D\<^sub>1 m\<^sub>1 c\<^sub>1 H\<^sub>1 f\<^sub>1 h\<^sub>1 r\<^sub>2 g\<^sub>2 D\<^sub>2 m\<^sub>2 c\<^sub>2 H\<^sub>2 f\<^sub>2 h\<^sub>2 +
  assumes
    i: \<open>\<exists>i. morphism (lhs r\<^sub>1) D\<^sub>2 i \<and> (\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v) \<and> (\<forall>e \<in> E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>E e = \<^bsub>g\<^sub>1\<^esub>\<^sub>E e)\<close> and
    j: \<open>\<exists>j. morphism (lhs r\<^sub>2) D\<^sub>1 j \<and> (\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> j\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v) \<and> (\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> j\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e)\<close>


locale sequential_independence =
  p\<^sub>1: direct_derivation r\<^sub>1 G g\<^sub>1 D\<^sub>1 m\<^sub>1 c\<^sub>1 H\<^sub>1 f\<^sub>1 h\<^sub>1 +
  p\<^sub>2: direct_derivation r\<^sub>2 H\<^sub>1 g\<^sub>2 D\<^sub>2 m\<^sub>2 c\<^sub>2 H\<^sub>2 f\<^sub>2 h\<^sub>2
  for r\<^sub>1 G g\<^sub>1 D\<^sub>1 m\<^sub>1 c\<^sub>1 H\<^sub>1 f\<^sub>1 h\<^sub>1 r\<^sub>2 g\<^sub>2 D\<^sub>2 m\<^sub>2 c\<^sub>2 H\<^sub>2 f\<^sub>2 h\<^sub>2 +
  assumes
    i: \<open>\<exists>i. morphism (rhs r\<^sub>1) D\<^sub>2 i \<and> (\<forall>v \<in> V\<^bsub>rhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v) \<and> (\<forall>e \<in> E\<^bsub>rhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e)\<close> and
    j: \<open>\<exists>j. morphism (lhs r\<^sub>2) D\<^sub>1 j \<and> (\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> j\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v) \<and> (\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> j\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e)\<close> 




theorem (in parallel_independence) church_rosser_1:
  shows \<open>\<exists>g' D' m' c' H f' h' g'' D'' m'' c'' H f'' h''. 
                  sequential_independence r\<^sub>1 G g\<^sub>1 D\<^sub>1 m\<^sub>1 c\<^sub>1 H\<^sub>1 f\<^sub>1 h\<^sub>1 r\<^sub>2 (g':: ('k, 'i, 'l, 'j) pre_morph) (D'::('g \<times> 'm + 'a, 'h \<times> 'n + 'b, 'c, 'd) pre_graph) (m'::('k, 'g \<times> 'm + 'a, 'l, 'h \<times> 'n + 'b) pre_morph) (c'::('g \<times> 'm + 'a, 'i, 'h \<times> 'n + 'b, 'j) pre_morph) (H::(('g \<times> 'm + 'k) + 'g \<times> 'm + 'a, ('h \<times> 'n + 'l) + 'h \<times> 'n + 'b, 'c, 'd) pre_graph) (f'::('k, ('g \<times> 'm + 'k) + 'g \<times> 'm + 'a, 'l, ('h \<times> 'n + 'l) + 'h \<times> 'n + 'b) pre_morph) (h'::('g \<times> 'm + 'a, ('g \<times> 'm + 'k) + 'g \<times> 'm + 'a, 'h \<times> 'n + 'b, ('h \<times> 'n + 'l) + 'h \<times> 'n + 'b) pre_morph)
                \<and> sequential_independence r\<^sub>2 G g\<^sub>2 D\<^sub>2 m\<^sub>2 c\<^sub>2 H\<^sub>2 f\<^sub>2 h\<^sub>2 r\<^sub>1 (g''::('a, 'o, 'b, 'p) pre_morph) (D''::('g \<times> 'm + 'k, 'h \<times> 'n + 'l, 'c, 'd) pre_graph) (m''::('a, 'g \<times> 'm + 'k, 'b, 'h \<times> 'n + 'l) pre_morph) (c''::('g \<times> 'm + 'k, 'o, 'h \<times> 'n + 'l, 'p) pre_morph) (H::(('g \<times> 'm + 'k) + 'g \<times> 'm + 'a, ('h \<times> 'n + 'l) + 'h \<times> 'n + 'b, 'c, 'd) pre_graph) (f''::('a, ('g \<times> 'm + 'k) + 'g \<times> 'm + 'a, 'b, ('h \<times> 'n + 'l) + 'h \<times> 'n + 'b) pre_morph) (h''::('g \<times> 'm + 'k, ('g \<times> 'm + 'k) + 'g \<times> 'm + 'a, 'h \<times> 'n + 'l, ('h \<times> 'n + 'l) + 'h \<times> 'n + 'b) pre_morph)\<close>
proof -

  interpret c\<^sub>1: injective_morphism D\<^sub>1 G c\<^sub>1
    using p\<^sub>1.po1.b_inj_imp_g_inj p\<^sub>1.r.k.injective_morphism_axioms by blast
  interpret c\<^sub>2: injective_morphism D\<^sub>2 G c\<^sub>2
    using p\<^sub>2.po1.b_inj_imp_g_inj p\<^sub>2.r.k.injective_morphism_axioms by blast

  interpret h\<^sub>1: injective_morphism D\<^sub>1 H\<^sub>1 h\<^sub>1
    using p\<^sub>1.po2.b_inj_imp_g_inj p\<^sub>1.r.r.injective_morphism_axioms by blast
  interpret h\<^sub>2: injective_morphism D\<^sub>2 H\<^sub>2 h\<^sub>2
    using p\<^sub>2.po2.b_inj_imp_g_inj p\<^sub>2.r.r.injective_morphism_axioms by blast

  obtain i\<^sub>1 i\<^sub>2 where \<open>morphism (lhs r\<^sub>1) D\<^sub>2 i\<^sub>1\<close>  
                      \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close> \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>E e = \<^bsub>g\<^sub>1\<^esub>\<^sub>E e\<close> and
                     \<open>morphism (lhs r\<^sub>2) D\<^sub>1 i\<^sub>2\<close>  
                      \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close> \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e\<close>
    using i j by auto

  interpret i\<^sub>1: morphism "lhs r\<^sub>1" D\<^sub>2 i\<^sub>1
    using \<open>morphism (lhs r\<^sub>1) D\<^sub>2 i\<^sub>1\<close>  by assumption
  interpret i\<^sub>2: morphism "lhs r\<^sub>2" D\<^sub>1 i\<^sub>2
    using \<open>morphism (lhs r\<^sub>2) D\<^sub>1 i\<^sub>2\<close>
  by assumption

  interpret i\<^sub>1: injective_morphism "lhs r\<^sub>1" D\<^sub>2 i\<^sub>1
    sorry
  interpret i\<^sub>2: injective_morphism "lhs r\<^sub>2" D\<^sub>1 i\<^sub>2
    sorry

(*   proof
    show \<open>inj_on \<^bsub>i\<^sub>1\<^esub>\<^sub>V V\<^bsub>lhs r\<^sub>1\<^esub>\<close>
      using \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close>  p\<^sub>1.g.inj_nodes
      by (auto simp add: morph_comp_def inj_on_def) metis
      try0
      sledgehammer
      by (metis inv_into_f_f p\<^sub>1.g.inj_nodes) *)

  interpret pb: pullback_construction D\<^sub>1 G D\<^sub>2 c\<^sub>1 c\<^sub>2 ..

  define j\<^sub>1 where \<open>j\<^sub>1 \<equiv> \<lparr>node_map = \<lambda>v. (inv_into V\<^bsub>D\<^sub>1\<^esub> \<^bsub>c\<^sub>1\<^esub>\<^sub>V (\<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v),\<^bsub>i\<^sub>1 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v)
                        ,edge_map = \<lambda>e. (inv_into E\<^bsub>D\<^sub>1\<^esub> \<^bsub>c\<^sub>1\<^esub>\<^sub>E (\<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e), \<^bsub>i\<^sub>1 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e)\<rparr>\<close>
  interpret j1: morphism "interf r\<^sub>1" pb.A j\<^sub>1
  proof
    show \<open>\<^bsub>j\<^sub>1\<^esub>\<^sub>E e \<in> E\<^bsub>pb.A\<^esub>\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>1\<^esub>\<close> for e
      using that \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>E e = \<^bsub>g\<^sub>1\<^esub>\<^sub>E e\<close> 
            i\<^sub>1.morph_edge_range c\<^sub>1.inj_edges inv_into_f_f p\<^sub>1.g.morph_edge_range
      apply (auto simp add: pb.A_def j\<^sub>1_def morph_comp_def)
      sledgehammer
      by (simp add: pb.A_def j\<^sub>1_def morph_comp_def) fastforce
  next
    show \<open>\<^bsub>j\<^sub>1\<^esub>\<^sub>V v \<in> V\<^bsub>pb.A\<^esub>\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>1\<^esub>\<close> for v
      using that \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close> 
            i\<^sub>1.morph_node_range c\<^sub>1.inj_nodes c\<^sub>1.surj_nodes inv_into_f_f p\<^sub>1.g.morph_node_range
      by (simp add: pb.A_def j\<^sub>1_def morph_comp_def) fastforce
  next
    show \<open>\<^bsub>j\<^sub>1\<^esub>\<^sub>V (s\<^bsub>interf r\<^sub>1\<^esub> e) = s\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>1\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>1\<^esub>\<close> for e
    proof 
      show \<open>fst (\<^bsub>j\<^sub>1\<^esub>\<^sub>V (s\<^bsub>interf r\<^sub>1\<^esub> e)) = fst (s\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>1\<^esub>\<^sub>E e))\<close>
        using bij_betw_inv_into_left[OF c\<^sub>1.bij_edges] bij_betw_inv_into_left[OF c\<^sub>1.bij_nodes] 
          c\<^sub>1.surj_edges i\<^sub>1.morph_edge_range i\<^sub>1.source_preserve p\<^sub>1.po1.c.H.source_integrity
          p\<^sub>1.po1.g.source_preserve p\<^sub>1.r.k.G.idm.id_edges p\<^sub>1.r.k.G.idm.source_preserve 
          p\<^sub>1.r.k.edges_g_in_h p\<^sub>1.r.k.source_preserve p\<^sub>2.po1.g.morph_edge_range 
          p\<^sub>2.po1.g.source_preserve that
        by (simp add: j\<^sub>1_def pb.A_def morph_comp_def) force
      next
        show \<open>snd (\<^bsub>j\<^sub>1\<^esub>\<^sub>V (s\<^bsub>interf r\<^sub>1\<^esub> e)) = snd (s\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>1\<^esub>\<^sub>E e))\<close>
          using that  i\<^sub>1.source_preserve p\<^sub>1.r.k.source_preserve
          by (simp add: j\<^sub>1_def pb.A_def morph_comp_def) 
    qed
  next
    show \<open>\<^bsub>j\<^sub>1\<^esub>\<^sub>V (t\<^bsub>interf r\<^sub>1\<^esub> e) = t\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>1\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>1\<^esub>\<close> for e
    proof 
      show \<open>fst (\<^bsub>j\<^sub>1\<^esub>\<^sub>V (t\<^bsub>interf r\<^sub>1\<^esub> e)) = fst (t\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>1\<^esub>\<^sub>E e))\<close>
        using bij_betw_inv_into_left[OF c\<^sub>1.bij_edges] bij_betw_inv_into_left[OF c\<^sub>1.bij_nodes] 
          c\<^sub>1.surj_edges i\<^sub>1.morph_edge_range i\<^sub>1.target_preserve p\<^sub>1.po1.c.H.target_integrity
          p\<^sub>1.po1.g.target_preserve p\<^sub>1.r.k.G.idm.id_edges p\<^sub>1.r.k.G.idm.target_preserve 
          p\<^sub>1.r.k.edges_g_in_h p\<^sub>1.r.k.target_preserve p\<^sub>2.po1.g.morph_edge_range 
          p\<^sub>2.po1.g.target_preserve that
        by (simp add: j\<^sub>1_def pb.A_def morph_comp_def) force
      next
        show \<open>snd (\<^bsub>j\<^sub>1\<^esub>\<^sub>V (t\<^bsub>interf r\<^sub>1\<^esub> e)) = snd (t\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>1\<^esub>\<^sub>E e))\<close>
          using that i\<^sub>1.target_preserve p\<^sub>1.r.k.target_preserve
          by (simp add: j\<^sub>1_def pb.A_def morph_comp_def)
      qed
    next
      show \<open>l\<^bsub>interf r\<^sub>1\<^esub> v = l\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>1\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>1\<^esub>\<close> for v
        using that i\<^sub>1.label_preserve p\<^sub>1.r.k.label_preserve  i\<^sub>1.morph_node_range
          c\<^sub>1.surj_nodes inv_into_f_f[OF c\<^sub>1.inj_nodes] p\<^sub>1.po1.g.label_preserve p\<^sub>2.po1.g.label_preserve p\<^sub>2.po1.g.morph_node_range
        by (simp add: j\<^sub>1_def pb.A_def morph_comp_def) fastforce
    next
      show \<open>m\<^bsub>interf r\<^sub>1\<^esub> e = m\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>1\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>1\<^esub>\<close> for e
        using that i\<^sub>1.mark_preserve p\<^sub>1.r.k.mark_preserve  i\<^sub>1.morph_edge_range
          c\<^sub>1.surj_edges inv_into_f_f[OF c\<^sub>1.inj_edges] p\<^sub>1.po1.g.mark_preserve p\<^sub>2.po1.g.mark_preserve p\<^sub>2.po1.g.morph_edge_range
        by (simp add: j\<^sub>1_def pb.A_def morph_comp_def) fastforce
    qed


  define j\<^sub>2 where \<open>j\<^sub>2 \<equiv> \<lparr>node_map = \<lambda>v. (\<^bsub>i\<^sub>2 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v, inv_into V\<^bsub>D\<^sub>2\<^esub> \<^bsub>c\<^sub>2\<^esub>\<^sub>V (\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v))
                        ,edge_map = \<lambda>e. (\<^bsub>i\<^sub>2 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e, inv_into E\<^bsub>D\<^sub>2\<^esub> \<^bsub>c\<^sub>2\<^esub>\<^sub>E (\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e))\<rparr>\<close>

  interpret j2: morphism "interf r\<^sub>2" pb.A j\<^sub>2
  proof
    show \<open>\<^bsub>j\<^sub>2\<^esub>\<^sub>E e \<in> E\<^bsub>pb.A\<^esub>\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>2\<^esub>\<close> for e
      using that \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e\<close>
            i\<^sub>2.morph_edge_range c\<^sub>2.inj_edges c\<^sub>2.surj_edges inv_into_f_f p\<^sub>2.g.morph_edge_range
      by (simp add: pb.A_def j\<^sub>2_def morph_comp_def) fastforce
  next
    show \<open>\<^bsub>j\<^sub>2\<^esub>\<^sub>V v \<in> V\<^bsub>pb.A\<^esub>\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>2\<^esub>\<close> for v
      using that \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close>
            i\<^sub>2.morph_node_range c\<^sub>2.inj_nodes c\<^sub>2.surj_nodes inv_into_f_f p\<^sub>2.g.morph_node_range
      by (simp add: pb.A_def j\<^sub>2_def morph_comp_def) fastforce
  next
    show \<open>\<^bsub>j\<^sub>2\<^esub>\<^sub>V (s\<^bsub>interf r\<^sub>2\<^esub> e) = s\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>2\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>2\<^esub>\<close> for e
    proof 
      show \<open>fst (\<^bsub>j\<^sub>2\<^esub>\<^sub>V (s\<^bsub>interf r\<^sub>2\<^esub> e)) = fst (s\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>2\<^esub>\<^sub>E e))\<close>
        using i\<^sub>2.morphism_axioms morphism.source_preserve p\<^sub>2.r.k.source_preserve that
        by (auto simp add: j\<^sub>2_def pb.A_def morph_comp_def)
    next
      show \<open>snd (\<^bsub>j\<^sub>2\<^esub>\<^sub>V (s\<^bsub>interf r\<^sub>2\<^esub> e)) = snd (s\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>2\<^esub>\<^sub>E e))\<close>
        using bij_betw_inv_into_left[OF c\<^sub>2.bij_edges] bij_betw_inv_into_left[OF c\<^sub>2.bij_nodes] 
          i\<^sub>2.morph_edge_range i\<^sub>2.source_preserve inclusion_morphism.edges_g_in_h 
          p\<^sub>1.po1.g.morph_edge_range p\<^sub>1.po1.g.source_preserve p\<^sub>2.po1.c.H.source_integrity 
          p\<^sub>2.po1.g.source_preserve p\<^sub>2.r.k.G.idm.id_edges p\<^sub>2.r.k.G.idm.source_preserve 
          p\<^sub>2.r.k.inclusion_morphism_axioms p\<^sub>2.r.k.source_preserve that  c\<^sub>2.surj_edges
        by (auto simp add: j\<^sub>2_def pb.A_def morph_comp_def) force
    qed
  next
    show \<open>\<^bsub>j\<^sub>2\<^esub>\<^sub>V (t\<^bsub>interf r\<^sub>2\<^esub> e) = t\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>2\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>2\<^esub>\<close> for e
    proof 
      show \<open>fst (\<^bsub>j\<^sub>2\<^esub>\<^sub>V (t\<^bsub>interf r\<^sub>2\<^esub> e)) = fst (t\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>2\<^esub>\<^sub>E e))\<close>
        using i\<^sub>2.morphism_axioms morphism.target_preserve p\<^sub>2.r.k.target_preserve that
        by (auto simp add: j\<^sub>2_def pb.A_def morph_comp_def)
    next
      show \<open>snd (\<^bsub>j\<^sub>2\<^esub>\<^sub>V (t\<^bsub>interf r\<^sub>2\<^esub> e)) = snd (t\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>2\<^esub>\<^sub>E e))\<close>
        using bij_betw_inv_into_left[OF c\<^sub>2.bij_edges] bij_betw_inv_into_left[OF c\<^sub>2.bij_nodes] 
          i\<^sub>2.morph_edge_range i\<^sub>2.target_preserve inclusion_morphism.edges_g_in_h 
          p\<^sub>1.po1.g.morph_edge_range p\<^sub>1.po1.g.target_preserve p\<^sub>2.po1.c.H.target_integrity 
          p\<^sub>2.po1.g.target_preserve p\<^sub>2.r.k.G.idm.id_edges p\<^sub>2.r.k.G.idm.target_preserve 
          p\<^sub>2.r.k.inclusion_morphism_axioms p\<^sub>2.r.k.target_preserve that  c\<^sub>2.surj_edges
        by (auto simp add: j\<^sub>2_def pb.A_def morph_comp_def) force
    qed
    next
      show \<open>l\<^bsub>interf r\<^sub>2\<^esub> v = l\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>2\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>2\<^esub>\<close> for v
        using i\<^sub>2.label_preserve p\<^sub>2.r.k.label_preserve that
        by (simp add: j\<^sub>2_def pb.A_def morph_comp_def) 
    next
      show \<open>m\<^bsub>interf r\<^sub>2\<^esub> e = m\<^bsub>pb.A\<^esub> (\<^bsub>j\<^sub>2\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>2\<^esub>\<close> for e
        using i\<^sub>2.mark_preserve p\<^sub>2.r.k.mark_preserve that
        by (simp add: j\<^sub>2_def pb.A_def morph_comp_def) 
    qed


  have a: \<open>\<^bsub>pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v = \<^bsub>m\<^sub>1\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>1\<^esub>\<close> for v
    using that \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close> p\<^sub>1.po1.node_commutativity
    by (auto simp add: pb.b_def j\<^sub>1_def morph_comp_def c\<^sub>1.inj_nodes p\<^sub>1.po1.c.morph_node_range)

  have b: \<open>\<^bsub>pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e = \<^bsub>m\<^sub>1\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>1\<^esub>\<close> for e
    using that \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>E e = \<^bsub>g\<^sub>1\<^esub>\<^sub>E e\<close> p\<^sub>1.po1.edge_commutativity
    by (auto simp add: pb.b_def j\<^sub>1_def morph_comp_def c\<^sub>1.inj_edges p\<^sub>1.po1.c.morph_edge_range)

  have c: \<open>\<^bsub>pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>V v = \<^bsub>m\<^sub>2\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>2\<^esub>\<close> for v
    using that \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close> p\<^sub>2.po1.node_commutativity
    by (auto simp add: pb.c_def j\<^sub>2_def morph_comp_def c\<^sub>2.inj_nodes p\<^sub>2.po1.c.morph_node_range)

  have d: \<open>\<^bsub>pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>E e = \<^bsub>m\<^sub>2\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>2\<^esub>\<close> for e
    using that \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e\<close> p\<^sub>2.po1.edge_commutativity
    by (auto simp add: pb.c_def j\<^sub>2_def morph_comp_def c\<^sub>2.inj_edges p\<^sub>2.po1.c.morph_edge_range)



  interpret morphism "interf r\<^sub>1" D\<^sub>1 "pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1"
    using wf_morph_comp[OF j1.morphism_axioms pb.b.morphism_axioms]
    by assumption

(* TODO: prob. wrong 6+5 *)
  interpret "6+5": pushout_diagram "interf r\<^sub>1" "lhs r\<^sub>1" D\<^sub>1 G "idM :: ('a, 'a, 'b, 'b) pre_morph" "pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1" g\<^sub>1 c\<^sub>1
  proof 
    show \<open>\<^bsub>g\<^sub>1 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v = \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>1\<^esub>\<close> for v
    proof -
      have \<open>\<^bsub>g\<^sub>1 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v = \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> m\<^sub>1\<^esub>\<^sub>V v\<close>
        using p\<^sub>1.po1.node_commutativity[OF that] by assumption
      also have \<open>\<dots> = \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v\<close>
        using that a
        by(simp add: morph_comp_def)
      also have \<open>\<dots> = \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>V v\<close>
        by (simp add: morph_comp_def)
      finally show ?thesis .
    qed
  next
    show \<open>\<^bsub>g\<^sub>1 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e = \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>1\<^esub>\<close> for e
    proof -
      have \<open>\<^bsub>g\<^sub>1 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e = \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> m\<^sub>1\<^esub>\<^sub>E e\<close>
        using p\<^sub>1.po1.edge_commutativity[OF that] by assumption
      also have \<open>\<dots> = \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e\<close>
        using that b
        by(simp add: morph_comp_def)
      also have \<open>\<dots> = \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>E e\<close>
        by (simp add: morph_comp_def)
      finally show ?thesis .
    qed
  next
    show \<open>Ex1M
        (\<lambda>xa. morphism (to_ngraph G) D' xa \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e))
        (to_ngraph G)\<close>
      if \<open>graph D'\<close>
         \<open>morphism (to_ngraph (lhs r\<^sub>1)) D' x\<close>
         \<open>morphism (to_ngraph D\<^sub>1) D' y\<close>
         \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>V v\<close>
         \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>E e\<close>
       for D' :: "('c,'d) ngraph" and x y
    proof -

      have aa: \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>1\<^esub>\<^sub>V v\<close>
      proof 
        fix v
        assume asm: \<open>v \<in> V\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>\<close>

        have a_lifted: \<open>\<^bsub>to_nmorph pb.b \<circ>\<^sub>\<rightarrow> to_nmorph j\<^sub>1\<^esub>\<^sub>V v = \<^bsub>to_nmorph m\<^sub>1\<^esub>\<^sub>V v\<close>
          using a comp_lift_node1 asm
          by blast
       
        have \<open>\<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>V v\<close>
          using \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>V v\<close>
            asm
          by simp

        thus \<open>\<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>V  v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>1\<^esub>\<^sub>V v\<close>
          using a_lifted
          by (auto simp add: morph_comp_def to_nmorph_def)
      qed

      have bb: \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>1\<^esub>\<^sub>E e\<close>
      proof
        fix e
        assume asm: \<open>e \<in> E\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>\<close>

        have b_lifted: \<open>\<^bsub>to_nmorph pb.b \<circ>\<^sub>\<rightarrow> to_nmorph j\<^sub>1\<^esub>\<^sub>E e = \<^bsub>to_nmorph m\<^sub>1\<^esub>\<^sub>E e\<close>
          using b comp_lift_edge1 asm
          by blast
       
        have \<open>\<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>E e\<close>
          using \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>E e\<close>
            asm
          by simp

        thus \<open>\<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>1\<^esub>\<^sub>E e\<close>
          using b_lifted
          by (auto simp add: morph_comp_def to_nmorph_def)
      qed

      show ?thesis
        using  p\<^sub>1.po1.universal_property[OF \<open>graph D'\<close> \<open>morphism (to_ngraph (lhs r\<^sub>1)) D' x\<close> \<open>morphism (to_ngraph D\<^sub>1) D' y\<close> aa bb]
        by assumption
    qed
  qed

  interpret "6+5": pushout_diagram "interf r\<^sub>1" D\<^sub>1 "lhs r\<^sub>1" G "pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1" idM c\<^sub>1 "c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1"
    by (smt (verit) "6+5.pushout_diagram_axioms" "6+5.uniqueness_po" \<open>\<forall>e\<in>E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>E e = \<^bsub>g\<^sub>1\<^esub>\<^sub>E e\<close> \<open>\<forall>v\<in>V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close> i\<^sub>1.morphism_axioms p\<^sub>1.g.H.graph_axioms p\<^sub>1.g.morphism_axioms p\<^sub>1.po1.g.morphism_axioms p\<^sub>2.po1.g.morphism_axioms pushout_diagram.flip_diagram wf_morph_comp)

  interpret j1: injective_morphism "interf r\<^sub>1" pb.A j\<^sub>1
  proof
    show \<open>inj_on \<^bsub>j\<^sub>1\<^esub>\<^sub>V V\<^bsub>interf r\<^sub>1\<^esub>\<close>
      using  \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close>
      inv_into_f_f[OF p\<^sub>1.g.inj_nodes] p\<^sub>1.r.k.nodes_g_in_h p\<^sub>1.r.r.nodes_g_in_h
      by (auto simp add: j\<^sub>1_def morph_comp_def inj_on_def) metis
  next
    show \<open>inj_on \<^bsub>j\<^sub>1\<^esub>\<^sub>E E\<^bsub>interf r\<^sub>1\<^esub>\<close>
      using \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>E e = \<^bsub>g\<^sub>1\<^esub>\<^sub>E e\<close>
        inv_into_f_f[OF p\<^sub>1.g.inj_edges] p\<^sub>1.r.k.edges_g_in_h p\<^sub>1.r.r.edges_g_in_h
      by (auto simp add: j\<^sub>1_def morph_comp_def inj_on_def) metis
  qed

  interpret "5": pushout_diagram pb.A D\<^sub>1 D\<^sub>2 G pb.b pb.c c\<^sub>1 c\<^sub>2
    using pushout_pullback_decomposition[OF "6+5.pushout_diagram_axioms" pb.pb.pullback_diagram_axioms
        c\<^sub>2.injective_morphism_axioms j1.injective_morphism_axioms]
    by simp
    
  interpret six: pushout_diagram "interf r\<^sub>1" pb.A "lhs r\<^sub>1" D\<^sub>2 j\<^sub>1 idM pb.c i\<^sub>1
        using pushout_pullback_decomposition[OF "6+5.pushout_diagram_axioms" pb.pb.pullback_diagram_axioms
        c\<^sub>2.injective_morphism_axioms j1.injective_morphism_axioms]
    by simp

  interpret j\<^sub>2: injective_morphism "interf r\<^sub>2" pb.A j\<^sub>2
  proof
    show \<open>inj_on \<^bsub>j\<^sub>2\<^esub>\<^sub>V V\<^bsub>interf r\<^sub>2\<^esub>\<close>
      using  \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close>
        inv_into_f_f[OF p\<^sub>2.g.inj_nodes] p\<^sub>2.r.k.nodes_g_in_h p\<^sub>2.r.r.nodes_g_in_h
      by (auto simp add: j\<^sub>2_def morph_comp_def inj_on_def) metis
  next
    show \<open>inj_on \<^bsub>j\<^sub>2\<^esub>\<^sub>E E\<^bsub>interf r\<^sub>2\<^esub>\<close>
      using \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e\<close>
        inv_into_f_f[OF p\<^sub>2.g.inj_edges] p\<^sub>2.r.k.edges_g_in_h p\<^sub>2.r.r.edges_g_in_h
      by (auto simp add: j\<^sub>2_def morph_comp_def inj_on_def) metis
  qed

  interpret morphism "interf r\<^sub>2" D\<^sub>2 "pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2"
    using wf_morph_comp[OF j2.morphism_axioms pb.c.morphism_axioms]
    by assumption

  interpret morphism "lhs r\<^sub>2" G "c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2"
  proof
    show \<open>\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e \<in> E\<^bsub>G\<^esub>\<close> if \<open>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>\<close> for e
      using that i\<^sub>2.morph_edge_range p\<^sub>1.po1.g.morph_edge_range
      by (simp add: morph_comp_def)
  next
    show \<open>\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v \<in> V\<^bsub>G\<^esub>\<close> if \<open>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>\<close> for v
      using that i\<^sub>2.morph_node_range p\<^sub>1.po1.g.morph_node_range
      by (simp add: morph_comp_def)
  next
    show \<open>\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V (s\<^bsub>lhs r\<^sub>2\<^esub> e) = s\<^bsub>G\<^esub> (\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>\<close> for e
      using that i\<^sub>2.morph_edge_range i\<^sub>2.source_preserve p\<^sub>1.po1.g.source_preserve
      by (simp add: morph_comp_def)
  next
    show \<open>\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V (t\<^bsub>lhs r\<^sub>2\<^esub> e) = t\<^bsub>G\<^esub> (\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>\<close> for e
      using that i\<^sub>2.morph_edge_range i\<^sub>2.target_preserve p\<^sub>1.po1.g.target_preserve
      by (simp add: morph_comp_def)
  next
    show \<open>l\<^bsub>lhs r\<^sub>2\<^esub> v = l\<^bsub>G\<^esub> (\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>\<close> for v
      using that  i\<^sub>2.label_preserve i\<^sub>2.morph_node_range p\<^sub>1.po1.g.label_preserve
      by (simp add: morph_comp_def)
  next
    show \<open>m\<^bsub>lhs r\<^sub>2\<^esub> e = m\<^bsub>G\<^esub> (\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>\<close> for e
      using that i\<^sub>2.mark_preserve i\<^sub>2.morph_edge_range p\<^sub>1.po1.g.mark_preserve
      by (simp add: morph_comp_def)
  qed

  interpret "7+5": pushout_diagram "interf r\<^sub>2" D\<^sub>2 "lhs r\<^sub>2" G "pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" "idM :: ('k, 'k, 'l, 'l) pre_morph" c\<^sub>2 "c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2"
  proof 
    show \<open>\<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> (pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>2\<^esub>\<close> for v
      using that inv_into_f_f[OF c\<^sub>2.inj_nodes] c\<^sub>2.surj_nodes i\<^sub>2.morph_node_range 
        p\<^sub>1.po1.g.morph_node_range
      by (simp add: morph_comp_def pb.c_def j\<^sub>2_def) fastforce
  next
    show \<open>\<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> (pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>2\<^esub>\<close> for e
      using that inv_into_f_f[OF c\<^sub>2.inj_edges] c\<^sub>2.surj_edges i\<^sub>2.morph_edge_range 
        p\<^sub>1.po1.g.morph_edge_range
      by (simp add: morph_comp_def pb.c_def j\<^sub>2_def) fastforce
  next
    show \<open>Ex1M
        (\<lambda>xa. morphism (to_ngraph G) D' xa \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e))
        (to_ngraph G)\<close>
      if \<open>graph D'\<close> \<open>morphism (to_ngraph D\<^sub>2) D' x\<close> \<open>morphism (to_ngraph (lhs r\<^sub>2)) D' y\<close>
        \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('k, 'k, 'l, 'l) pre_morph)\<^esub>\<^sub>V v\<close>
        \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('k, 'k, 'l, 'l) pre_morph)\<^esub>\<^sub>E e\<close>
      for D' :: "('c,'d) ngraph" and x y
    proof -

     have a: \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('k, 'k, 'l, 'l) pre_morph)\<^esub>\<^sub>V v = \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>2\<^esub>\<^sub>V v\<close>
      proof
        fix v
        assume asm: \<open>v \<in> V\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>\<close>

        have c_lifted: \<open>\<^bsub>to_nmorph pb.c \<circ>\<^sub>\<rightarrow> to_nmorph j\<^sub>2\<^esub>\<^sub>V v = \<^bsub>to_nmorph m\<^sub>2\<^esub>\<^sub>V v\<close>
          using c comp_lift_node1 asm
          by blast

        have \<open>\<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('k, 'k, 'l, 'l) pre_morph)\<^esub>\<^sub>V v = \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>V v\<close>
          using \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('k, 'k, 'l, 'l) pre_morph)\<^esub>\<^sub>V v\<close>
            asm
          by simp

        thus \<open>\<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('k, 'k, 'l, 'l) pre_morph)\<^esub>\<^sub>V v = \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>2\<^esub>\<^sub>V v\<close>
          using c_lifted
          by (auto simp add: morph_comp_def to_nmorph_def)
      qed

      have b: \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('k, 'k, 'l, 'l) pre_morph)\<^esub>\<^sub>E e = \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>2\<^esub>\<^sub>E e\<close>
      proof
        fix e
        assume asm: \<open>e \<in> E\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>\<close>

        have d_lifted: \<open>\<^bsub>to_nmorph pb.c \<circ>\<^sub>\<rightarrow> to_nmorph j\<^sub>2\<^esub>\<^sub>E e = \<^bsub>to_nmorph m\<^sub>2\<^esub>\<^sub>E e\<close>
          using d comp_lift_edge1 asm
          by blast

        have \<open>\<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('k, 'k, 'l, 'l) pre_morph)\<^esub>\<^sub>E e = \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>E e\<close>
          using \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('k, 'k, 'l, 'l) pre_morph)\<^esub>\<^sub>E e\<close>
            asm
          by simp

        thus \<open>\<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('k, 'k, 'l, 'l) pre_morph)\<^esub>\<^sub>E e = \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>2\<^esub>\<^sub>E e\<close>
          using d_lifted
          by (auto simp add: morph_comp_def to_nmorph_def)
      qed

      obtain u where
        \<open>morphism (to_ngraph G) D' u\<close>
         \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
         \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
         \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
         \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
        using p\<^sub>2.po1.universal_property[OF \<open>graph D'\<close> \<open>morphism (to_ngraph (lhs r\<^sub>2)) D' y\<close> \<open>morphism (to_ngraph D\<^sub>2) D' x\<close> a b]
        by fast

      interpret u: morphism "to_ngraph G" D' u
        using \<open>morphism (to_ngraph G) D' u\<close>
        by assumption

      interpret x: morphism "to_ngraph D\<^sub>2" D' x
        using \<open>morphism (to_ngraph D\<^sub>2) D' x\<close> by assumption

      have aa: \<open>morphism (to_ngraph G) D' u \<and>
                (\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
                (\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<and> 
                (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> 
                (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e)\<close>
        using \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close> 
          \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> 
          \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> 
          \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> u.morphism_axioms 
          by blast

      show ?thesis
      proof (rule_tac x = u in exI, safe)
        show \<open>morphism (to_ngraph G) D' u\<close>
          using \<open>morphism (to_ngraph G) D' u\<close> by assumption
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph D\<^sub>2\<^esub>\<close> for v
          using \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> that
          by simp
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> if \<open>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>\<close> for e
          using \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> that
          by simp
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> if \<open>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>\<close> for v
          using \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> that
            \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close>
          by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def)
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close> if \<open>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>\<close> for e
          using \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close> that
            \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e\<close>
          by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def)
      next
        show \<open>\<^bsub>ya\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e\<close> if \<open>morphism (to_ngraph G) D' ya\<close> 
          \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
          \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
          \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
          \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
          \<open>e \<in> E\<^bsub>to_ngraph G\<^esub>\<close> for ya e
        proof -
          have bb: \<open>morphism (to_ngraph G) D' ya \<and>
                    (\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
                    (\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<and> 
                    (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> 
                    (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e)\<close>
          proof (intro conjI)
            show \<open>morphism (to_ngraph G) D' ya\<close>
              using \<open>morphism (to_ngraph G) D' ya\<close> by assumption
          next
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
              using \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
                \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close>
              by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def)
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
              using \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
                \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e\<close>
              by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def)
          next
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
              using \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> by assumption
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
              using \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> by assumption
          qed
        

          show ?thesis  
            using ex_eq[OF p\<^sub>2.po1.universal_property[OF \<open>graph D'\<close> 
                  \<open>morphism (to_ngraph (lhs r\<^sub>2)) D' y\<close> \<open>morphism (to_ngraph D\<^sub>2) D' x\<close> a b] aa bb] 
                  \<open>e \<in> E\<^bsub>to_ngraph G\<^esub>\<close>
            by simp
        qed
        next
        show \<open>\<^bsub>ya\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v\<close> if \<open>morphism (to_ngraph G) D' ya\<close> 
          \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
          \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
          \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
          \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
          \<open>v \<in> V\<^bsub>to_ngraph G\<^esub>\<close> for ya v
        proof -
          have bb: \<open>morphism (to_ngraph G) D' ya \<and>
                    (\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
                    (\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<and> 
                    (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> 
                    (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e)\<close>
          proof (intro conjI)
            show \<open>morphism (to_ngraph G) D' ya\<close>
              using \<open>morphism (to_ngraph G) D' ya\<close> by assumption
          next
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
              using \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
                \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close>
              by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def)
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
              using \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
                \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e\<close>
              by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def)
          next
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
              using \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> by assumption
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
              using \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> by assumption
          qed
        

          show ?thesis  
            using ex_eq[OF p\<^sub>2.po1.universal_property[OF \<open>graph D'\<close> 
                  \<open>morphism (to_ngraph (lhs r\<^sub>2)) D' y\<close> \<open>morphism (to_ngraph D\<^sub>2) D' x\<close> a b] aa bb] 
                  \<open>v \<in> V\<^bsub>to_ngraph G\<^esub>\<close>
            by simp
        qed
      qed
    qed
  qed


  interpret seven: pushout_diagram "interf r\<^sub>2" "lhs r\<^sub>2" pb.A D\<^sub>1 idM j\<^sub>2 i\<^sub>2 pb.b
    using pushout_pullback_decomposition[OF "7+5.pushout_diagram_axioms" pb.pb.flip_diagram
        c\<^sub>1.injective_morphism_axioms j\<^sub>2.injective_morphism_axioms]  
    pushout_diagram.flip_diagram
    by blast

  interpret acht: gluing "interf r\<^sub>1" pb.A "rhs r\<^sub>1" j\<^sub>1 idM ..

  interpret neun: gluing "interf r\<^sub>2" pb.A "rhs r\<^sub>2" j\<^sub>2 idM ..

  interpret ten: gluing pb.A neun.H acht.H neun.c acht.c ..



(* aaa and bbb belong to s\<^sub>1 *)
  have  aaa: \<open>\<forall>v\<in>V\<^bsub>interf r\<^sub>1\<^esub>. \<^bsub>f\<^sub>1 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v\<close>
    using p\<^sub>1.po2.node_commutativity a
    by (simp add: morph_comp_def)   
  have bbb: \<open>\<forall>e\<in>E\<^bsub>interf r\<^sub>1\<^esub>. \<^bsub>f\<^sub>1 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e\<close>
    using p\<^sub>1.po2.edge_commutativity b
    by (simp add: morph_comp_def)

  obtain s\<^sub>1 where
    \<open>morphism acht.H H\<^sub>1 s\<^sub>1\<close> and
    \<open>\<And>v. v \<in> V\<^bsub>pb.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.c\<^esub>\<^sub>V v = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> pb.b\<^esub>\<^sub>V v\<close>
    \<open>\<And>e. e \<in> E\<^bsub>pb.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.c\<^esub>\<^sub>E e = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> pb.b\<^esub>\<^sub>E e\<close>
(* and (2) = (8) + (11) *)
    \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
    \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
     using acht.po.universal_property_exist_gen[OF p\<^sub>1.po2.f.H.graph_axioms
        p\<^sub>1.po2.f.morphism_axioms
        wf_morph_comp[OF pb.b.morphism_axioms p\<^sub>1.po2.g.morphism_axioms] aaa bbb]
    by auto

  interpret s\<^sub>1: morphism acht.H H\<^sub>1 s\<^sub>1
    using \<open>morphism acht.H H\<^sub>1 s\<^sub>1\<close> by assumption

  interpret morphism "rhs r\<^sub>1" H\<^sub>1 "s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h"
  proof
    show \<open>\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e \<in> E\<^bsub>H\<^sub>1\<^esub>\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>1\<^esub>\<close> for e
      using that \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
        p\<^sub>1.po2.f.morph_edge_range
      by simp
  next
    show \<open>\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V v \<in> V\<^bsub>H\<^sub>1\<^esub>\<close> if \<open>v \<in> V\<^bsub>rhs r\<^sub>1\<^esub>\<close> for v
      using that \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
        p\<^sub>1.po2.f.morph_node_range
      by simp
  next
    show \<open>\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V (s\<^bsub>rhs r\<^sub>1\<^esub> e) = s\<^bsub>H\<^sub>1\<^esub> (\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>1\<^esub>\<close> for e
      using that p\<^sub>1.r.r.H.source_integrity  p\<^sub>1.po2.f.source_preserve
        \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
        \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close> p\<^sub>1.r.r.H.source_integrity 
      by simp
  next
    show \<open>\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V (t\<^bsub>rhs r\<^sub>1\<^esub> e) = t\<^bsub>H\<^sub>1\<^esub> (\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>1\<^esub>\<close> for e
      using that p\<^sub>1.r.r.H.target_integrity  p\<^sub>1.po2.f.target_preserve
        \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
        \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close> p\<^sub>1.r.r.H.target_integrity 
      by simp
  next
    show \<open>l\<^bsub>rhs r\<^sub>1\<^esub> v = l\<^bsub>H\<^sub>1\<^esub> (\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>rhs r\<^sub>1\<^esub>\<close> for v
      using that p\<^sub>1.po2.f.label_preserve
        \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
        \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
      by simp
  next
    show \<open> m\<^bsub>rhs r\<^sub>1\<^esub> e = m\<^bsub>H\<^sub>1\<^esub> (\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>1\<^esub>\<close> for e
      using that p\<^sub>1.po2.f.mark_preserve
        \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
        \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
      by simp
  qed

  interpret "8+11": pushout_diagram "interf r\<^sub>1" "rhs r\<^sub>1" D\<^sub>1 H\<^sub>1 "idM :: ('a, 'a, 'b, 'b) pre_morph" "pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1" \<open>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<close> h\<^sub>1
  proof
    show \<open>\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>1\<^esub>\<close> for v
      using that aaa
        \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
      by (fastforce simp add: morph_comp_def)
  next
    show \<open>\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>1\<^esub>\<close> for e
      using that bbb
        \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
      by (fastforce simp add: morph_comp_def)
  next
    show \<open>Ex1M
        (\<lambda>xa. morphism (to_ngraph H\<^sub>1) D' xa \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e))
        (to_ngraph H\<^sub>1)\<close> 
      if  \<open>graph D'\<close>
          \<open>morphism (to_ngraph (rhs r\<^sub>1)) D' x\<close>
          \<open>morphism (to_ngraph D\<^sub>1) D' y\<close>
          \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>V v\<close>
          \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>E e\<close>
        for D' :: "('c,'d) ngraph" and x y
    proof -
      have aaa: \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>1\<^esub>\<^sub>V v\<close>
      proof -
        have \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>to_nmorph (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>V v = \<^bsub>to_nmorph m\<^sub>1\<^esub>\<^sub>V v\<close>
          using comp_lift_node1[of "interf r\<^sub>1" pb.b j\<^sub>1 m\<^sub>1] a to_nmorph_dist
          by metis

        thus ?thesis
          using \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>V v\<close> 
          by (auto simp add: morph_comp_def )
      qed
      have bbb: \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>1\<^esub>\<^sub>E e\<close>
      proof -
        have \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>to_nmorph (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>E e = \<^bsub>to_nmorph m\<^sub>1\<^esub>\<^sub>E e\<close>
          using comp_lift_edge1[of "interf r\<^sub>1" pb.b j\<^sub>1 m\<^sub>1] b to_nmorph_dist
          by metis

        thus ?thesis
          using \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('a, 'a, 'b, 'b) pre_morph)\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (pb.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>E e\<close> 
          by (auto simp add: morph_comp_def)
      qed

      obtain u where \<open>morphism (to_ngraph H\<^sub>1) D' u\<close>
         \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
         \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
         \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
         \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
        using p\<^sub>1.po2.universal_property[OF \<open>graph D'\<close> \<open>morphism (to_ngraph (rhs r\<^sub>1)) D' x\<close>
            \<open>morphism (to_ngraph D\<^sub>1) D' y\<close> aaa bbb]
        by fast

      have aaaa: \<open>morphism (to_ngraph H\<^sub>1) D' u \<and>
                  (\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
                  (\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> 
                  (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> 
                  (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)\<close>
        using \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> 
          \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
          \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
          \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
          \<open>morphism (to_ngraph H\<^sub>1) D' u\<close> 
        by fastforce

      show ?thesis
      proof (rule_tac x = u in exI, safe)
        show \<open>morphism (to_ngraph H\<^sub>1) D' u\<close>
          using \<open>morphism (to_ngraph H\<^sub>1) D' u\<close> by assumption
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>\<close> for v
          using that \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
            \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
          by (auto simp add: morph_comp_def to_ngraph_def to_nmorph_def)
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>\<close> for e
          using that \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
            \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
          by (auto simp add: morph_comp_def to_ngraph_def to_nmorph_def)
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph D\<^sub>1\<^esub>\<close> for v
          using that \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
          by simp
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>to_ngraph D\<^sub>1\<^esub>\<close> for e
          using that \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
          by simp
      next
        show \<open>\<^bsub>ya\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e\<close>
          if  \<open>morphism (to_ngraph H\<^sub>1) D' ya\<close>
              \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
              \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
              \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
              \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
              \<open>e \<in> E\<^bsub>to_ngraph H\<^sub>1\<^esub>\<close>
            for ya e
        proof -
          have bbbb: \<open>morphism (to_ngraph H\<^sub>1) D' ya \<and>
                    (\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
                    (\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> 
                    (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> 
                    (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)\<close>
          proof (intro conjI)
            show \<open>morphism (to_ngraph H\<^sub>1) D' ya\<close>
              using \<open>morphism (to_ngraph H\<^sub>1) D' ya\<close> by assumption
          next
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
              using \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
              by (auto simp add: morph_comp_def to_ngraph_def to_nmorph_def)
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
              using \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
              by (auto simp add: morph_comp_def to_ngraph_def to_nmorph_def)
          next
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
              using \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> by assumption
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
              using \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close> by assumption
          qed
        
          show ?thesis
          using ex_eq[OF p\<^sub>1.po2.universal_property[OF \<open>graph D'\<close> \<open>morphism (to_ngraph (rhs r\<^sub>1)) D' x\<close>
            \<open>morphism (to_ngraph D\<^sub>1) D' y\<close> aaa bbb] aaaa bbbb] \<open>e \<in> E\<^bsub>to_ngraph H\<^sub>1\<^esub>\<close>
          by simp
      qed
      next
        show \<open>\<^bsub>ya\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v\<close>
          if  \<open>morphism (to_ngraph H\<^sub>1) D' ya\<close>
              \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
              \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
              \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
              \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
              \<open>v \<in> V\<^bsub>to_ngraph H\<^sub>1\<^esub>\<close>
            for ya v
        proof -
          have bbbb: \<open>morphism (to_ngraph H\<^sub>1) D' ya \<and>
                    (\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
                    (\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> 
                    (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> 
                    (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)\<close>
          proof (intro conjI)
            show \<open>morphism (to_ngraph H\<^sub>1) D' ya\<close>
              using \<open>morphism (to_ngraph H\<^sub>1) D' ya\<close> by assumption
          next
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
              using \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
              by (auto simp add: morph_comp_def to_ngraph_def to_nmorph_def)
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
              using \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
              by (auto simp add: morph_comp_def to_ngraph_def to_nmorph_def)
          next
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
              using \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> by assumption
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
              using \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close> by assumption
          qed
        
          show ?thesis
          using ex_eq[OF p\<^sub>1.po2.universal_property[OF \<open>graph D'\<close> \<open>morphism (to_ngraph (rhs r\<^sub>1)) D' x\<close>
            \<open>morphism (to_ngraph D\<^sub>1) D' y\<close> aaa bbb] aaaa bbbb] \<open>v \<in> V\<^bsub>to_ngraph H\<^sub>1\<^esub>\<close>
          by simp
      qed
    qed
  qed
qed

  interpret eleven:  pushout_diagram pb.A D\<^sub>1 acht.H H\<^sub>1 pb.b acht.c h\<^sub>1 s\<^sub>1
    using pushout_decomposition[OF pb.b.morphism_axioms s\<^sub>1.morphism_axioms acht.po.flip_diagram "8+11.flip_diagram"]
      \<open>\<And>e. e \<in> E\<^bsub>pb.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.c\<^esub>\<^sub>E e = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> pb.b\<^esub>\<^sub>E e\<close> \<open>\<And>v. v \<in> V\<^bsub>pb.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.c\<^esub>\<^sub>V v = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> pb.b\<^esub>\<^sub>V v\<close>
    by simp


(* start of s\<^sub>2 *)

  have aaa2: \<open>\<forall>v\<in>V\<^bsub>interf r\<^sub>2\<^esub>. \<^bsub>f\<^sub>2 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>V v\<close>
    using p\<^sub>2.po2.node_commutativity c
    by (simp add: morph_comp_def)   
  have bbb2: \<open>\<forall>e\<in>E\<^bsub>interf r\<^sub>2\<^esub>. \<^bsub>f\<^sub>2 \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>E e\<close>
    using p\<^sub>2.po2.edge_commutativity d
    by (simp add: morph_comp_def) 
   
   obtain s\<^sub>2 where
    \<open>morphism neun.H H\<^sub>2 s\<^sub>2\<close> and
    \<open>\<And>v. v \<in> V\<^bsub>pb.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.c\<^esub>\<^sub>V v = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> pb.c\<^esub>\<^sub>V v\<close>
    \<open>\<And>e. e \<in> E\<^bsub>pb.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.c\<^esub>\<^sub>E e = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> pb.c\<^esub>\<^sub>E e\<close>
(* (4) = (9)+(12) *)
    \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close>
    \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close>
    using neun.po.universal_property_exist_gen[OF p\<^sub>2.po2.f.H.graph_axioms
      p\<^sub>2.po2.f.morphism_axioms
      wf_morph_comp[OF pb.c.morphism_axioms p\<^sub>2.po2.g.morphism_axioms] aaa2 bbb2]
    by fast

  interpret s\<^sub>2: morphism neun.H H\<^sub>2 s\<^sub>2
    using \<open>morphism neun.H H\<^sub>2 s\<^sub>2\<close> by assumption

  interpret morphism "rhs r\<^sub>2" H\<^sub>2 "s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h"
  proof
    show \<open>\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>E e \<in> E\<^bsub>H\<^sub>2\<^esub>\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>2\<^esub>\<close> for e
      using that  \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close> p\<^sub>2.po2.f.morph_edge_range
      by simp
  next
    show \<open>\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>V v \<in> V\<^bsub>H\<^sub>2\<^esub>\<close> if \<open>v \<in> V\<^bsub>rhs r\<^sub>2\<^esub>\<close> for v
      using that \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close> p\<^sub>2.po2.f.morph_node_range 
      by simp
  next
    show \<open>\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>V (s\<^bsub>rhs r\<^sub>2\<^esub> e) = s\<^bsub>H\<^sub>2\<^esub> (\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>2\<^esub>\<close> for e
      using that
        \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close>
        \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close>
        p\<^sub>2.po2.f.source_preserve p\<^sub>2.r.r.H.source_integrity
      by simp
  next
    show \<open>\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>V (t\<^bsub>rhs r\<^sub>2\<^esub> e) = t\<^bsub>H\<^sub>2\<^esub> (\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>2\<^esub>\<close> for e
      using that 
        \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close>
        \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close>
        p\<^sub>2.po2.f.target_preserve p\<^sub>2.r.r.H.target_integrity
      by simp
  next
    show \<open>l\<^bsub>rhs r\<^sub>2\<^esub> v = l\<^bsub>H\<^sub>2\<^esub> (\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>rhs r\<^sub>2\<^esub>\<close> for v
      using that \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close>
        p\<^sub>2.po2.f.label_preserve
      by simp
  next
    show \<open>m\<^bsub>rhs r\<^sub>2\<^esub> e = m\<^bsub>H\<^sub>2\<^esub> (\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>2\<^esub>\<close> for e
      using that \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close>
        p\<^sub>2.po2.f.mark_preserve
      by simp
  qed

  interpret "9+12": pushout_diagram "interf r\<^sub>2" "rhs r\<^sub>2" D\<^sub>2 H\<^sub>2 "idM :: ('k, 'k, 'l, 'l) pre_morph" "pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" "s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h" h\<^sub>2
  proof
    show \<open>\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>V v = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> (pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>2\<^esub>\<close> for v
      using that \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close> aaa2
      by (fastforce simp add: morph_comp_def)
  next
    show \<open>\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h \<circ>\<^sub>\<rightarrow> idM\<^esub>\<^sub>E e = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> (pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>2\<^esub>\<close> for e
      using that \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close> bbb2
      by (fastforce simp add: morph_comp_def)
  next
    show \<open>Ex1M
        (\<lambda>xa. morphism (to_ngraph H\<^sub>2) D' xa \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e))
        (to_ngraph H\<^sub>2)\<close>
      if  \<open>graph D'\<close>
          \<open>morphism (to_ngraph (rhs r\<^sub>2)) D' x\<close>
          \<open>morphism (to_ngraph D\<^sub>2) D' y\<close>
          \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('k, 'k, 'l, 'l) pre_morph)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>V v\<close>
          \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('k, 'k, 'l, 'l) pre_morph)\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (pb.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>E e\<close>
        for D' :: "('c,'d) ngraph" and x y
    proof -
      have a: \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('k, 'k, 'l, 'l) pre_morph)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>2\<^esub>\<^sub>V v\<close>
        sorry

      have b: \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (idM :: ('k, 'k, 'l, 'l) pre_morph)\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>2\<^esub>\<^sub>E e\<close>
        sorry

      obtain u where \<open>morphism (to_ngraph H\<^sub>2) D' u\<close>
        using p\<^sub>2.po2.universal_property[OF \<open>graph D'\<close> 
            \<open>morphism (to_ngraph (rhs r\<^sub>2)) D' x\<close>
            \<open>morphism (to_ngraph D\<^sub>2) D' y\<close>
            a b]
        by fast
      show ?thesis
      proof (rule_tac x = u in exI, safe)
        show \<open>morphism (to_ngraph H\<^sub>2) D' u\<close>
          using \<open>morphism (to_ngraph H\<^sub>2) D' u\<close>
          by assumption
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>\<close> for v
          sorry
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>\<close> for e
          sorry
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph D\<^sub>2\<^esub>\<close> for v
          sorry
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>to_ngraph D\<^sub>2\<^esub>\<close> for e
          sorry
      next
        show \<open>\<^bsub>ya\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e\<close>
          if  \<open>morphism (to_ngraph H\<^sub>2) D' ya\<close>
              \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
              \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
              \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
              \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
              \<open>e \<in> E\<^bsub>to_ngraph H\<^sub>2\<^esub>\<close>
            for ya e
          sorry
      next
        show \<open>\<^bsub>ya\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v\<close>
          if  \<open>morphism (to_ngraph H\<^sub>2) D' ya\<close>
              \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
              \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
              \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
              \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
              \<open>v \<in> V\<^bsub>to_ngraph H\<^sub>2\<^esub>\<close>
            for ya v
          sorry
      qed
    qed
  qed

  interpret twelve: pushout_diagram pb.A D\<^sub>2 neun.H H\<^sub>2 pb.c neun.c h\<^sub>2 s\<^sub>2
   using pushout_decomposition[OF pb.c.morphism_axioms s\<^sub>2.morphism_axioms neun.po.flip_diagram "9+12.flip_diagram"]
      \<open>\<And>e. e \<in> E\<^bsub>pb.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.c\<^esub>\<^sub>E e = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> pb.c\<^esub>\<^sub>E e\<close> \<open>\<And>v. v \<in> V\<^bsub>pb.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.c\<^esub>\<^sub>V v = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> pb.c\<^esub>\<^sub>V v\<close>
   by simp

(* one side *)
    interpret "7+11": pushout_diagram "interf r\<^sub>2" acht.H "lhs r\<^sub>2" H\<^sub>1 "acht.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" idM s\<^sub>1 "h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2"
      using pushout_composition[OF seven.flip_diagram eleven.flip_diagram ] by assumption

    interpret "9+10": pushout_diagram "interf r\<^sub>2" acht.H "rhs r\<^sub>2" ten.H "acht.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" idM ten.h "ten.c \<circ>\<^sub>\<rightarrow> neun.h"
      using pushout_composition[OF neun.po.flip_diagram ten.po.pushout_diagram_axioms] by assumption

(* flipped ones are needed for the sequential independence *)
    interpret pushout_diagram "interf r\<^sub>2" "lhs r\<^sub>2" acht.H H\<^sub>1 idM "acht.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" "h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2" s\<^sub>1
      using "7+11.flip_diagram" by assumption

    interpret pushout_diagram "interf r\<^sub>2" "rhs r\<^sub>2" acht.H ten.H idM "acht.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" "ten.c \<circ>\<^sub>\<rightarrow> neun.h" ten.h
      using "9+10.flip_diagram" by assumption

(* show second direct derivation *)
    interpret direct_derivation r\<^sub>2 H\<^sub>1 "h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2" acht.H "acht.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" s\<^sub>1 ten.H "ten.c \<circ>\<^sub>\<rightarrow> neun.h" ten.h
    proof
      show \<open>inj_on \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V V\<^bsub>lhs r\<^sub>2\<^esub>\<close>
        using injective_morphism.inj_nodes[OF inj_comp_inj[OF i\<^sub>2.injective_morphism_axioms h\<^sub>1.injective_morphism_axioms ]]
        by assumption
    next
      show \<open> inj_on \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E E\<^bsub>lhs r\<^sub>2\<^esub>\<close>
        using injective_morphism.inj_edges[OF inj_comp_inj[OF i\<^sub>2.injective_morphism_axioms h\<^sub>1.injective_morphism_axioms ]]
        by assumption
    qed

(* first seq. indep. *)
    interpret p3: sequential_independence r\<^sub>1 G g\<^sub>1 D\<^sub>1 m\<^sub>1 c\<^sub>1 H\<^sub>1 f\<^sub>1 h\<^sub>1 r\<^sub>2 "h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2" acht.H "acht.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" s\<^sub>1 ten.H "ten.c \<circ>\<^sub>\<rightarrow> neun.h" ten.h
    proof
      show \<open>\<exists>i. morphism (rhs r\<^sub>1) acht.H i \<and>
        (\<forall>v\<in>V\<^bsub>rhs r\<^sub>1\<^esub>. \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>rhs r\<^sub>1\<^esub>. \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e)\<close>
      proof (rule_tac x = acht.h in exI, intro conjI)
        show \<open>morphism (rhs r\<^sub>1) acht.H acht.h\<close>
          using acht.inc_h.morphism_axioms by assumption
      next
        show \<open>\<forall>v\<in>V\<^bsub>rhs r\<^sub>1\<^esub>. \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
          by (simp add: \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>)
      next
        show \<open>\<forall>e\<in>E\<^bsub>rhs r\<^sub>1\<^esub>. \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
          by (simp add: \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> acht.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>)
      qed
    next
      show \<open>\<exists>j. morphism (lhs r\<^sub>2) D\<^sub>1 j \<and>
        (\<forall>v\<in>V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> j\<^esub>\<^sub>V v = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> j\<^esub>\<^sub>E e = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e)\<close>
      proof (rule_tac x = i\<^sub>2 in exI, intro conjI)
        show \<open>morphism (lhs r\<^sub>2) D\<^sub>1 i\<^sub>2\<close>
          using i\<^sub>2.morphism_axioms by assumption
      next
        show \<open>\<forall>v\<in>V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v\<close>
          by simp
      next
        show \<open>\<forall>e\<in>E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e\<close>
          by simp
      qed
    qed




    interpret "6+12": pushout_diagram "interf r\<^sub>1" neun.H "lhs r\<^sub>1" H\<^sub>2 "neun.c \<circ>\<^sub>\<rightarrow> j\<^sub>1" idM s\<^sub>2 "h\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1"
      using pushout_composition[OF six.pushout_diagram_axioms twelve.flip_diagram ] by assumption
    
    interpret pushout_diagram "interf r\<^sub>1" "lhs r\<^sub>1" neun.H H\<^sub>2 idM "neun.c \<circ>\<^sub>\<rightarrow> j\<^sub>1" "h\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1" s\<^sub>2
      using "6+12.flip_diagram" by assumption

    interpret "8+10": pushout_diagram "interf r\<^sub>1" neun.H "rhs r\<^sub>1" ten.H "neun.c \<circ>\<^sub>\<rightarrow> j\<^sub>1" idM ten.c "ten.h \<circ>\<^sub>\<rightarrow> acht.h"
      using pushout_composition[OF acht.po.flip_diagram ten.po.flip_diagram] by assumption

    thm "8+10.flip_diagram"
    interpret pushout_diagram "interf r\<^sub>1" "rhs r\<^sub>1" neun.H ten.H idM "neun.c \<circ>\<^sub>\<rightarrow> j\<^sub>1" "ten.h \<circ>\<^sub>\<rightarrow> acht.h" ten.c
      using "8+10.flip_diagram" by assumption

    interpret direct_derivation r\<^sub>1 H\<^sub>2 "h\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1" neun.H "neun.c \<circ>\<^sub>\<rightarrow> j\<^sub>1" s\<^sub>2 ten.H "ten.h \<circ>\<^sub>\<rightarrow> acht.h" ten.c
    proof
      show \<open>inj_on \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V V\<^bsub>lhs r\<^sub>1\<^esub>\<close>
        using injective_morphism.inj_nodes[OF inj_comp_inj[OF i\<^sub>1.injective_morphism_axioms h\<^sub>2.injective_morphism_axioms ]]
        by assumption
    next
      show \<open>inj_on \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>E E\<^bsub>lhs r\<^sub>1\<^esub>\<close>
        using injective_morphism.inj_edges[OF inj_comp_inj[OF i\<^sub>1.injective_morphism_axioms h\<^sub>2.injective_morphism_axioms ]]
        by assumption
    qed

    interpret p4: sequential_independence r\<^sub>2 G g\<^sub>2 D\<^sub>2 m\<^sub>2 c\<^sub>2 H\<^sub>2 f\<^sub>2 h\<^sub>2 r\<^sub>1  "h\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1" neun.H "neun.c \<circ>\<^sub>\<rightarrow> j\<^sub>1" s\<^sub>2 ten.H "ten.h \<circ>\<^sub>\<rightarrow> acht.h" ten.c 
    proof
      show \<open>\<exists>i. morphism (rhs r\<^sub>2) neun.H i \<and>
        (\<forall>v\<in>V\<^bsub>rhs r\<^sub>2\<^esub>. \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>rhs r\<^sub>2\<^esub>. \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e)\<close>
        using \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close> \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> neun.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close> neun.inc_h.morphism_axioms by blast
    next
      show \<open>\<exists>j. morphism (lhs r\<^sub>1) D\<^sub>2 j \<and>
        (\<forall>v\<in>V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> j\<^esub>\<^sub>V v = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> j\<^esub>\<^sub>E e = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>E e)\<close>
        using i\<^sub>1.morphism_axioms by blast
    qed

    show ?thesis
      using p3.sequential_independence_axioms p4.sequential_independence_axioms
      by fast
qed

end