theory LocalChurchRosser
  imports DirectDerivation
begin
(* Fund. Alg. GT, PDF. P. 117
https://link.springer.com/content/pdf/10.1007/3-540-31188-2.pdf?pdf=button
 *)
(*  declare [[show_sorts]]
 *) 
locale parallel_independence =
  p\<^sub>1: direct_derivation r\<^sub>1 b\<^sub>1 b\<^sub>1' G g\<^sub>1 D\<^sub>1 m\<^sub>1 c\<^sub>1 H\<^sub>1 f\<^sub>1 h\<^sub>1 +
  p\<^sub>2: direct_derivation r\<^sub>2 b\<^sub>2 b\<^sub>2' G g\<^sub>2 D\<^sub>2 m\<^sub>2 c\<^sub>2 H\<^sub>2 f\<^sub>2 h\<^sub>2
  for r\<^sub>1 b\<^sub>1 b\<^sub>1' G g\<^sub>1 D\<^sub>1 m\<^sub>1 c\<^sub>1 H\<^sub>1 f\<^sub>1 h\<^sub>1 
      r\<^sub>2 b\<^sub>2 b\<^sub>2' g\<^sub>2 D\<^sub>2 m\<^sub>2 c\<^sub>2 H\<^sub>2 f\<^sub>2 h\<^sub>2 +
  assumes
    i: \<open>\<exists>i. morphism (lhs r\<^sub>1) D\<^sub>2 i 
            \<and> (\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v) 
            \<and> (\<forall>e \<in> E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>E e = \<^bsub>g\<^sub>1\<^esub>\<^sub>E e)\<close> and
    j: \<open>\<exists>j. morphism (lhs r\<^sub>2) D\<^sub>1 j 
            \<and> (\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> j\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v) 
            \<and> (\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> j\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e)\<close>

locale sequential_independence =
  p\<^sub>1: direct_derivation r\<^sub>1 b\<^sub>1 b\<^sub>1' G g\<^sub>1 D\<^sub>1 m\<^sub>1 c\<^sub>1 H\<^sub>1 f\<^sub>1 h\<^sub>1 +
  p\<^sub>2: direct_derivation r\<^sub>2 b\<^sub>2 b\<^sub>2' H\<^sub>1 g\<^sub>2 D\<^sub>2 m\<^sub>2 c\<^sub>2 H\<^sub>2 f\<^sub>2 h\<^sub>2
  for r\<^sub>1 b\<^sub>1 b\<^sub>1' G g\<^sub>1 D\<^sub>1 m\<^sub>1 c\<^sub>1 H\<^sub>1 f\<^sub>1 h\<^sub>1 
      r\<^sub>2 b\<^sub>2 b\<^sub>2' g\<^sub>2 D\<^sub>2 m\<^sub>2 c\<^sub>2 H\<^sub>2 f\<^sub>2 h\<^sub>2 +
  assumes
    i: \<open>\<exists>i. morphism (rhs r\<^sub>1) D\<^sub>2 i 
            \<and> (\<forall>v \<in> V\<^bsub>rhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v) 
            \<and> (\<forall>e \<in> E\<^bsub>rhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e)\<close> and
    j: \<open>\<exists>j. morphism (lhs r\<^sub>2) D\<^sub>1 j 
            \<and> (\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> j\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v) 
            \<and> (\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> j\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e)\<close> 


theorem (in parallel_independence) church_rosser1:
  shows \<open>\<exists>(g' ::('o, 'm, 'p, 'n) pre_morph)
           (D' :: ('k \<times> 'u + 'e, 'l \<times> 'v + 'f, 'g, 'h) pre_graph) 
           (m':: ('q, 'k \<times> 'u + 'e, 'r, 'l \<times> 'v + 'f) pre_morph)
           (c':: ('k \<times> 'u + 'e, 'm, 'l \<times> 'v + 'f, 'n) pre_morph)
           (H :: (('k \<times> 'u + 's) + 'k \<times> 'u + 'e, ('l \<times> 'v + 't) + 'l \<times> 'v + 'f, 'g, 'h) pre_graph)
           (f':: ('s, ('k \<times> 'u + 's) + 'k \<times> 'u + 'e, 't, ('l \<times> 'v + 't) + 'l \<times> 'v + 'f) pre_morph)
            h' 
            (g'')
             (D'' ::('k \<times> 'u + 's, 'l \<times> 'v + 't, 'g, 'h) pre_graph)
              m'' c'' 
            (H :: (('k \<times> 'u + 's) + 'k \<times> 'u + 'e, ('l \<times> 'v + 't) + 'l \<times> 'v + 'f, 'g, 'h) pre_graph)
             f'' h''. 
                  sequential_independence r\<^sub>1 b\<^sub>1 b\<^sub>1' G g\<^sub>1 D\<^sub>1 m\<^sub>1 c\<^sub>1 H\<^sub>1 f\<^sub>1 h\<^sub>1 r\<^sub>2 b\<^sub>2 b\<^sub>2' g' D' m' c' H f' h'
                \<and> sequential_independence r\<^sub>2 b\<^sub>2 b\<^sub>2' G g\<^sub>2 D\<^sub>2 m\<^sub>2 c\<^sub>2 H\<^sub>2 f\<^sub>2 h\<^sub>2 r\<^sub>1 b\<^sub>1 b\<^sub>1' g'' D'' m'' c'' H f'' h''\<close>
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
                      \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close> 
                      \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>E e = \<^bsub>g\<^sub>1\<^esub>\<^sub>E e\<close> 
                 and  \<open>morphism (lhs r\<^sub>2) D\<^sub>1 i\<^sub>2\<close>  
                      \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close>
                      \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e\<close>
    using i j by auto
  interpret i\<^sub>1: morphism "lhs r\<^sub>1" D\<^sub>2 i\<^sub>1 
    using \<open>morphism (lhs r\<^sub>1) D\<^sub>2 i\<^sub>1\<close> by assumption

  interpret i\<^sub>1: injective_morphism "lhs r\<^sub>1" D\<^sub>2 i\<^sub>1    
  proof
    show \<open>inj_on \<^bsub>i\<^sub>1\<^esub>\<^sub>V V\<^bsub>lhs r\<^sub>1\<^esub>\<close>
      using \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close>
        c\<^sub>2.inj_nodes p\<^sub>1.gi.inj_nodes
      by (simp add: inj_on_def morph_comp_def) metis
  next
    show \<open>inj_on \<^bsub>i\<^sub>1\<^esub>\<^sub>E E\<^bsub>lhs r\<^sub>1\<^esub>\<close>
      using \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>E e = \<^bsub>g\<^sub>1\<^esub>\<^sub>E e\<close>
        c\<^sub>2.inj_edges p\<^sub>1.gi.inj_edges
      by (simp add: inj_on_def morph_comp_def) metis
  qed

  interpret i\<^sub>2: morphism "lhs r\<^sub>2" D\<^sub>1 i\<^sub>2
    using \<open>morphism (lhs r\<^sub>2) D\<^sub>1 i\<^sub>2\<close>
    by assumption

  interpret i\<^sub>2: injective_morphism "lhs r\<^sub>2" D\<^sub>1 i\<^sub>2
  proof
    show \<open>inj_on \<^bsub>i\<^sub>2\<^esub>\<^sub>V V\<^bsub>lhs r\<^sub>2\<^esub>\<close>
      using \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close>
        c\<^sub>1.inj_nodes p\<^sub>2.gi.inj_nodes
      by (simp add: inj_on_def morph_comp_def) metis
  next
    show \<open>inj_on \<^bsub>i\<^sub>2\<^esub>\<^sub>E E\<^bsub>lhs r\<^sub>2\<^esub>\<close>
      using \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e\<close>
        c\<^sub>1.inj_edges p\<^sub>2.gi.inj_edges
      by (simp add: inj_on_def morph_comp_def) metis
  qed
  interpret "c12": pullback_construction D\<^sub>1 G D\<^sub>2 c\<^sub>1 c\<^sub>2 ..
  interpret wf_b\<^sub>1i\<^sub>1: morphism "interf r\<^sub>1" D\<^sub>2 "i\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1"
    using wf_morph_comp[OF p\<^sub>1.r.k.morphism_axioms i\<^sub>1.morphism_axioms]
    by assumption

(* j1 start *)
  have a: \<open>\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> m\<^sub>1\<^esub>\<^sub>V v = \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> (i\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1)\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>1\<^esub>\<close> for v
    using that "c12.pb.node_commutativity"  \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close>
      p\<^sub>1.po1.node_commutativity p\<^sub>1.r.k.morph_node_range
    by (simp add: morph_comp_def "c12.b_def" "c12.c_def" "c12.A_def")
  have b: \<open>\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> m\<^sub>1\<^esub>\<^sub>E e = \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> (i\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1)\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>1\<^esub>\<close> for e
    using that "c12.pb.edge_commutativity"  \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>E e = \<^bsub>g\<^sub>1\<^esub>\<^sub>E e\<close>
      p\<^sub>1.po1.edge_commutativity p\<^sub>1.r.k.morph_edge_range
    by (simp add: morph_comp_def "c12.b_def" "c12.c_def" "c12.A_def")

  obtain j\<^sub>1 where \<open>morphism (interf r\<^sub>1) c12.A j\<^sub>1\<close>
    and \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v = \<^bsub>m\<^sub>1\<^esub>\<^sub>V v\<close>
        \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e = \<^bsub>m\<^sub>1\<^esub>\<^sub>E e\<close>
    and \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v = \<^bsub>i\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1\<^esub>\<^sub>V v\<close>
        \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e = \<^bsub>i\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1\<^esub>\<^sub>E e\<close>
    using c12.pb.universal_property_exist_gen[OF p\<^sub>1.r.k.G.graph_axioms
               wf_b\<^sub>1i\<^sub>1.morphism_axioms p\<^sub>1.po1.c.morphism_axioms a b]
    by fast
  interpret j\<^sub>1: morphism "interf r\<^sub>1" c12.A j\<^sub>1
    using \<open>morphism (interf r\<^sub>1) c12.A j\<^sub>1\<close> 
    by assumption
  interpret j\<^sub>1: injective_morphism "interf r\<^sub>1" c12.A j\<^sub>1
  proof
    show \<open>inj_on \<^bsub>j\<^sub>1\<^esub>\<^sub>V V\<^bsub>interf r\<^sub>1\<^esub>\<close>
      thm c12.b.morphism_axioms
      using \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v = \<^bsub>m\<^sub>1\<^esub>\<^sub>V v\<close> p\<^sub>1.d_inj.inj_nodes
      by (simp add: morph_comp_def inj_on_def) metis
  next
    show \<open>inj_on \<^bsub>j\<^sub>1\<^esub>\<^sub>E E\<^bsub>interf r\<^sub>1\<^esub>\<close>
      using \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e = \<^bsub>m\<^sub>1\<^esub>\<^sub>E e\<close> p\<^sub>1.d_inj.inj_edges
      by (simp add: morph_comp_def inj_on_def) metis
  qed
     
(* j2 start *)

  interpret b\<^sub>2i\<^sub>2: morphism "interf r\<^sub>2" D\<^sub>1 "i\<^sub>2 \<circ>\<^sub>\<rightarrow> b\<^sub>2"
    using wf_morph_comp[OF p\<^sub>2.r.k.morphism_axioms i\<^sub>2.morphism_axioms]
    by assumption


  have a: \<open>\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> (i\<^sub>2 \<circ>\<^sub>\<rightarrow> b\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> m\<^sub>2\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>2\<^esub>\<close> for v
    using c12.pb.node_commutativity  \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close>
      p\<^sub>2.po1.node_commutativity p\<^sub>2.r.k.morph_node_range that
    by (simp add: morph_comp_def c12.b_def c12.c_def c12.A_def)

  have b: \<open>\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> (i\<^sub>2 \<circ>\<^sub>\<rightarrow> b\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> m\<^sub>2\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>2\<^esub>\<close> for e
    using c12.pb.edge_commutativity  \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e\<close>
      p\<^sub>2.po1.edge_commutativity p\<^sub>2.r.k.morph_edge_range that
    by (simp add: morph_comp_def c12.b_def c12.c_def c12.A_def)

  obtain j\<^sub>2 where \<open>morphism (interf r\<^sub>2) c12.A j\<^sub>2\<close>
    and \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>V v = \<^bsub>m\<^sub>2\<^esub>\<^sub>V v\<close> \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>E e = \<^bsub>m\<^sub>2\<^esub>\<^sub>E e\<close>
    and j2c: \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>V v = \<^bsub>i\<^sub>2 \<circ>\<^sub>\<rightarrow> b\<^sub>2\<^esub>\<^sub>V v\<close>  \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>E e = \<^bsub>i\<^sub>2 \<circ>\<^sub>\<rightarrow> b\<^sub>2\<^esub>\<^sub>E e\<close>
    using c12.pb.universal_property_exist_gen[OF p\<^sub>2.r.k.G.graph_axioms p\<^sub>2.po1.c.morphism_axioms b\<^sub>2i\<^sub>2.morphism_axioms a b]
    by fast
  interpret j\<^sub>2: morphism "interf r\<^sub>2" c12.A j\<^sub>2
    using \<open>morphism (interf r\<^sub>2) c12.A j\<^sub>2\<close> 
    by assumption

  interpret j\<^sub>2: injective_morphism "interf r\<^sub>2" c12.A j\<^sub>2
  proof
    show \<open>inj_on \<^bsub>j\<^sub>2\<^esub>\<^sub>V V\<^bsub>interf r\<^sub>2\<^esub>\<close>
      using \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>V v = \<^bsub>m\<^sub>2\<^esub>\<^sub>V v\<close>  p\<^sub>2.d_inj.inj_nodes
      by (simp add: morph_comp_def inj_on_def) metis
  next
    show \<open>inj_on \<^bsub>j\<^sub>2\<^esub>\<^sub>E E\<^bsub>interf r\<^sub>2\<^esub>\<close>
      using \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>E e = \<^bsub>m\<^sub>2\<^esub>\<^sub>E e\<close>  p\<^sub>2.d_inj.inj_edges
      by (simp add: morph_comp_def inj_on_def) metis
  qed

(* commutativity *)

  interpret morphism "interf r\<^sub>1" D\<^sub>1 "c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1"
    using wf_morph_comp[OF j\<^sub>1.morphism_axioms c12.b.morphism_axioms]
    by assumption
  interpret morphism "lhs r\<^sub>1" G "c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1"
    using wf_morph_comp[OF i\<^sub>1.morphism_axioms p\<^sub>2.po1.g.morphism_axioms]
    by assumption

  interpret pb1: pullback_diagram "interf r\<^sub>1" "lhs r\<^sub>1" D\<^sub>1 G b\<^sub>1 m\<^sub>1 g\<^sub>1 c\<^sub>1
    using p\<^sub>1.pb1.pullback_diagram_axioms by force

  interpret "11+12": pushout_diagram "interf r\<^sub>1" D\<^sub>1 "lhs r\<^sub>1" G 
                                 "c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1" b\<^sub>1 c\<^sub>1 "c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1"
  proof 
    show \<open>\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> (c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>V v = \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>1\<^esub>\<close> for v
      using that p\<^sub>1.po1.node_commutativity \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v = \<^bsub>m\<^sub>1\<^esub>\<^sub>V v\<close>
        \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close>  p\<^sub>1.r.k.morph_node_range
      by (simp add: morph_comp_def)
  next
    show \<open>\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> (c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>E e = \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>1\<^esub>\<close> for e
      using that p\<^sub>1.po1.edge_commutativity \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e = \<^bsub>m\<^sub>1\<^esub>\<^sub>E e\<close>
        \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>E e = \<^bsub>g\<^sub>1\<^esub>\<^sub>E e\<close>  p\<^sub>1.r.k.morph_edge_range
      by (simp add: morph_comp_def)
  next
    show \<open>Ex1M
        (\<lambda>xa. morphism (to_ngraph G) D' xa \<and>
               (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
               (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and>
               (\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1)\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
               (\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1)\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e))
        (to_ngraph G)\<close> if \<open>graph D'\<close> \<open>morphism (to_ngraph (lhs r\<^sub>1)) D' y\<close> \<open>morphism (to_ngraph D\<^sub>1) D' x\<close>
        
       \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>1\<^esub>\<^sub>V v\<close>
       \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>1\<^esub>\<^sub>E e\<close>
     for D' :: "('g,'h) ngraph" and x y
    proof -

      have \<open>\<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v = \<^bsub>m\<^sub>1\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>1\<^esub>\<close> for v
        using that \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v = \<^bsub>m\<^sub>1\<^esub>\<^sub>V v\<close> 
                   \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e = \<^bsub>m\<^sub>1\<^esub>\<^sub>E e\<close>
        by (simp add: morph_comp_def)

      have \<open>\<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>\<close> for v
        using that \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close> 
        by (simp add: morph_comp_def)
                                                                         
(*  from here: *)

      have a: \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>1\<^esub>\<^sub>V v\<close>
        using \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v = \<^bsub>m\<^sub>1\<^esub>\<^sub>V v\<close>
         \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close> that
        by (simp add: morph_comp_def to_ngraph_def to_nmorph_def) 
      have b: \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>1\<^esub>\<^sub>E e\<close>
        using \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e = \<^bsub>m\<^sub>1\<^esub>\<^sub>E e\<close>   \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>E e = \<^bsub>g\<^sub>1\<^esub>\<^sub>E e\<close>
          that
        by (simp add: morph_comp_def to_ngraph_def to_nmorph_def) 

      obtain u where \<open>morphism (to_ngraph G) D' u\<close>
        and aa1: \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
        and aa2: \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
        using p\<^sub>1.po1.universal_property[OF  \<open>graph D'\<close> \<open>morphism (to_ngraph (lhs r\<^sub>1)) D' y\<close> \<open>morphism (to_ngraph D\<^sub>1) D' x\<close> a b]
        by fast


(* used for technical reasons within the upcoming proof *)
      have n: \<open>morphism (to_ngraph G) D' u \<and>
            (\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
            (\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e)\<close>
            using \<open>morphism (to_ngraph G) D' u\<close> aa1(1) aa1(2) aa2(1) aa2(2) by force


      show ?thesis
      proof (rule_tac x = u in exI, safe)
        show \<open>morphism (to_ngraph G) D' u\<close>
          using \<open>morphism (to_ngraph G) D' u\<close> by assumption
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph D\<^sub>1\<^esub>\<close> for v
          using that \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> 
          by simp
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> if \<open>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>\<close> for e
          using \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> that 
          by simp
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1)\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> if \<open>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>\<close> for v
          using aa1(1)  \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close> that
          by (auto simp add: to_nmorph_def morph_comp_def to_ngraph_def)
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1)\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close> if \<open>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>\<close> for e
          using aa1(2)  \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>E e = \<^bsub>g\<^sub>1\<^esub>\<^sub>E e\<close> that
          by (auto simp add: to_nmorph_def morph_comp_def to_ngraph_def)
      next
        show \<open>\<^bsub>ya\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e\<close>
          if \<open>morphism (to_ngraph G) D' ya\<close>
             \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
             \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1)\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1)\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
             \<open> e \<in> E\<^bsub>to_ngraph G\<^esub>\<close>
           for ya  e
        proof -
          have m:\<open>morphism (to_ngraph G) D' ya \<and>
            (\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
            (\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e)\<close>
            using that
          proof (intro conjI)
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
              using \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close> that
              by (simp add: morph_comp_def to_ngraph_def to_nmorph_def)
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
              using that \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>E e = \<^bsub>g\<^sub>1\<^esub>\<^sub>E e\<close>
              by (simp add: morph_comp_def to_ngraph_def to_nmorph_def)
          qed assumption

          show ?thesis
            using ex_eq[OF p\<^sub>1.po1.universal_property[OF  \<open>graph D'\<close> \<open>morphism (to_ngraph (lhs r\<^sub>1)) D' y\<close> \<open>morphism (to_ngraph D\<^sub>1) D' x\<close> a b], OF n m] that
            by simp
        qed
      next
        show \<open>\<^bsub>ya\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v\<close>
          if \<open>morphism (to_ngraph G) D' ya\<close>
             \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
             \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1)\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1)\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
             \<open>v \<in> V\<^bsub>to_ngraph G\<^esub>\<close>
           for ya v
        proof -
          have m:\<open>morphism (to_ngraph G) D' ya \<and>
            (\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
            (\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e)\<close>
            using that
          proof (intro conjI)
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
              using \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>V v = \<^bsub>g\<^sub>1\<^esub>\<^sub>V v\<close> that
              by (simp add: morph_comp_def to_ngraph_def to_nmorph_def)
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
              using that \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1\<^esub>\<^sub>E e = \<^bsub>g\<^sub>1\<^esub>\<^sub>E e\<close>
              by (simp add: morph_comp_def to_ngraph_def to_nmorph_def)
          qed assumption

          show ?thesis
            using ex_eq[OF p\<^sub>1.po1.universal_property[OF  \<open>graph D'\<close> \<open>morphism (to_ngraph (lhs r\<^sub>1)) D' y\<close> \<open>morphism (to_ngraph D\<^sub>1) D' x\<close> a b], OF n m] that
            by simp
        qed
      qed
    qed
  qed
    

(* show pb is also a pushout *)
   interpret  inj_k: injective_morphism c12.A D\<^sub>1 c12.b
    using  c12.pb.g_inj_imp_b_inj[OF c\<^sub>2.injective_morphism_axioms]
    by assumption

  interpret ink_l: injective_morphism c12.A D\<^sub>2 c12.c
    using pullback_diagram.g_inj_imp_b_inj[OF c12.pb.flip_diagram c\<^sub>1.injective_morphism_axioms]
    by assumption

  have a: \<open>\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v = \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>1\<^esub>\<close> for v
    using that "11+12.node_commutativity"
    by(simp add: morph_comp_def)
  have b: \<open>\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e = \<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>1\<^esub>\<close> for e
    using that "11+12.edge_commutativity"
    by(simp add: morph_comp_def)



 
(* till here (experiment) *)
  interpret pbj1: injective_morphism "interf r\<^sub>1" D\<^sub>1 "c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1"
    using inj_comp_inj
    using "11+12.flip_diagram" c\<^sub>2.injective_morphism_axioms i\<^sub>1.injective_morphism_axioms p\<^sub>1.r.k.injective_morphism_axioms pushout_diagram.b_f_inj_imp_c_inj by blast

  interpret "11+12pb": pullback_diagram "interf r\<^sub>1" D\<^sub>1 "lhs r\<^sub>1" G "c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1" b\<^sub>1 c\<^sub>1 "c\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1"
    using "11+12.pushout_pullback_inj_b"[OF pbj1.injective_morphism_axioms]
    using p\<^sub>1.r.k.injective_morphism_axioms by fastforce


  interpret pb11: pullback_diagram "interf r\<^sub>1" c12.A "lhs r\<^sub>1" D\<^sub>2 j\<^sub>1 b\<^sub>1 c12.c i\<^sub>1
    using pullback_decomposition[OF j\<^sub>1.morphism_axioms _ c12.pb.pullback_diagram_axioms]
    using "11+12pb.pullback_diagram_axioms" \<open>\<And>e. e \<in> E\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e = \<^bsub>i\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1\<^esub>\<^sub>E e\<close> \<open>\<And>v. v \<in> V\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v = \<^bsub>i\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1\<^esub>\<^sub>V v\<close> i\<^sub>1.morphism_axioms by blast


(* CLEANUP HERE *)


(* WITH BRIAN *)
 have jointly_surj_nodes: \<open>(\<exists>v\<in>V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>i\<^sub>1\<^esub>\<^sub>V v = x) \<or> (\<exists>v\<in>V\<^bsub>c12.A\<^esub>. \<^bsub>c12.c\<^esub>\<^sub>V v = x)\<close>
   if \<open>x \<in> V\<^bsub>D\<^sub>2\<^esub>\<close>  for x
   apply (simp add: c12.A_def c12.c_def)
  
   using c\<^sub>2.inj_nodes  "11+12.joint_surjectivity_nodes"[OF  p\<^sub>2.po1.g.morph_node_range[OF \<open>x \<in> V\<^bsub>D\<^sub>2\<^esub>\<close>]]  that i\<^sub>1.morph_node_range
   by (auto simp add: morph_comp_def inj_on_def)
   
 have jointly_surj_nodes: \<open>(\<exists>v\<in>V\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>i\<^sub>1\<^esub>\<^sub>V v = x) \<or> (\<exists>v\<in>V\<^bsub>c12.A\<^esub>. \<^bsub>c12.c\<^esub>\<^sub>V v = x)\<close>
   if \<open>x \<in> V\<^bsub>D\<^sub>2\<^esub>\<close>  for x
   using that c\<^sub>2.inj_nodes p\<^sub>2.po1.g.morph_node_range c12.reduced_chain_condition_nodes
     "11+12.joint_surjectivity_nodes" p\<^sub>1.po1.joint_surjectivity_nodes i\<^sub>1.morph_node_range
   by (auto simp add: morph_comp_def inj_on_def) metis

  have jointly_surj_edges: \<open>(\<exists>e\<in>E\<^bsub>lhs r\<^sub>1\<^esub>. \<^bsub>i\<^sub>1\<^esub>\<^sub>E e = x) \<or> (\<exists>e\<in>E\<^bsub>c12.A\<^esub>. \<^bsub>c12.c\<^esub>\<^sub>E e = x)\<close>
   if \<open>x \<in> E\<^bsub>D\<^sub>2\<^esub>\<close>  for x
   using that c\<^sub>2.inj_edges p\<^sub>2.po1.g.morph_edge_range c12.reduced_chain_condition_edges
     "11+12.joint_surjectivity_edges" p\<^sub>1.po1.joint_surjectivity_edges i\<^sub>1.morph_edge_range
   by (auto simp add: morph_comp_def inj_on_def) metis

  interpret "11": pushout_diagram "interf r\<^sub>1" c12.A "lhs r\<^sub>1" D\<^sub>2
                                                 j\<^sub>1 b\<^sub>1 c12.c i\<^sub>1
    using po_characterization[OF j\<^sub>1.injective_morphism_axioms
          p\<^sub>1.r.k.injective_morphism_axioms
          ink_l.injective_morphism_axioms i\<^sub>1.injective_morphism_axioms
          \<open>\<And>v. v \<in> V\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v = \<^bsub>i\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1\<^esub>\<^sub>V v\<close>
          \<open>\<And>e. e \<in> E\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e = \<^bsub>i\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1\<^esub>\<^sub>E e\<close>
          pb11.reduced_chain_condition_nodes 
          pb11.reduced_chain_condition_edges
          jointly_surj_nodes jointly_surj_edges] by blast
  interpret pushout_diagram c12.A D\<^sub>1 D\<^sub>2 G c12.b c12.c c\<^sub>1 c\<^sub>2
    using pushout_decomposition[OF c12.b.morphism_axioms p\<^sub>2.po1.g.morphism_axioms "11.pushout_diagram_axioms" "11+12.pushout_diagram_axioms"  c12.pb.node_commutativity c12.pb.edge_commutativity]
    by simp

  interpret morphism "interf r\<^sub>2" D\<^sub>2 "c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2"
    using wf_morph_comp[OF j\<^sub>2.morphism_axioms c12.c.morphism_axioms]
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

 

  
  
  interpret "31+32": pushout_diagram "interf r\<^sub>2" D\<^sub>2 "lhs r\<^sub>2" G "c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" b\<^sub>2 c\<^sub>2 "c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2"
  proof
    show \<open>\<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> (c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2 \<circ>\<^sub>\<rightarrow> b\<^sub>2\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>2\<^esub>\<close> for v
      using that p\<^sub>2.po1.node_commutativity p\<^sub>2.r.k.morph_node_range
        \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close> \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>V v = \<^bsub>m\<^sub>2\<^esub>\<^sub>V v\<close> 
      by (simp add: morph_comp_def)
  next
    show \<open>\<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> (c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2 \<circ>\<^sub>\<rightarrow> b\<^sub>2\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>2\<^esub>\<close> for e
      using that p\<^sub>2.po1.edge_commutativity p\<^sub>2.r.k.morph_edge_range
        \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e\<close> \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>E e= \<^bsub>m\<^sub>2\<^esub>\<^sub>E e\<close> 
      by (simp add: morph_comp_def)
  next
    show \<open>Ex1M
        (\<lambda>xa. morphism (to_ngraph G) D' xa \<and>
               (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
               (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e))
        (to_ngraph G)\<close>
      if \<open>graph D'\<close>
       \<open>morphism (to_ngraph D\<^sub>2) D' x\<close>
       \<open>morphism (to_ngraph (lhs r\<^sub>2)) D' y\<close>
       \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>2\<^esub>\<^sub>V v\<close>
       \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph (c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>2\<^esub>\<^sub>E e\<close>
     for D' :: "('g,'h) ngraph" and x y
    proof -

      have \<open>\<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>V v = \<^bsub>m\<^sub>2\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>2\<^esub>\<close> for v
        using that \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>V v = \<^bsub>m\<^sub>2\<^esub>\<^sub>V v\<close> 
        by (simp add: morph_comp_def)

     have \<open>\<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>\<close> for v
        using that \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close> 
        by (simp add: morph_comp_def)

     have a: \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>2\<^esub>\<^sub>V v\<close>
        using \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>V v = \<^bsub>m\<^sub>2\<^esub>\<^sub>V v\<close>
         \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close> that
        by (simp add: morph_comp_def to_ngraph_def to_nmorph_def) 

      have b: \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>2\<^esub>\<^sub>E e\<close>
        using \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>E e = \<^bsub>m\<^sub>2\<^esub>\<^sub>E e\<close>   \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e\<close>
          that
        by (simp add: morph_comp_def to_ngraph_def to_nmorph_def) 

    obtain u where \<open>morphism (to_ngraph G) D' u\<close>
        and aa1: \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
        and aa2: \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
        using p\<^sub>2.po1.universal_property[OF  \<open>graph D'\<close> \<open>morphism (to_ngraph (lhs r\<^sub>2)) D' y\<close> \<open>morphism (to_ngraph D\<^sub>2) D' x\<close> a b]
        by fast

(* used for technical reasons within the upcoming proof *)
      have n: \<open>morphism (to_ngraph G) D' u \<and>
            (\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
            (\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<and> 
            (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e)\<close>
        using \<open>morphism (to_ngraph G) D' u\<close> aa1(1) aa1(2) aa2(1) aa2(2) by force

     show ?thesis
      proof (rule_tac x = u in exI, safe)
        show \<open>morphism (to_ngraph G) D' u\<close>
          using \<open>morphism (to_ngraph G) D' u\<close> by assumption
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph D\<^sub>2\<^esub>\<close> for v
          using that \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> 
          by simp
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> if \<open>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>\<close> for e
          using \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> that 
          by simp
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> if \<open>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>\<close> for v
          using aa1(1)  \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close> that
          by (auto simp add: to_nmorph_def morph_comp_def to_ngraph_def)
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close> if \<open>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>\<close> for e
          using aa1(2)  \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e\<close> that
          by (auto simp add: to_nmorph_def morph_comp_def to_ngraph_def)
      next
        show \<open>\<^bsub>ya\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e\<close>
          if \<open>morphism (to_ngraph G) D' ya\<close>
             \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
             \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
             \<open> e \<in> E\<^bsub>to_ngraph G\<^esub>\<close>
           for ya  e
        proof -
          have m:\<open>morphism (to_ngraph G) D' ya \<and>
            (\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
            (\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e)\<close>
            using that
          proof (intro conjI)
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
              using \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close> that
              by (simp add: morph_comp_def to_ngraph_def to_nmorph_def)
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
              using that \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e\<close>
              by (simp add: morph_comp_def to_ngraph_def to_nmorph_def)
          qed assumption

          show ?thesis
            using ex_eq[OF p\<^sub>2.po1.universal_property[OF  \<open>graph D'\<close> \<open>morphism (to_ngraph (lhs r\<^sub>2)) D' y\<close> \<open>morphism (to_ngraph D\<^sub>2) D' x\<close> a b], OF n m] that
            by simp
        qed
      next
        show \<open>\<^bsub>ya\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v\<close>
          if \<open>morphism (to_ngraph G) D' ya\<close>
             \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
             \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2)\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
             \<open>v \<in> V\<^bsub>to_ngraph G\<^esub>\<close>
           for ya v
        proof -
          have m:\<open>morphism (to_ngraph G) D' ya \<and>
            (\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
            (\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph c\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e)\<close>
            using that
          proof (intro conjI)
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
              using \<open>\<forall>v \<in> V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>V v = \<^bsub>g\<^sub>2\<^esub>\<^sub>V v\<close> that
              by (simp add: morph_comp_def to_ngraph_def to_nmorph_def)
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph (lhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph g\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
              using that \<open>\<forall>e \<in> E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2\<^esub>\<^sub>E e = \<^bsub>g\<^sub>2\<^esub>\<^sub>E e\<close>
              by (simp add: morph_comp_def to_ngraph_def to_nmorph_def)
          qed assumption

          show ?thesis
            using ex_eq[OF p\<^sub>2.po1.universal_property[OF  \<open>graph D'\<close> \<open>morphism (to_ngraph (lhs r\<^sub>2)) D' y\<close> \<open>morphism (to_ngraph D\<^sub>2) D' x\<close> a b], OF n m] that
            by simp
        qed
      qed
    qed
  qed


  have a: \<open>\<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>V v = \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2 \<circ>\<^sub>\<rightarrow> b\<^sub>2\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>2\<^esub>\<close> for v
    using  "31+32.node_commutativity" that
    by (simp add: morph_comp_def)

  have b: \<open>\<^bsub>c\<^sub>2 \<circ>\<^sub>\<rightarrow> c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>E e = \<^bsub>c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2 \<circ>\<^sub>\<rightarrow> b\<^sub>2\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>2\<^esub>\<close> for e
    using  "31+32.edge_commutativity" that
    by (simp add: morph_comp_def)


(* Experimental *)

(* TODO: proof *)
  interpret "31+32pb": pullback_diagram "interf r\<^sub>2" D\<^sub>2 "lhs r\<^sub>2" G "c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" b\<^sub>2 c\<^sub>2 "c\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2"
    using "31+32.flip_diagram" "31+32.pushout_pullback_inj_b" c\<^sub>1.injective_morphism_axioms i\<^sub>2.injective_morphism_axioms inj_comp_inj p\<^sub>2.r.k.injective_morphism_axioms pushout_diagram.b_f_inj_imp_c_inj by blast

(* TODO Proof *)
  interpret pb31: pullback_diagram "interf r\<^sub>2" c12.A "lhs r\<^sub>2" D\<^sub>1 j\<^sub>2 b\<^sub>2 c12.b i\<^sub>2
   using pullback_decomposition[OF _ _ c12.pb.flip_diagram  "31+32pb.pullback_diagram_axioms"]
   using i\<^sub>2.morphism_axioms j2c(1) j2c(2) j\<^sub>2.morphism_axioms by blast

  have jointly_surj_nodes: \<open>(\<exists>v\<in>V\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>i\<^sub>2\<^esub>\<^sub>V v = x) \<or> (\<exists>v\<in>V\<^bsub>c12.A\<^esub>. \<^bsub>c12.b\<^esub>\<^sub>V v = x)\<close>
    if \<open>x \<in> V\<^bsub>D\<^sub>1\<^esub>\<close> for x
    using that c12.reduced_chain_condition_nodes i\<^sub>2.inj_nodes inj_k.inj_nodes 
      p\<^sub>2.po1.joint_surjectivity_nodes "31+32.joint_surjectivity_nodes"
      c\<^sub>1.inj_nodes i\<^sub>2.morph_node_range inj_on_def p\<^sub>1.po1.g.morph_node_range
    apply (auto simp add: morph_comp_def inj_on_def)
    by metis


  have jointly_surj_edges: \<open>(\<exists>e\<in>E\<^bsub>lhs r\<^sub>2\<^esub>. \<^bsub>i\<^sub>2\<^esub>\<^sub>E e = x) \<or> (\<exists>e\<in>E\<^bsub>c12.A\<^esub>. \<^bsub>c12.b\<^esub>\<^sub>E e = x)\<close>
    if \<open>x \<in> E\<^bsub>D\<^sub>1\<^esub>\<close> for x
       using that c12.reduced_chain_condition_edges i\<^sub>2.inj_edges inj_k.inj_edges
      p\<^sub>2.po1.joint_surjectivity_edges "31+32.joint_surjectivity_edges"
      c\<^sub>1.inj_edges i\<^sub>2.morph_edge_range inj_on_def p\<^sub>1.po1.g.morph_edge_range
    apply (auto simp add: morph_comp_def inj_on_def)
    by metis


(* pushout_diagram (interf r\<^sub>2) c12.A (lhs r\<^sub>2) D\<^sub>1 j\<^sub>2 b\<^sub>2 c12.b i\<^sub>2 *)
  interpret "31": pushout_diagram "interf r\<^sub>2" "lhs r\<^sub>2" c12.A D\<^sub>1 b\<^sub>2 j\<^sub>2 i\<^sub>2 c12.b
    using po_characterization[OF j\<^sub>2.injective_morphism_axioms p\<^sub>2.r.k.injective_morphism_axioms
        inj_k.injective_morphism_axioms i\<^sub>2.injective_morphism_axioms
        j2c
        pb31.reduced_chain_condition_nodes pb31.reduced_chain_condition_edges
        jointly_surj_nodes jointly_surj_edges]
    using pushout_diagram.flip_diagram by blast

  interpret "c21": gluing "interf r\<^sub>1" c12.A "rhs r\<^sub>1" j\<^sub>1 b\<^sub>1' ..
  interpret "c41": gluing "interf r\<^sub>2" c12.A "rhs r\<^sub>2" j\<^sub>2 b\<^sub>2' ..
  interpret "c5": gluing c12.A "c41.H" "c21.H" "c41.c" "c21.c" ..

  interpret h1b: morphism c12.A H\<^sub>1 "h\<^sub>1 \<circ>\<^sub>\<rightarrow> c12.b"
    using wf_morph_comp[OF c12.b.morphism_axioms p\<^sub>1.po2.g.morphism_axioms]
    by assumption


(* aaa and bbb belong to s\<^sub>1 *)
  have  aaa: \<open>\<forall>v\<in>V\<^bsub>interf r\<^sub>1\<^esub>. \<^bsub>f\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1'\<^esub>\<^sub>V v = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v\<close>
    using p\<^sub>1.po2.node_commutativity a \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v = \<^bsub>m\<^sub>1\<^esub>\<^sub>V v\<close>
    by (simp add: morph_comp_def) 
    
  have bbb: \<open>\<forall>e\<in>E\<^bsub>interf r\<^sub>1\<^esub>. \<^bsub>f\<^sub>1 \<circ>\<^sub>\<rightarrow>  b\<^sub>1'\<^esub>\<^sub>E e = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e\<close>
    using p\<^sub>1.po2.edge_commutativity b \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e = \<^bsub>m\<^sub>1\<^esub>\<^sub>E e\<close>
    by (simp add: morph_comp_def) 

  obtain s\<^sub>1 where
    \<open>morphism c21.H H\<^sub>1 s\<^sub>1\<close> and
    \<open>\<And>v. v \<in> V\<^bsub>c12.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.c\<^esub>\<^sub>V v = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> c12.b\<^esub>\<^sub>V v\<close>
    \<open>\<And>e. e \<in> E\<^bsub>c12.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.c\<^esub>\<^sub>E e = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> c12.b\<^esub>\<^sub>E e\<close>
(* and (2) = (8) + (11) *)
    \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
    \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
     using c21.po.universal_property_exist_gen[OF p\<^sub>1.po2.f.H.graph_axioms
        p\<^sub>1.po2.f.morphism_axioms
        wf_morph_comp[OF c12.b.morphism_axioms p\<^sub>1.po2.g.morphism_axioms] aaa bbb]
    by auto

  interpret s\<^sub>1: morphism c21.H H\<^sub>1 s\<^sub>1
    using \<open>morphism c21.H H\<^sub>1 s\<^sub>1\<close> by assumption

  interpret morphism "rhs r\<^sub>1" H\<^sub>1 "s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h"
  proof
    show \<open>\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e \<in> E\<^bsub>H\<^sub>1\<^esub>\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>1\<^esub>\<close> for e
      using that \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
        p\<^sub>1.po2.f.morph_edge_range
      by simp
  next
    show \<open>\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V v \<in> V\<^bsub>H\<^sub>1\<^esub>\<close> if \<open>v \<in> V\<^bsub>rhs r\<^sub>1\<^esub>\<close> for v
      using that \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
        p\<^sub>1.po2.f.morph_node_range
      by simp
  next
    show \<open>\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V (s\<^bsub>rhs r\<^sub>1\<^esub> e) = s\<^bsub>H\<^sub>1\<^esub> (\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>1\<^esub>\<close> for e
      using that p\<^sub>1.r.r.H.source_integrity  p\<^sub>1.po2.f.source_preserve
        \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
        \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close> p\<^sub>1.r.r.H.source_integrity 
      by simp
  next
    show \<open>\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V (t\<^bsub>rhs r\<^sub>1\<^esub> e) = t\<^bsub>H\<^sub>1\<^esub> (\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>1\<^esub>\<close> for e
      using that p\<^sub>1.r.r.H.target_integrity  p\<^sub>1.po2.f.target_preserve
        \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
        \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close> p\<^sub>1.r.r.H.target_integrity 
      by simp
  next
    show \<open>l\<^bsub>rhs r\<^sub>1\<^esub> v = l\<^bsub>H\<^sub>1\<^esub> (\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>rhs r\<^sub>1\<^esub>\<close> for v
      using that p\<^sub>1.po2.f.label_preserve
        \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
        \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
      by simp
  next
    show \<open> m\<^bsub>rhs r\<^sub>1\<^esub> e = m\<^bsub>H\<^sub>1\<^esub> (\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>1\<^esub>\<close> for e
      using that p\<^sub>1.po2.f.mark_preserve
        \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
        \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
      by simp
  qed



  interpret "21+22": pushout_diagram "interf r\<^sub>1" "rhs r\<^sub>1" D\<^sub>1 H\<^sub>1 b\<^sub>1' "c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1" \<open>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<close> h\<^sub>1
  proof
    show \<open>\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h \<circ>\<^sub>\<rightarrow> b\<^sub>1'\<^esub>\<^sub>V v = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> (c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>interf r\<^sub>1\<^esub>\<close> for v
      using that aaa
        \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close> p\<^sub>1.r.r.morph_node_range
      by (simp add: morph_comp_def)
  next
    show \<open>\<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h \<circ>\<^sub>\<rightarrow> b\<^sub>1'\<^esub>\<^sub>E e = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> (c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>interf r\<^sub>1\<^esub>\<close> for e
      using that bbb
        \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close> p\<^sub>1.r.r.morph_edge_range
      by (simp add: morph_comp_def)
  next
    show \<open>Ex1M
        (\<lambda>xa. morphism (to_ngraph H\<^sub>1) D' xa \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e))
        (to_ngraph H\<^sub>1)\<close> 
      if  \<open>graph D'\<close>
          \<open>morphism (to_ngraph (rhs r\<^sub>1)) D' x\<close>
          \<open>morphism (to_ngraph D\<^sub>1) D' y\<close>
          \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>1'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>V v\<close>
          \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>1'\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>E e\<close>
        for D' :: "('g,'h) ngraph" and x y
    proof -
      have a: \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>1'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>1\<^esub>\<^sub>V v\<close>
        using \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v = \<^bsub>m\<^sub>1\<^esub>\<^sub>V v\<close> 
          \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>1'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>V v\<close>
        by (simp add: morph_comp_def to_nmorph_def to_ngraph_def)

      have b:\<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>1'\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>1\<^esub>\<^sub>E e\<close>
        using \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e = \<^bsub>m\<^sub>1\<^esub>\<^sub>E e\<close> 
          \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>1)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>1'\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (c12.b \<circ>\<^sub>\<rightarrow> j\<^sub>1)\<^esub>\<^sub>E e\<close>
        by (simp add: morph_comp_def to_nmorph_def to_ngraph_def)
 
      obtain u where \<open>morphism (to_ngraph H\<^sub>1) D' u\<close>
        and u1: \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
        and u2: \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
        using p\<^sub>1.po2.universal_property[OF \<open>graph D'\<close> \<open>morphism (to_ngraph (rhs r\<^sub>1)) D' x\<close>  \<open>morphism (to_ngraph D\<^sub>1) D' y\<close> a b]
        by fast

      have m: \<open>morphism (to_ngraph H\<^sub>1) D' u \<and>
        (\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
        (\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> 
        (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> 
        (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)\<close>
        using u1 u2  \<open>morphism (to_ngraph H\<^sub>1) D' u\<close>
        by fastforce

      show ?thesis
      proof (rule_tac x = u in exI, safe)
        show \<open>morphism (to_ngraph H\<^sub>1) D' u\<close>
          using \<open>morphism (to_ngraph H\<^sub>1) D' u\<close> by assumption
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>\<close> for v
          using that \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
            \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
          by (fastforce simp add: morph_comp_def to_nmorph_def to_ngraph_def)
      next
        show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>\<close> for e
          using that \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
            \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
          by (fastforce simp add: morph_comp_def to_nmorph_def to_ngraph_def)
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
          if \<open>morphism (to_ngraph H\<^sub>1) D' ya\<close>
           \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
           \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
           \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
           \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
           \<open>e \<in> E\<^bsub>to_ngraph H\<^sub>1\<^esub>\<close> for ya e
        proof -
          have n: \<open>morphism (to_ngraph H\<^sub>1) D' ya \<and>
            (\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
            (\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)\<close>
          proof (intro conjI)
            show \<open>morphism (to_ngraph H\<^sub>1) D' ya\<close>
              using \<open> morphism (to_ngraph H\<^sub>1) D' ya\<close> by assumption
          next
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
              using that \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
                \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
              by (fastforce simp add: morph_comp_def to_nmorph_def to_ngraph_def)
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
              using that \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
                \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
              by (fastforce simp add: morph_comp_def to_nmorph_def to_ngraph_def)
          next
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
              using \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> by assumption
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
              using that(5) by assumption
          qed

          show ?thesis
            using that ex_eq[OF p\<^sub>1.po2.universal_property[OF \<open>graph D'\<close> \<open>morphism (to_ngraph (rhs r\<^sub>1)) D' x\<close>  \<open>morphism (to_ngraph D\<^sub>1) D' y\<close> a b] n m]
            by blast
        qed
      next
        show \<open>\<^bsub>ya\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v\<close>
          if \<open>morphism (to_ngraph H\<^sub>1) D' ya\<close>
           \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
           \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
           \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
           \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
           \<open>v \<in> V\<^bsub>to_ngraph H\<^sub>1\<^esub>\<close> for ya v
        proof -
          have n: \<open>morphism (to_ngraph H\<^sub>1) D' ya \<and>
            (\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
            (\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)\<close>
          proof (intro conjI)
            show \<open>morphism (to_ngraph H\<^sub>1) D' ya\<close>
              using \<open> morphism (to_ngraph H\<^sub>1) D' ya\<close> by assumption
          next
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
              using that \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
                \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
              by (fastforce simp add: morph_comp_def to_nmorph_def to_ngraph_def)
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
              using that \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>1)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>1\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
                \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
              by (fastforce simp add: morph_comp_def to_nmorph_def to_ngraph_def)
          next
            show \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
              using \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> by assumption
          next
            show \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>1\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>1\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
              using that(5) by blast
          qed

          show ?thesis
            using that ex_eq[OF p\<^sub>1.po2.universal_property[OF \<open>graph D'\<close> \<open>morphism (to_ngraph (rhs r\<^sub>1)) D' x\<close>  \<open>morphism (to_ngraph D\<^sub>1) D' y\<close> a b] n m]
            by blast
        qed
      qed
    qed
  qed



  interpret "22":  pushout_diagram c12.A D\<^sub>1 c21.H H\<^sub>1 c12.b c21.c h\<^sub>1 s\<^sub>1
    using pushout_decomposition[OF c12.b.morphism_axioms s\<^sub>1.morphism_axioms 
                                   c21.po.flip_diagram "21+22.flip_diagram"]
                                    \<open>\<And>e. e \<in> E\<^bsub>c12.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.c\<^esub>\<^sub>E e = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> c12.b\<^esub>\<^sub>E e\<close> 
                                    \<open>\<And>v. v \<in> V\<^bsub>c12.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.c\<^esub>\<^sub>V v = \<^bsub>h\<^sub>1 \<circ>\<^sub>\<rightarrow> c12.b\<^esub>\<^sub>V v\<close>
    by simp


(* start of s\<^sub>2 *)

  have aaa2: \<open>\<forall>v\<in>V\<^bsub>interf r\<^sub>2\<^esub>. \<^bsub>f\<^sub>2 \<circ>\<^sub>\<rightarrow> b\<^sub>2'\<^esub>\<^sub>V v = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>V v\<close>
    using p\<^sub>2.po2.node_commutativity  \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>V v = \<^bsub>i\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1\<^esub>\<^sub>V v\<close>
      \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>V v = \<^bsub>m\<^sub>2\<^esub>\<^sub>V v\<close> 
    by (simp add: morph_comp_def) 

  have bbb2: \<open>\<forall>e\<in>E\<^bsub>interf r\<^sub>2\<^esub>. \<^bsub>f\<^sub>2 \<circ>\<^sub>\<rightarrow> b\<^sub>2'\<^esub>\<^sub>E e = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>E e\<close>
    using p\<^sub>2.po2.edge_commutativity  \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>1\<^esub>\<^sub>E e = \<^bsub>i\<^sub>1 \<circ>\<^sub>\<rightarrow> b\<^sub>1\<^esub>\<^sub>E e\<close>
      \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>E e = \<^bsub>m\<^sub>2\<^esub>\<^sub>E e\<close> 
    by (simp add: morph_comp_def)


   obtain s\<^sub>2 where
    \<open>morphism c41.H H\<^sub>2 s\<^sub>2\<close> and
    \<open>\<And>v. v \<in> V\<^bsub>c12.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.c\<^esub>\<^sub>V v = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> c12.c\<^esub>\<^sub>V v\<close>
    \<open>\<And>e. e \<in> E\<^bsub>c12.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.c\<^esub>\<^sub>E e = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> c12.c\<^esub>\<^sub>E e\<close>
(* (4) = (9)+(12) *)
    \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close>
    \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close>
     using c41.po.universal_property_exist_gen[OF p\<^sub>2.po2.f.H.graph_axioms
      p\<^sub>2.po2.f.morphism_axioms
      wf_morph_comp[OF c12.c.morphism_axioms p\<^sub>2.po2.g.morphism_axioms] aaa2 bbb2]
    by fast 

  interpret s\<^sub>2: morphism c41.H H\<^sub>2 s\<^sub>2
    using \<open>morphism c41.H H\<^sub>2 s\<^sub>2\<close> by assumption

  interpret morphism "rhs r\<^sub>2" H\<^sub>2 "s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h"
  proof
    show \<open>\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>E e \<in> E\<^bsub>H\<^sub>2\<^esub>\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>2\<^esub>\<close> for e
      using that  \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close> p\<^sub>2.po2.f.morph_edge_range
      by simp
  next
    show \<open>\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>V v \<in> V\<^bsub>H\<^sub>2\<^esub>\<close> if \<open>v \<in> V\<^bsub>rhs r\<^sub>2\<^esub>\<close> for v
      using that \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close> p\<^sub>2.po2.f.morph_node_range 
      by simp
  next
    show \<open>\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>V (s\<^bsub>rhs r\<^sub>2\<^esub> e) = s\<^bsub>H\<^sub>2\<^esub> (\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>2\<^esub>\<close> for e
      using that
        \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close>
        \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close>
        p\<^sub>2.po2.f.source_preserve p\<^sub>2.r.r.H.source_integrity
      by simp
  next
    show \<open>\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>V (t\<^bsub>rhs r\<^sub>2\<^esub> e) = t\<^bsub>H\<^sub>2\<^esub> (\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>2\<^esub>\<close> for e
      using that 
        \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close>
        \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close>
        p\<^sub>2.po2.f.target_preserve p\<^sub>2.r.r.H.target_integrity
      by simp
  next
    show \<open>l\<^bsub>rhs r\<^sub>2\<^esub> v = l\<^bsub>H\<^sub>2\<^esub> (\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>V v)\<close> if \<open>v \<in> V\<^bsub>rhs r\<^sub>2\<^esub>\<close> for v
      using that \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close>
        p\<^sub>2.po2.f.label_preserve
      by simp
  next
    show \<open>m\<^bsub>rhs r\<^sub>2\<^esub> e = m\<^bsub>H\<^sub>2\<^esub> (\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>E e)\<close> if \<open>e \<in> E\<^bsub>rhs r\<^sub>2\<^esub>\<close> for e
      using that \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close>
        p\<^sub>2.po2.f.mark_preserve
      by simp
  qed


  interpret "41+42": pushout_diagram "interf r\<^sub>2" "rhs r\<^sub>2" D\<^sub>2 H\<^sub>2 b\<^sub>2' "c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" "s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h" h\<^sub>2
  proof
    show \<open>\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h \<circ>\<^sub>\<rightarrow> b\<^sub>2'\<^esub>\<^sub>V v = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> (c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>V v\<close>
      if \<open>v \<in> V\<^bsub>interf r\<^sub>2\<^esub>\<close> for v
      using that p\<^sub>2.po2.node_commutativity aaa2  p\<^sub>2.r.r.morph_node_range
        \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close>
      by (simp add: morph_comp_def)
  next
    show \<open>\<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h \<circ>\<^sub>\<rightarrow> b\<^sub>2'\<^esub>\<^sub>E e = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> (c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>E e\<close> 
      if \<open>e \<in> E\<^bsub>interf r\<^sub>2\<^esub>\<close> for e
      using that p\<^sub>2.po2.edge_commutativity bbb2  p\<^sub>2.r.r.morph_edge_range
        \<open>\<And>e. e\<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close>
      by (simp add: morph_comp_def)
  next
    show \<open>Ex1M
        (\<lambda>xa. morphism (to_ngraph H\<^sub>2) D' xa \<and>
               (\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
               (\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>xa \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e))
        (to_ngraph H\<^sub>2)\<close>
      if \<open>graph D'\<close>
       \<open>morphism (to_ngraph (rhs r\<^sub>2)) D' x\<close>
       \<open>morphism (to_ngraph D\<^sub>2) D' y\<close>
       \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>2'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>V v\<close>
       \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>2'\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>E e\<close>
     for D' :: "('g,'h) ngraph" and x y
    proof -

      have a: \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>2'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>2\<^esub>\<^sub>V v\<close>
        using \<open>\<forall>v\<in>V\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>2'\<^esub>\<^sub>V v = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>V v\<close>
            \<open>\<And>v. v\<in>V\<^bsub>interf r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>V v = \<^bsub>m\<^sub>2\<^esub>\<^sub>V v\<close>
          by (simp add: morph_comp_def to_nmorph_def to_ngraph_def)

      have b: \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>2'\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph m\<^sub>2\<^esub>\<^sub>E e\<close>
        using \<open>\<forall>e\<in>E\<^bsub>to_ngraph (interf r\<^sub>2)\<^esub>. \<^bsub>x \<circ>\<^sub>\<rightarrow> to_nmorph b\<^sub>2'\<^esub>\<^sub>E e = \<^bsub>y \<circ>\<^sub>\<rightarrow> to_nmorph (c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2)\<^esub>\<^sub>E e\<close>
            \<open>\<And>e. e\<in>E\<^bsub>interf r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>c12.c \<circ>\<^sub>\<rightarrow> j\<^sub>2\<^esub>\<^sub>E e = \<^bsub>m\<^sub>2\<^esub>\<^sub>E e\<close>
          by (simp add: morph_comp_def to_nmorph_def to_ngraph_def)

        
        
        obtain u where \<open>morphism (to_ngraph H\<^sub>2) D' u\<close>
          and u1: \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> 
          and u2: \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
          using p\<^sub>2.po2.universal_property[OF  \<open>graph D'\<close> \<open>morphism (to_ngraph (rhs r\<^sub>2)) D' x\<close> \<open>morphism (to_ngraph D\<^sub>2) D' y\<close> a b]
          by fast

(* technical reasons *)
        have m: \<open>morphism (to_ngraph H\<^sub>2) D' u \<and>
          (\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and> 
          (\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> 
          (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> 
          (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)\<close>
          using u1 u2 \<open>morphism (to_ngraph H\<^sub>2) D' u\<close>
          by fastforce

        show ?thesis
        proof (rule_tac x = u in exI, safe)
          show \<open>morphism (to_ngraph H\<^sub>2) D' u\<close>
            using \<open>morphism (to_ngraph H\<^sub>2) D' u\<close> by assumption
        next
          show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>\<close> for v
            using that \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
              \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close>
            by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def)
        next
          show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>\<close> for e
            using that \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
              \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close>
            by (auto simp add: morph_comp_def to_nmorph_def to_ngraph_def)
        next
          show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close> if \<open>v \<in> V\<^bsub>to_ngraph D\<^sub>2\<^esub>\<close> for v
            using that \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
            by simp
        next
          show \<open>\<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close> if \<open>e \<in> E\<^bsub>to_ngraph D\<^sub>2\<^esub>\<close> for e
            using that \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
            by simp
        next
          show \<open>\<^bsub>ya\<^esub>\<^sub>E e = \<^bsub>u\<^esub>\<^sub>E e\<close>
            if \<open>morphism (to_ngraph H\<^sub>2) D' ya\<close>
             \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
             \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
             \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
             \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
             \<open>e \<in> E\<^bsub>to_ngraph H\<^sub>2\<^esub>\<close>
           for ya e
          proof -
        
            have n: \<open>morphism (to_ngraph H\<^sub>2) D' ya \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> 
              (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> 
              (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)\<close>
            proof (intro conjI)
              show \<open>morphism (to_ngraph H\<^sub>2) D' ya\<close>
                using \<open>morphism (to_ngraph H\<^sub>2) D' ya\<close>
                by assumption
            next
              show \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
                using \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
                  \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
                  \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close>
                by (simp add: morph_comp_def to_ngraph_def to_nmorph_def)
            next
              show \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
                using \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
                  \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
                  \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close>
                by (simp add: morph_comp_def to_ngraph_def to_nmorph_def)
            next
              show \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
                using \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
                by assumption
            next
              show \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
                using \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
                by assumption
            qed

            show ?thesis
              using that ex_eq[OF p\<^sub>2.po2.universal_property[OF  \<open>graph D'\<close> \<open>morphism (to_ngraph (rhs r\<^sub>2)) D' x\<close> \<open>morphism (to_ngraph D\<^sub>2) D' y\<close> a b] n m]
              by fast
          qed
        next
          show \<open>\<^bsub>ya\<^esub>\<^sub>V v = \<^bsub>u\<^esub>\<^sub>V v\<close>
            if \<open>morphism (to_ngraph H\<^sub>2) D' ya\<close>
             \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
             \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
             \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
             \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
             \<open>v \<in> V\<^bsub>to_ngraph H\<^sub>2\<^esub>\<close>
           for ya v
          proof -
        
            have n: \<open>morphism (to_ngraph H\<^sub>2) D' ya \<and>
              (\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v) \<and>
              (\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e) \<and> 
              (\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v) \<and> 
              (\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e)\<close>
            proof (intro conjI)
              show \<open>morphism (to_ngraph H\<^sub>2) D' ya\<close>
                using \<open>morphism (to_ngraph H\<^sub>2) D' ya\<close>
                by assumption
            next
              show \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
                using \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
                  \<open>\<forall>v\<in>V\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h)\<^esub>\<^sub>V v = \<^bsub>x\<^esub>\<^sub>V v\<close>
                  \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close>
                by (simp add: morph_comp_def to_ngraph_def to_nmorph_def)
            next
              show \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
                using \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>u \<circ>\<^sub>\<rightarrow> to_nmorph f\<^sub>2\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
                  \<open>\<forall>e\<in>E\<^bsub>to_ngraph (rhs r\<^sub>2)\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph (s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h)\<^esub>\<^sub>E e = \<^bsub>x\<^esub>\<^sub>E e\<close>
                  \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close>
                by (simp add: morph_comp_def to_ngraph_def to_nmorph_def)
            next
              show \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
                using \<open>\<forall>v\<in>V\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>V v = \<^bsub>y\<^esub>\<^sub>V v\<close>
                by assumption
            next
              show \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
                using \<open>\<forall>e\<in>E\<^bsub>to_ngraph D\<^sub>2\<^esub>. \<^bsub>ya \<circ>\<^sub>\<rightarrow> to_nmorph h\<^sub>2\<^esub>\<^sub>E e = \<^bsub>y\<^esub>\<^sub>E e\<close>
                by assumption
            qed

            show ?thesis
              using that ex_eq[OF p\<^sub>2.po2.universal_property[OF  \<open>graph D'\<close> \<open>morphism (to_ngraph (rhs r\<^sub>2)) D' x\<close> \<open>morphism (to_ngraph D\<^sub>2) D' y\<close> a b] n m]
              by fast
          qed
        qed
      qed
    qed


  interpret "42": pushout_diagram c12.A D\<^sub>2 c41.H H\<^sub>2 c12.c c41.c h\<^sub>2 s\<^sub>2
   using pushout_decomposition[OF c12.c.morphism_axioms s\<^sub>2.morphism_axioms c41.po.flip_diagram "41+42.flip_diagram"]
      \<open>\<And>e. e \<in> E\<^bsub>c12.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.c\<^esub>\<^sub>E e = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> c12.c\<^esub>\<^sub>E e\<close> \<open>\<And>v. v \<in> V\<^bsub>c12.A\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.c\<^esub>\<^sub>V v = \<^bsub>h\<^sub>2 \<circ>\<^sub>\<rightarrow> c12.c\<^esub>\<^sub>V v\<close>
   by simp

(* one side *)

  interpret "31+22": pushout_diagram "interf r\<^sub>2" c21.H "lhs r\<^sub>2" H\<^sub>1 
                                    "c21.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" b\<^sub>2 s\<^sub>1 "h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2"
    using pushout_composition[OF 
        "31.flip_diagram" "22.flip_diagram" ] by assumption
    interpret "41+5": pushout_diagram "interf r\<^sub>2" c21.H "rhs r\<^sub>2" "c5.H" "c21.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" b\<^sub>2' "c5.h" "c5.c \<circ>\<^sub>\<rightarrow> c41.h"
      using pushout_composition[OF c41.po.flip_diagram c5.po.pushout_diagram_axioms] by assumption

(* flipped ones are needed for the sequential independence *)
    interpret pushout_diagram "interf r\<^sub>2" "lhs r\<^sub>2" c21.H H\<^sub>1 b\<^sub>2 "c21.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" "h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2" s\<^sub>1
      using "31+22.flip_diagram" by assumption

    interpret pushout_diagram "interf r\<^sub>2" "rhs r\<^sub>2" c21.H c5.H b\<^sub>2' "c21.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" "c5.c \<circ>\<^sub>\<rightarrow> c41.h" c5.h
      using "41+5.flip_diagram" by assumption

(* show second direct derivation *)
    interpret injective_morphism "lhs r\<^sub>2" H\<^sub>1 "h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2"
      using inj_comp_inj[OF i\<^sub>2.injective_morphism_axioms h\<^sub>1.injective_morphism_axioms]
      by assumption

    interpret direct_derivation r\<^sub>2  b\<^sub>2 b\<^sub>2' H\<^sub>1 "h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2" c21.H "c21.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" s\<^sub>1 c5.H "c5.c \<circ>\<^sub>\<rightarrow> c41.h" c5.h
      ..

(* first seq. indep. *)
    interpret p3: sequential_independence r\<^sub>1 b\<^sub>1 b\<^sub>1' G g\<^sub>1 D\<^sub>1 m\<^sub>1 c\<^sub>1 H\<^sub>1 f\<^sub>1 h\<^sub>1 r\<^sub>2 b\<^sub>2 b\<^sub>2' "h\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^sub>2" c21.H "c21.c \<circ>\<^sub>\<rightarrow> j\<^sub>2" s\<^sub>1 c5.H "c5.c \<circ>\<^sub>\<rightarrow> c41.h" c5.h
    proof
      show \<open>\<exists>i. morphism (rhs r\<^sub>1) c21.H i \<and>
        (\<forall>v\<in>V\<^bsub>rhs r\<^sub>1\<^esub>. \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>rhs r\<^sub>1\<^esub>. \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e)\<close>
      proof (rule_tac x = c21.h in exI, intro conjI)
        show \<open>morphism (rhs r\<^sub>1) c21.H c21.h\<close>
          using c21.inc_h.morphism_axioms by assumption
      next
        show \<open>\<forall>v\<in>V\<^bsub>rhs r\<^sub>1\<^esub>. \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>
          by (simp add: \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>1\<^esub>\<^sub>V v\<close>)
      next
        show \<open>\<forall>e\<in>E\<^bsub>rhs r\<^sub>1\<^esub>. \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>
          by (simp add: \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>1\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>1 \<circ>\<^sub>\<rightarrow> c21.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>1\<^esub>\<^sub>E e\<close>)
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


    interpret "11+42": pushout_diagram "interf r\<^sub>1" c41.H "lhs r\<^sub>1" H\<^sub>2 "c41.c \<circ>\<^sub>\<rightarrow> j\<^sub>1" b\<^sub>1 s\<^sub>2 "h\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1"
      using pushout_composition[OF "11.pushout_diagram_axioms" "42.flip_diagram" ] by assumption
    
    interpret pushout_diagram "interf r\<^sub>1" "lhs r\<^sub>1" c41.H H\<^sub>2 b\<^sub>1 "c41.c \<circ>\<^sub>\<rightarrow> j\<^sub>1" "h\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1" s\<^sub>2
      using "11+42.flip_diagram" by assumption

    interpret "21+5": pushout_diagram "interf r\<^sub>1" c41.H "rhs r\<^sub>1" c5.H "c41.c \<circ>\<^sub>\<rightarrow> j\<^sub>1" b\<^sub>1' c5.c "c5.h \<circ>\<^sub>\<rightarrow> c21.h"
      using pushout_composition[OF c21.po.flip_diagram c5.po.flip_diagram] by assumption

    
    interpret pushout_diagram "interf r\<^sub>1" "rhs r\<^sub>1" c41.H c5.H b\<^sub>1' "c41.c \<circ>\<^sub>\<rightarrow> j\<^sub>1" "c5.h \<circ>\<^sub>\<rightarrow> c21.h" c5.c
      using "21+5.flip_diagram" by assumption

    interpret injective_morphism "lhs r\<^sub>1" H\<^sub>2 "h\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1"
      using inj_comp_inj[OF i\<^sub>1.injective_morphism_axioms h\<^sub>2.injective_morphism_axioms]
      by assumption

    interpret direct_derivation r\<^sub>1 b\<^sub>1 b\<^sub>1' H\<^sub>2 "h\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1" c41.H "c41.c \<circ>\<^sub>\<rightarrow> j\<^sub>1" s\<^sub>2 c5.H "c5.h \<circ>\<^sub>\<rightarrow> c21.h" c5.c
      ..

    interpret p4: sequential_independence r\<^sub>2 b\<^sub>2 b\<^sub>2' G g\<^sub>2 D\<^sub>2 m\<^sub>2 c\<^sub>2 H\<^sub>2 f\<^sub>2 h\<^sub>2 r\<^sub>1 b\<^sub>1 b\<^sub>1' "h\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^sub>1" c41.H "c41.c \<circ>\<^sub>\<rightarrow> j\<^sub>1" s\<^sub>2 c5.H "c5.h \<circ>\<^sub>\<rightarrow> c21.h" c5.c 
    proof
      show \<open>\<exists>i. morphism (rhs r\<^sub>2) c41.H i \<and>
        (\<forall>v\<in>V\<^bsub>rhs r\<^sub>2\<^esub>. \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v) \<and> (\<forall>e\<in>E\<^bsub>rhs r\<^sub>2\<^esub>. \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> i\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e)\<close>
        using \<open>\<And>e. e \<in> E\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>E e = \<^bsub>f\<^sub>2\<^esub>\<^sub>E e\<close> \<open>\<And>v. v \<in> V\<^bsub>rhs r\<^sub>2\<^esub> \<Longrightarrow> \<^bsub>s\<^sub>2 \<circ>\<^sub>\<rightarrow> c41.h\<^esub>\<^sub>V v = \<^bsub>f\<^sub>2\<^esub>\<^sub>V v\<close> c41.inc_h.morphism_axioms by blast
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