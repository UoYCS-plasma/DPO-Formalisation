theory Pushout
  imports Morphism
begin

section \<open>Pushout Diagram\<close>

text_raw \<open>
\begin{figure}[!htb]
  \centering
  \includestandalone{figs/fig-pushout}
  \caption{Abstract Pushout}
\end{figure}
\<close>

locale pushout_diagram =
  b: morphism V\<^sub>A E\<^sub>A s\<^sub>A s'\<^sub>A t\<^sub>A t'\<^sub>A l\<^sub>A l'\<^sub>A m\<^sub>A m'\<^sub>A V\<^sub>B E\<^sub>B s\<^sub>B s'\<^sub>B t\<^sub>B t'\<^sub>B l\<^sub>B l'\<^sub>B m\<^sub>B m'\<^sub>B b\<^sub>V b'\<^sub>V b\<^sub>E b'\<^sub>E +
  c: morphism V\<^sub>A E\<^sub>A s\<^sub>A s'\<^sub>A t\<^sub>A t'\<^sub>A l\<^sub>A l'\<^sub>A m\<^sub>A m'\<^sub>A V\<^sub>C E\<^sub>C s\<^sub>C s'\<^sub>C t\<^sub>C t'\<^sub>C l\<^sub>C l'\<^sub>C m\<^sub>C m'\<^sub>C c\<^sub>V c'\<^sub>V c\<^sub>E c'\<^sub>E +
  f: morphism V\<^sub>B E\<^sub>B s\<^sub>B s'\<^sub>B t\<^sub>B t'\<^sub>B l\<^sub>B l'\<^sub>B m\<^sub>B m'\<^sub>B V\<^sub>D E\<^sub>D s\<^sub>D s'\<^sub>D t\<^sub>D t'\<^sub>D l\<^sub>D l'\<^sub>D m\<^sub>D m'\<^sub>D f\<^sub>V f'\<^sub>V f\<^sub>E f'\<^sub>E +
  g: morphism V\<^sub>C E\<^sub>C s\<^sub>C s'\<^sub>C t\<^sub>C t'\<^sub>C l\<^sub>C l'\<^sub>C m\<^sub>C m'\<^sub>C V\<^sub>D E\<^sub>D s\<^sub>D s'\<^sub>D t\<^sub>D t'\<^sub>D l\<^sub>D l'\<^sub>D m\<^sub>D m'\<^sub>D g\<^sub>V g'\<^sub>V g\<^sub>E g'\<^sub>E 
  for 
    V\<^sub>A E\<^sub>A s\<^sub>A s'\<^sub>A t\<^sub>A t'\<^sub>A l\<^sub>A l'\<^sub>A m\<^sub>A m'\<^sub>A 
    V\<^sub>B E\<^sub>B s\<^sub>B s'\<^sub>B t\<^sub>B t'\<^sub>B l\<^sub>B l'\<^sub>B m\<^sub>B m'\<^sub>B
    V\<^sub>C E\<^sub>C s\<^sub>C s'\<^sub>C t\<^sub>C t'\<^sub>C l\<^sub>C l'\<^sub>C m\<^sub>C m'\<^sub>C and
    V\<^sub>D :: "'v set" and E\<^sub>D :: "'e set" and s\<^sub>D s'\<^sub>D t\<^sub>D t'\<^sub>D l\<^sub>D l'\<^sub>D m\<^sub>D m'\<^sub>D
    b\<^sub>V b'\<^sub>V b\<^sub>E b'\<^sub>E 
    c\<^sub>V c'\<^sub>V c\<^sub>E c'\<^sub>E
    f\<^sub>V f'\<^sub>V f\<^sub>E f'\<^sub>E 
    g\<^sub>V g'\<^sub>V g\<^sub>E g'\<^sub>E 
    +
  assumes
    node_commutativity: "f\<^sub>V \<circ>\<^sub>m b\<^sub>V = g\<^sub>V \<circ>\<^sub>m c\<^sub>V" and
    edge_commutativity: "f\<^sub>E \<circ>\<^sub>m b\<^sub>E = g\<^sub>E \<circ>\<^sub>m c\<^sub>E" and
    universal_property: 
      "\<lbrakk>graph (V\<^sub>H :: 'v set) (E\<^sub>H :: 'e set) s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H; 
        morphism V\<^sub>B E\<^sub>B s\<^sub>B t\<^sub>B l\<^sub>B m\<^sub>B V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H p\<^sub>V p\<^sub>E;
        morphism V\<^sub>C E\<^sub>C s\<^sub>C t\<^sub>C l\<^sub>C m\<^sub>C V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H t\<^sub>V t\<^sub>E;
        p\<^sub>V \<circ>\<^sub>m b\<^sub>V = t\<^sub>V \<circ>\<^sub>m c\<^sub>V;
        p\<^sub>E \<circ>\<^sub>m b\<^sub>E = t\<^sub>E \<circ>\<^sub>m c\<^sub>E\<rbrakk> 
        \<Longrightarrow> \<exists>! (u\<^sub>V, u\<^sub>E). morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E 
              \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E
              \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E"

begin

(* https://link.springer.com/content/pdf/10.1007/BF00289616.pdf *)
(* lemma
  assumes 
    \<open>pushout_diagram 
          V\<^sub>A E\<^sub>A s\<^sub>A t\<^sub>A l\<^sub>A m\<^sub>A V\<^sub>B E\<^sub>B s\<^sub>B t\<^sub>B l\<^sub>B m\<^sub>B 
          V\<^sub>C E\<^sub>C s\<^sub>C t\<^sub>C l\<^sub>C m\<^sub>C V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' 
          b\<^sub>V b\<^sub>E c\<^sub>V c\<^sub>E p\<^sub>V p\<^sub>E q\<^sub>V q\<^sub>E\<close> and
    c1: \<open>injective_morphism V\<^sub>C E\<^sub>C s\<^sub>C t\<^sub>C l\<^sub>C m\<^sub>C V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D c\<^sub>1\<^sub>V c\<^sub>1\<^sub>E\<close> and
    c2: \<open>injective_morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D c\<^sub>2\<^sub>V c\<^sub>2\<^sub>E\<close> 
  shows \<open>True\<close>
  sorry *)

lemma
  fixes 
    V\<^sub>D\<^sub>' :: "'v set" and
    E\<^sub>D\<^sub>' :: "'e set" 
  assumes 
    D': \<open>graph V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>'\<close> and
    p': \<open>morphism V\<^sub>B E\<^sub>B s\<^sub>B t\<^sub>B l\<^sub>B m\<^sub>B V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' p\<^sub>V p\<^sub>E\<close> and
    d': \<open>morphism V\<^sub>C E\<^sub>C s\<^sub>C t\<^sub>C l\<^sub>C m\<^sub>C V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' q\<^sub>V q\<^sub>E\<close>
  shows \<open>pushout_diagram 
    V\<^sub>A E\<^sub>A s\<^sub>A t\<^sub>A l\<^sub>A m\<^sub>A 
    V\<^sub>B E\<^sub>B s\<^sub>B t\<^sub>B l\<^sub>B m\<^sub>B 
    V\<^sub>C E\<^sub>C s\<^sub>C t\<^sub>C l\<^sub>C m\<^sub>C
    V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' 
    b\<^sub>V b\<^sub>E 
    c\<^sub>V c\<^sub>E 
    p\<^sub>V p\<^sub>E
    q\<^sub>V q\<^sub>E \<longleftrightarrow> (\<exists>u\<^sub>V u\<^sub>E. bijective_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' u\<^sub>V u\<^sub>E 
      \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = q\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = q\<^sub>E 
      \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E)\<close>
proof
\<comment> \<open>only if\<close>
  show \<open>\<exists>u\<^sub>V u\<^sub>E. bijective_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' u\<^sub>V u\<^sub>E 
        \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = q\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = q\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E\<close> 
    if a:\<open>pushout_diagram 
          V\<^sub>A E\<^sub>A s\<^sub>A t\<^sub>A l\<^sub>A m\<^sub>A V\<^sub>B E\<^sub>B s\<^sub>B t\<^sub>B l\<^sub>B m\<^sub>B 
          V\<^sub>C E\<^sub>C s\<^sub>C t\<^sub>C l\<^sub>C m\<^sub>C V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' 
          b\<^sub>V b\<^sub>E c\<^sub>V c\<^sub>E p\<^sub>V p\<^sub>E q\<^sub>V q\<^sub>E\<close>
  proof -
    obtain u\<^sub>V and u\<^sub>E where \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' u\<^sub>V u\<^sub>E\<close>
      and \<open>u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V\<close> and \<open>u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E\<close>
      and \<open>u\<^sub>V \<circ>\<^sub>m g\<^sub>V = q\<^sub>V\<close> and \<open>u\<^sub>E \<circ>\<^sub>m g\<^sub>E = q\<^sub>E\<close>
      using universal_property[of V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' p\<^sub>V p\<^sub>E q\<^sub>V q\<^sub>E]
      by (metis (mono_tags, lifting) D' a case_prod_unfold d' p' pushout_diagram.edge_commutativity pushout_diagram.node_commutativity)

    obtain u'\<^sub>V and u'\<^sub>E 
      where \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D  u'\<^sub>V u'\<^sub>E\<close>
      and \<open>u'\<^sub>V \<circ>\<^sub>m p\<^sub>V = f\<^sub>V\<close> and \<open>u'\<^sub>E \<circ>\<^sub>m p\<^sub>E = f\<^sub>E\<close> 
      and \<open>u'\<^sub>V \<circ>\<^sub>m q\<^sub>V = g\<^sub>V\<close> and \<open>u'\<^sub>E \<circ>\<^sub>m q\<^sub>E = g\<^sub>E\<close>
      using  pushout_diagram.universal_property[of V\<^sub>A E\<^sub>A s\<^sub>A t\<^sub>A l\<^sub>A m\<^sub>A V\<^sub>B E\<^sub>B s\<^sub>B t\<^sub>B l\<^sub>B m\<^sub>B 
          V\<^sub>C E\<^sub>C s\<^sub>C t\<^sub>C l\<^sub>C m\<^sub>C V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' 
          b\<^sub>V b\<^sub>E c\<^sub>V c\<^sub>E p\<^sub>V p\<^sub>E q\<^sub>V q\<^sub>E 
          V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D f\<^sub>V f\<^sub>E g\<^sub>V g\<^sub>E]
      using a edge_commutativity f.H.graph_axioms f.morphism_axioms g.morphism_axioms node_commutativity by auto

    obtain id\<^sub>V and id\<^sub>E where \<open>identity_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E\<close>
      using f.H.graph_axioms id_morphI by blast

    obtain id'\<^sub>V and id'\<^sub>E where \<open>identity_morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' id'\<^sub>V id'\<^sub>E\<close>
      using D' id_morphI by blast


    have \<open>u'\<^sub>V \<circ>\<^sub>m u\<^sub>V \<circ>\<^sub>m f\<^sub>V = f\<^sub>V\<close>
      by (simp add: \<open>u'\<^sub>V \<circ>\<^sub>m p\<^sub>V = f\<^sub>V\<close> \<open>u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V\<close> map_comp_assoc)
    moreover have \<open>u'\<^sub>E \<circ>\<^sub>m u\<^sub>E \<circ>\<^sub>m f\<^sub>E = f\<^sub>E\<close>
      by (simp add: \<open>u'\<^sub>E \<circ>\<^sub>m p\<^sub>E = f\<^sub>E\<close> \<open>u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E\<close> map_comp_assoc)


    moreover have \<open>u'\<^sub>V \<circ>\<^sub>m u\<^sub>V \<circ>\<^sub>m g\<^sub>V = g\<^sub>V\<close>
      by (simp add: \<open>u'\<^sub>V \<circ>\<^sub>m q\<^sub>V = g\<^sub>V\<close> \<open>u\<^sub>V \<circ>\<^sub>m g\<^sub>V = q\<^sub>V\<close> map_comp_assoc)
    moreover have \<open>u'\<^sub>E \<circ>\<^sub>m u\<^sub>E \<circ>\<^sub>m g\<^sub>E = g\<^sub>E\<close>
      by (simp add: \<open>u'\<^sub>E \<circ>\<^sub>m q\<^sub>E = g\<^sub>E\<close> \<open>u\<^sub>E \<circ>\<^sub>m g\<^sub>E = q\<^sub>E\<close> map_comp_assoc)

    moreover have \<open>id\<^sub>V \<circ>\<^sub>m f\<^sub>V = f\<^sub>V\<close>
      using comp_id_morph
      using \<open>identity_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E\<close> b.H.graph_axioms f.morphism_axioms id_morphI by fastforce

    moreover have \<open>id\<^sub>E \<circ>\<^sub>m f\<^sub>E = f\<^sub>E\<close>
      using comp_id_morph
      using \<open>identity_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E\<close> b.H.graph_axioms f.morphism_axioms id_morphI by fastforce
     

    moreover have \<open>id\<^sub>V \<circ>\<^sub>m g\<^sub>V = g\<^sub>V\<close>
      using comp_id_morph
      using \<open>identity_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E\<close> c.H.graph_axioms g.morphism_axioms id_morphI by fastforce
    moreover have \<open>id\<^sub>E \<circ>\<^sub>m g\<^sub>E = g\<^sub>E\<close>
      using comp_id_morph
      using \<open>identity_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E\<close> c.H.graph_axioms g.morphism_axioms id_morphI by fastforce

    moreover have \<open>u'\<^sub>V \<circ>\<^sub>m u\<^sub>V = id\<^sub>V\<close>
    proof -
      have \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D (u'\<^sub>V \<circ>\<^sub>m u\<^sub>V) (u'\<^sub>E \<circ>\<^sub>m u\<^sub>E) \<and>
         u'\<^sub>V \<circ>\<^sub>m u\<^sub>V \<circ>\<^sub>m f\<^sub>V = f\<^sub>V \<and> u'\<^sub>E \<circ>\<^sub>m u\<^sub>E \<circ>\<^sub>m f\<^sub>E = f\<^sub>E \<and> u'\<^sub>V \<circ>\<^sub>m u\<^sub>V \<circ>\<^sub>m g\<^sub>V = g\<^sub>V \<and> u'\<^sub>E\<circ>\<^sub>m u\<^sub>E\<circ>\<^sub>m g\<^sub>E = g\<^sub>E\<close>
        by (meson \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' u\<^sub>V u\<^sub>E\<close> \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D u'\<^sub>V u'\<^sub>E\<close> calculation(1) calculation(2) calculation(3) calculation(4) morph_composition)

      moreover have \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E \<and>
         id\<^sub>V \<circ>\<^sub>m f\<^sub>V = f\<^sub>V \<and> id\<^sub>E \<circ>\<^sub>m f\<^sub>E = f\<^sub>E \<and> id\<^sub>V \<circ>\<^sub>m g\<^sub>V = g\<^sub>V \<and> id\<^sub>E \<circ>\<^sub>m g\<^sub>E = g\<^sub>E\<close>
        using \<open>identity_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E\<close>
        unfolding identity_morphism_def bijective_morphism_def injective_morphism_def
        using \<open>id\<^sub>E \<circ>\<^sub>m f\<^sub>E = f\<^sub>E\<close> \<open>id\<^sub>E \<circ>\<^sub>m g\<^sub>E = g\<^sub>E\<close> \<open>id\<^sub>V \<circ>\<^sub>m f\<^sub>V = f\<^sub>V\<close> \<open>id\<^sub>V \<circ>\<^sub>m g\<^sub>V = g\<^sub>V\<close> by fastforce

      ultimately show ?thesis
        using universal_property[of V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D f\<^sub>V f\<^sub>E g\<^sub>V g\<^sub>E]
        using ex_eq[of \<open>\<lambda>u. morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D (fst u) (snd u) \<and>
             (fst u) \<circ>\<^sub>m f\<^sub>V = f\<^sub>V \<and> (snd u) \<circ>\<^sub>m f\<^sub>E = f\<^sub>E \<and> (fst u) \<circ>\<^sub>m g\<^sub>V = g\<^sub>V \<and> (snd u) \<circ>\<^sub>m g\<^sub>E = g\<^sub>E\<close>
            \<open>(u'\<^sub>V \<circ>\<^sub>m u\<^sub>V , u'\<^sub>E \<circ>\<^sub>m u\<^sub>E )\<close>
            \<open>(id\<^sub>V, id\<^sub>E)\<close>]
        using edge_commutativity f.H.graph_axioms f.morphism_axioms g.morphism_axioms node_commutativity by auto
    qed

    moreover have \<open>u'\<^sub>E \<circ>\<^sub>m u\<^sub>E = id\<^sub>E\<close>
    proof -
      have \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D (u'\<^sub>V \<circ>\<^sub>m u\<^sub>V) (u'\<^sub>E \<circ>\<^sub>m u\<^sub>E) \<and>
         u'\<^sub>V \<circ>\<^sub>m u\<^sub>V \<circ>\<^sub>m f\<^sub>V = f\<^sub>V \<and> u'\<^sub>E \<circ>\<^sub>m u\<^sub>E \<circ>\<^sub>m f\<^sub>E = f\<^sub>E \<and> u'\<^sub>V \<circ>\<^sub>m u\<^sub>V \<circ>\<^sub>m g\<^sub>V = g\<^sub>V \<and> u'\<^sub>E\<circ>\<^sub>m u\<^sub>E\<circ>\<^sub>m g\<^sub>E = g\<^sub>E\<close>
        by (meson \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' u\<^sub>V u\<^sub>E\<close> \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D u'\<^sub>V u'\<^sub>E\<close> calculation(1) calculation(2) calculation(3) calculation(4) morph_composition)

      moreover have \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E \<and>
         id\<^sub>V \<circ>\<^sub>m f\<^sub>V = f\<^sub>V \<and> id\<^sub>E \<circ>\<^sub>m f\<^sub>E = f\<^sub>E \<and> id\<^sub>V \<circ>\<^sub>m g\<^sub>V = g\<^sub>V \<and> id\<^sub>E \<circ>\<^sub>m g\<^sub>E = g\<^sub>E\<close>
        using \<open>identity_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E\<close>
        unfolding identity_morphism_def bijective_morphism_def injective_morphism_def
        using \<open>id\<^sub>E \<circ>\<^sub>m f\<^sub>E = f\<^sub>E\<close> \<open>id\<^sub>E \<circ>\<^sub>m g\<^sub>E = g\<^sub>E\<close> \<open>id\<^sub>V \<circ>\<^sub>m f\<^sub>V = f\<^sub>V\<close> \<open>id\<^sub>V \<circ>\<^sub>m g\<^sub>V = g\<^sub>V\<close> by fastforce

      ultimately show ?thesis
        using universal_property[of V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D f\<^sub>V f\<^sub>E g\<^sub>V g\<^sub>E]
        using ex_eq[of \<open>\<lambda>u. morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D (fst u) (snd u) \<and>
             (fst u) \<circ>\<^sub>m f\<^sub>V = f\<^sub>V \<and> (snd u) \<circ>\<^sub>m f\<^sub>E = f\<^sub>E \<and> (fst u) \<circ>\<^sub>m g\<^sub>V = g\<^sub>V \<and> (snd u) \<circ>\<^sub>m g\<^sub>E = g\<^sub>E\<close>
            \<open>(u'\<^sub>V \<circ>\<^sub>m u\<^sub>V , u'\<^sub>E \<circ>\<^sub>m u\<^sub>E )\<close>
            \<open>(id\<^sub>V, id\<^sub>E)\<close>]
        using edge_commutativity f.H.graph_axioms f.morphism_axioms g.morphism_axioms node_commutativity by auto
    qed

    moreover have \<open>u\<^sub>V \<circ>\<^sub>m u'\<^sub>V \<circ>\<^sub>m p\<^sub>V = p\<^sub>V\<close>
      by (simp add: \<open>u'\<^sub>V \<circ>\<^sub>m p\<^sub>V = f\<^sub>V\<close> \<open>u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V\<close> map_comp_assoc)
    moreover have \<open>u\<^sub>E \<circ>\<^sub>m u'\<^sub>E \<circ>\<^sub>m p\<^sub>E = p\<^sub>E\<close>
      by (simp add: \<open>u'\<^sub>E \<circ>\<^sub>m p\<^sub>E = f\<^sub>E\<close> \<open>u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E\<close> map_comp_assoc)


    moreover have \<open>u\<^sub>V \<circ>\<^sub>m u'\<^sub>V \<circ>\<^sub>m q\<^sub>V = q\<^sub>V\<close>
      by (simp add: \<open>u'\<^sub>V \<circ>\<^sub>m q\<^sub>V = g\<^sub>V\<close> \<open>u\<^sub>V \<circ>\<^sub>m g\<^sub>V = q\<^sub>V\<close> map_comp_assoc)
    moreover have \<open>u\<^sub>E \<circ>\<^sub>m u'\<^sub>E \<circ>\<^sub>m q\<^sub>E = q\<^sub>E\<close>
      by (simp add: \<open>u'\<^sub>E \<circ>\<^sub>m q\<^sub>E = g\<^sub>E\<close> \<open>u\<^sub>E \<circ>\<^sub>m g\<^sub>E = q\<^sub>E\<close> map_comp_assoc)

    moreover have \<open>u\<^sub>V \<circ>\<^sub>m u'\<^sub>V = id'\<^sub>V\<close>
   proof -
      have \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' (u\<^sub>V \<circ>\<^sub>m u'\<^sub>V) (u\<^sub>E \<circ>\<^sub>m u'\<^sub>E) \<and>
         u\<^sub>V \<circ>\<^sub>m u'\<^sub>V \<circ>\<^sub>m p\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m u'\<^sub>E \<circ>\<^sub>m p\<^sub>E = p\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m u'\<^sub>V \<circ>\<^sub>m q\<^sub>V = q\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m u'\<^sub>E \<circ>\<^sub>m q\<^sub>E = q\<^sub>E\<close>
        by (meson \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' u\<^sub>V u\<^sub>E\<close> \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D u'\<^sub>V u'\<^sub>E\<close> calculation(11) calculation(12) calculation(13) calculation(14) morph_composition)

      moreover have \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' id'\<^sub>V id'\<^sub>E \<and>
         id'\<^sub>V \<circ>\<^sub>m p\<^sub>V = p\<^sub>V \<and> id'\<^sub>E \<circ>\<^sub>m p\<^sub>E = p\<^sub>E \<and> id'\<^sub>V \<circ>\<^sub>m q\<^sub>V = q\<^sub>V \<and> id'\<^sub>E \<circ>\<^sub>m q\<^sub>E = q\<^sub>E\<close>
        using \<open>identity_morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' id'\<^sub>V id'\<^sub>E\<close>
        unfolding identity_morphism_def bijective_morphism_def injective_morphism_def
        by (metis (no_types, lifting) \<open>identity_morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' id'\<^sub>V id'\<^sub>E\<close> b.H.graph_axioms c.H.graph_axioms comp_id_morph(3) comp_id_morph(4) d' id_morphI p')

      ultimately show ?thesis
        using 
          universal_property[of V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' f\<^sub>V f\<^sub>E g\<^sub>V g\<^sub>E] D'
          ex_eq[of \<open>\<lambda>u. morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' (fst u) (snd u) \<and>
             (fst u) \<circ>\<^sub>m f\<^sub>V = f\<^sub>V \<and> (snd u) \<circ>\<^sub>m f\<^sub>E = f\<^sub>E \<and> (fst u) \<circ>\<^sub>m g\<^sub>V = g\<^sub>V \<and> (snd u) \<circ>\<^sub>m g\<^sub>E = g\<^sub>E\<close>
            \<open>(u\<^sub>V \<circ>\<^sub>m u'\<^sub>V , u\<^sub>E \<circ>\<^sub>m u'\<^sub>E )\<close>
            \<open>(id'\<^sub>V, id'\<^sub>E)\<close>]
          a
        unfolding pushout_diagram_def pushout_diagram_axioms_def
        by blast
    qed

    moreover have \<open>u\<^sub>E \<circ>\<^sub>m u'\<^sub>E = id'\<^sub>E\<close>
       proof -
      have \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' (u\<^sub>V \<circ>\<^sub>m u'\<^sub>V) (u\<^sub>E \<circ>\<^sub>m u'\<^sub>E) \<and>
         u\<^sub>V \<circ>\<^sub>m u'\<^sub>V \<circ>\<^sub>m p\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m u'\<^sub>E \<circ>\<^sub>m p\<^sub>E = p\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m u'\<^sub>V \<circ>\<^sub>m q\<^sub>V = q\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m u'\<^sub>E \<circ>\<^sub>m q\<^sub>E = q\<^sub>E\<close>
        by (meson \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' u\<^sub>V u\<^sub>E\<close> \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D u'\<^sub>V u'\<^sub>E\<close> calculation(11) calculation(12) calculation(13) calculation(14) morph_composition)

      moreover have \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' id'\<^sub>V id'\<^sub>E \<and>
         id'\<^sub>V \<circ>\<^sub>m p\<^sub>V = p\<^sub>V \<and> id'\<^sub>E \<circ>\<^sub>m p\<^sub>E = p\<^sub>E \<and> id'\<^sub>V \<circ>\<^sub>m q\<^sub>V = q\<^sub>V \<and> id'\<^sub>E \<circ>\<^sub>m q\<^sub>E = q\<^sub>E\<close>
        using \<open>identity_morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' id'\<^sub>V id'\<^sub>E\<close>
        unfolding identity_morphism_def bijective_morphism_def injective_morphism_def
        by (metis (no_types, lifting) \<open>identity_morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' id'\<^sub>V id'\<^sub>E\<close> b.H.graph_axioms c.H.graph_axioms comp_id_morph(3) comp_id_morph(4) d' id_morphI p')

      ultimately show ?thesis
        using 
          universal_property[of V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' f\<^sub>V f\<^sub>E g\<^sub>V g\<^sub>E] D'
          ex_eq[of \<open>\<lambda>u. morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' (fst u) (snd u) \<and>
             (fst u) \<circ>\<^sub>m f\<^sub>V = f\<^sub>V \<and> (snd u) \<circ>\<^sub>m f\<^sub>E = f\<^sub>E \<and> (fst u) \<circ>\<^sub>m g\<^sub>V = g\<^sub>V \<and> (snd u) \<circ>\<^sub>m g\<^sub>E = g\<^sub>E\<close>
            \<open>(u\<^sub>V \<circ>\<^sub>m u'\<^sub>V , u\<^sub>E \<circ>\<^sub>m u'\<^sub>E )\<close>
            \<open>(id'\<^sub>V, id'\<^sub>E)\<close>]
          a
        unfolding pushout_diagram_def pushout_diagram_axioms_def
        by blast
    qed
    ultimately show ?thesis
      by (metis \<open>identity_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E\<close> \<open>identity_morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' id'\<^sub>V id'\<^sub>E\<close> \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' u\<^sub>V u\<^sub>E\<close> \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D u'\<^sub>V u'\<^sub>E\<close> \<open>u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E\<close> \<open>u\<^sub>E \<circ>\<^sub>m g\<^sub>E = q\<^sub>E\<close> \<open>u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V\<close> \<open>u\<^sub>V \<circ>\<^sub>m g\<^sub>V = q\<^sub>V\<close> bij_morphism_comp_idL)

  qed
next
\<comment> \<open>if\<close>
  show \<open>pushout_diagram V\<^sub>A E\<^sub>A s\<^sub>A t\<^sub>A l\<^sub>A m\<^sub>A V\<^sub>B E\<^sub>B s\<^sub>B t\<^sub>B l\<^sub>B m\<^sub>B V\<^sub>C E\<^sub>C s\<^sub>C t\<^sub>C l\<^sub>C m\<^sub>C V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>'
     l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' b\<^sub>V b\<^sub>E c\<^sub>V c\<^sub>E p\<^sub>V p\<^sub>E q\<^sub>V q\<^sub>E\<close>
    if \<open>\<exists>u\<^sub>V u\<^sub>E. bijective_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' u\<^sub>V u\<^sub>E 
          \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = q\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = q\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E\<close>
  proof (intro_locales)
    show \<open>graph V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>'\<close>
      by (simp add: D')
  next
    show \<open>morphism_axioms V\<^sub>B E\<^sub>B s\<^sub>B t\<^sub>B l\<^sub>B m\<^sub>B V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' p\<^sub>V p\<^sub>E\<close>
      by (simp add: morphism.axioms(3) p')
  next
    show \<open>morphism_axioms V\<^sub>C E\<^sub>C s\<^sub>C t\<^sub>C l\<^sub>C m\<^sub>C V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' q\<^sub>V q\<^sub>E\<close>
      by (simp add: d' morphism.axioms(3))
  next
    show \<open>pushout_diagram_axioms V\<^sub>B E\<^sub>B s\<^sub>B t\<^sub>B l\<^sub>B m\<^sub>B V\<^sub>C E\<^sub>C s\<^sub>C t\<^sub>C l\<^sub>C m\<^sub>C V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' b\<^sub>V b\<^sub>E c\<^sub>V c\<^sub>E p\<^sub>V p\<^sub>E q\<^sub>V q\<^sub>E\<close>
    proof
      show \<open>p\<^sub>V \<circ>\<^sub>m b\<^sub>V = q\<^sub>V \<circ>\<^sub>m c\<^sub>V\<close>
      proof 
       obtain u where ex:\<open>bijective_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' (fst u) (snd u)
                  \<and> (fst u) \<circ>\<^sub>m g\<^sub>V = q\<^sub>V \<and> (snd u) \<circ>\<^sub>m g\<^sub>E = q\<^sub>E \<and> (fst u) \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> (snd u) \<circ>\<^sub>m f\<^sub>E = p\<^sub>E\<close>
          using \<open>\<exists>u\<^sub>V u\<^sub>E. bijective_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' u\<^sub>V u\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = q\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = q\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E\<close> by force

       show \<open>(p\<^sub>V \<circ>\<^sub>m b\<^sub>V) x = (q\<^sub>V \<circ>\<^sub>m c\<^sub>V) x\<close> for x
       proof -
          have \<open>(p\<^sub>V \<circ>\<^sub>m b\<^sub>V) x = ((fst u) \<circ>\<^sub>m f\<^sub>V \<circ>\<^sub>m b\<^sub>V) x\<close>
            using ex by fastforce

          also have \<open>\<dots> = ((fst u) \<circ>\<^sub>m g\<^sub>V \<circ>\<^sub>m c\<^sub>V) x\<close>
            by (simp add: map_comp_assoc node_commutativity)

          also have \<open>\<dots> = (q\<^sub>V \<circ>\<^sub>m c\<^sub>V) x\<close>
            using ex by force

          finally show ?thesis .
        qed      
      qed
    next
      show \<open>p\<^sub>E \<circ>\<^sub>m b\<^sub>E = q\<^sub>E \<circ>\<^sub>m c\<^sub>E\<close>
      proof
        show \<open>(p\<^sub>E \<circ>\<^sub>m b\<^sub>E) x = (q\<^sub>E \<circ>\<^sub>m c\<^sub>E) x\<close> for x
        proof -
          obtain u where ex:\<open>bijective_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' (fst u) (snd u)
            \<and> (fst u) \<circ>\<^sub>m g\<^sub>V = q\<^sub>V \<and> (snd u) \<circ>\<^sub>m g\<^sub>E = q\<^sub>E \<and> (fst u) \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> (snd u) \<circ>\<^sub>m f\<^sub>E = p\<^sub>E\<close>
            using \<open>\<exists>u\<^sub>V u\<^sub>E. bijective_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' u\<^sub>V u\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = q\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = q\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E\<close> by force

          show \<open>(p\<^sub>E \<circ>\<^sub>m b\<^sub>E) x = (q\<^sub>E \<circ>\<^sub>m c\<^sub>E) x\<close> for x
          proof -
            have \<open>(p\<^sub>E \<circ>\<^sub>m b\<^sub>E) x = ((snd u) \<circ>\<^sub>m f\<^sub>E \<circ>\<^sub>m b\<^sub>E) x\<close>
              using ex by fastforce

            also have \<open>\<dots> = ((snd u) \<circ>\<^sub>m g\<^sub>E \<circ>\<^sub>m c\<^sub>E) x\<close>
              by (simp add: map_comp_assoc edge_commutativity)

            also have \<open>\<dots> = (q\<^sub>E \<circ>\<^sub>m c\<^sub>E) x\<close>
              using ex by force

            finally show ?thesis .
          qed      
        qed
      qed
    next 
      show \<open>\<exists>!(u\<^sub>V, u\<^sub>E).
              morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and>
              u\<^sub>V \<circ>\<^sub>m p\<^sub>V = p\<^sub>V' \<and> u\<^sub>E \<circ>\<^sub>m p\<^sub>E = p\<^sub>E' \<and> u\<^sub>V \<circ>\<^sub>m q\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m q\<^sub>E = t\<^sub>E\<close>
        if 
          \<open>graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H\<close> and 
          \<open>morphism V\<^sub>B E\<^sub>B s\<^sub>B t\<^sub>B l\<^sub>B m\<^sub>B V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H p\<^sub>V' p\<^sub>E'\<close> and
          \<open>morphism V\<^sub>C E\<^sub>C s\<^sub>C t\<^sub>C l\<^sub>C m\<^sub>C V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H t\<^sub>V t\<^sub>E\<close> and
          \<open>p\<^sub>V' \<circ>\<^sub>m b\<^sub>V = t\<^sub>V \<circ>\<^sub>m c\<^sub>V\<close> and
          \<open>p\<^sub>E' \<circ>\<^sub>m b\<^sub>E = t\<^sub>E \<circ>\<^sub>m c\<^sub>E\<close>
        for V\<^sub>H :: "'v set" and E\<^sub>H :: "'e set" and s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H p\<^sub>V' p\<^sub>E' t\<^sub>V t\<^sub>E
      proof -
        obtain u''\<^sub>V and u''\<^sub>E where \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u''\<^sub>V u''\<^sub>E
            \<and> u''\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V' \<and> u''\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E' \<and> u''\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u''\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close>
          by (smt (verit, ccfv_SIG) \<open>graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H\<close> \<open>morphism V\<^sub>B E\<^sub>B s\<^sub>B t\<^sub>B l\<^sub>B m\<^sub>B V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H p\<^sub>V' p\<^sub>E'\<close> \<open>morphism V\<^sub>C E\<^sub>C s\<^sub>C t\<^sub>C l\<^sub>C m\<^sub>C V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H t\<^sub>V t\<^sub>E\<close> \<open>p\<^sub>E' \<circ>\<^sub>m b\<^sub>E = t\<^sub>E \<circ>\<^sub>m c\<^sub>E\<close> \<open>p\<^sub>V' \<circ>\<^sub>m b\<^sub>V = t\<^sub>V \<circ>\<^sub>m c\<^sub>V\<close> case_prod_unfold universal_property)

        obtain id\<^sub>V and id\<^sub>E where \<open>identity_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E\<close>
          using f.H.graph_axioms id_morphI by blast

        obtain id'\<^sub>V and id'\<^sub>E where \<open>identity_morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' id'\<^sub>V id'\<^sub>E\<close>
          using D' id_morphI by blast



        obtain u\<^sub>V and u\<^sub>E where ex:\<open>bijective_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' u\<^sub>V u\<^sub>E
                  \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = q\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = q\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E\<close>
          using \<open>\<exists>u\<^sub>V u\<^sub>E. bijective_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' u\<^sub>V u\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m g\<^sub>V = q\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m g\<^sub>E = q\<^sub>E \<and> u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E\<close> by force

        obtain u'\<^sub>V and u'\<^sub>E where \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D u'\<^sub>V u'\<^sub>E 
          \<and> u'\<^sub>V \<circ>\<^sub>m u\<^sub>V = id\<^sub>V
          \<and> u\<^sub>V \<circ>\<^sub>m u'\<^sub>V = id'\<^sub>V
          \<and> u'\<^sub>E \<circ>\<^sub>m u\<^sub>E = id\<^sub>E
          \<and> u\<^sub>E \<circ>\<^sub>m u'\<^sub>E = id'\<^sub>E\<close>
          by (meson \<open>identity_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E\<close> \<open>identity_morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' id'\<^sub>V id'\<^sub>E\<close> bij_impl_inv_l bijective_morphism.axioms(1) ex injective_morphism_def)


\<comment> \<open>part i\<close>
        have \<open>u'\<^sub>V \<circ>\<^sub>m p\<^sub>V = u'\<^sub>V \<circ>\<^sub>m (u\<^sub>V \<circ>\<^sub>m f\<^sub>V)\<close>
          using ex map_comp_assoc by blast
        moreover have \<open>\<dots> = id\<^sub>V \<circ>\<^sub>m f\<^sub>V\<close>
          using calculation ex map_comp_assoc 
          by (metis \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D u'\<^sub>V u'\<^sub>E \<and> u'\<^sub>V \<circ>\<^sub>m u\<^sub>V = id\<^sub>V \<and> u\<^sub>V \<circ>\<^sub>m u'\<^sub>V = id'\<^sub>V \<and> u'\<^sub>E \<circ>\<^sub>m u\<^sub>E = id\<^sub>E \<and> u\<^sub>E \<circ>\<^sub>m u'\<^sub>E = id'\<^sub>E\<close>)
        moreover have \<open>\<dots> = f\<^sub>V\<close>
          using \<open>identity_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E\<close> b.H.graph_axioms comp_id_morph(3) f.morphism_axioms id_morphI by fastforce

        have \<open>u'\<^sub>E \<circ>\<^sub>m p\<^sub>E = u'\<^sub>E \<circ>\<^sub>m (u\<^sub>E \<circ>\<^sub>m f\<^sub>E)\<close>
          using ex map_comp_assoc by blast
        moreover have \<open>\<dots> = id\<^sub>E \<circ>\<^sub>m f\<^sub>E\<close>
          using calculation ex map_comp_assoc 
          by (metis \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D u'\<^sub>V u'\<^sub>E \<and> u'\<^sub>V \<circ>\<^sub>m u\<^sub>V = id\<^sub>V \<and> u\<^sub>V \<circ>\<^sub>m u'\<^sub>V = id'\<^sub>V \<and> u'\<^sub>E \<circ>\<^sub>m u\<^sub>E = id\<^sub>E \<and> u\<^sub>E \<circ>\<^sub>m u'\<^sub>E = id'\<^sub>E\<close>)
        moreover have \<open>\<dots> = f\<^sub>E\<close>
          using \<open>identity_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E\<close> b.H.graph_axioms comp_id_morph(4) f.morphism_axioms id_morphI by fastforce

\<comment> \<open>part ii\<close>
        moreover have \<open>u'\<^sub>V \<circ>\<^sub>m q\<^sub>V = u'\<^sub>V \<circ>\<^sub>m (u\<^sub>V \<circ>\<^sub>m g\<^sub>V)\<close>
          using ex map_comp_assoc by blast
        moreover have \<open>\<dots> = id\<^sub>V \<circ>\<^sub>m g\<^sub>V\<close>
          using calculation ex map_comp_assoc
          by (metis \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D u'\<^sub>V u'\<^sub>E \<and> u'\<^sub>V \<circ>\<^sub>m u\<^sub>V = id\<^sub>V \<and> u\<^sub>V \<circ>\<^sub>m u'\<^sub>V = id'\<^sub>V \<and> u'\<^sub>E \<circ>\<^sub>m u\<^sub>E = id\<^sub>E \<and> u\<^sub>E \<circ>\<^sub>m u'\<^sub>E = id'\<^sub>E\<close>)
        moreover have \<open>\<dots> = g\<^sub>V\<close>
          using \<open>identity_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E\<close> c.H.graph_axioms comp_id_morph(3) g.morphism_axioms id_morphI by fastforce

        moreover have \<open>u'\<^sub>E \<circ>\<^sub>m q\<^sub>E = u'\<^sub>E \<circ>\<^sub>m (u\<^sub>E \<circ>\<^sub>m g\<^sub>E)\<close>
          using ex map_comp_assoc by blast
        moreover have \<open>\<dots> = id\<^sub>E \<circ>\<^sub>m g\<^sub>E\<close>
          using calculation ex map_comp_assoc
          by (metis \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D u'\<^sub>V u'\<^sub>E \<and> u'\<^sub>V \<circ>\<^sub>m u\<^sub>V = id\<^sub>V \<and> u\<^sub>V \<circ>\<^sub>m u'\<^sub>V = id'\<^sub>V \<and> u'\<^sub>E \<circ>\<^sub>m u\<^sub>E = id\<^sub>E \<and> u\<^sub>E \<circ>\<^sub>m u'\<^sub>E = id'\<^sub>E\<close>)
        moreover have \<open>\<dots> = g\<^sub>E\<close>
          using \<open>identity_morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D id\<^sub>V id\<^sub>E\<close> c.H.graph_axioms comp_id_morph(4) g.morphism_axioms id_morphI by fastforce


        ultimately show ?thesis
        proof -
          let ?u'''\<^sub>V = \<open>u''\<^sub>V \<circ>\<^sub>m u'\<^sub>V\<close> and ?u'''\<^sub>E = \<open>u''\<^sub>E \<circ>\<^sub>m u'\<^sub>E\<close>

          have \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H ?u'''\<^sub>V ?u'''\<^sub>E\<close>
            by (meson \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u''\<^sub>V u''\<^sub>E \<and> u''\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V' \<and> u''\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E' \<and> u''\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u''\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close> \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D u'\<^sub>V u'\<^sub>E \<and> u'\<^sub>V \<circ>\<^sub>m u\<^sub>V = id\<^sub>V \<and> u\<^sub>V \<circ>\<^sub>m u'\<^sub>V = id'\<^sub>V \<and> u'\<^sub>E \<circ>\<^sub>m u\<^sub>E = id\<^sub>E \<and> u\<^sub>E \<circ>\<^sub>m u'\<^sub>E = id'\<^sub>E\<close> morph_composition)

          moreover have \<open> ?u'''\<^sub>V \<circ>\<^sub>m p\<^sub>V = p\<^sub>V' \<and> ?u'''\<^sub>E \<circ>\<^sub>m p\<^sub>E = p\<^sub>E' \<and> ?u'''\<^sub>V \<circ>\<^sub>m q\<^sub>V = t\<^sub>V \<and> ?u'''\<^sub>E \<circ>\<^sub>m q\<^sub>E = t\<^sub>E \<close>
            by (metis \<open>id\<^sub>E \<circ>\<^sub>m f\<^sub>E = f\<^sub>E\<close> \<open>id\<^sub>E \<circ>\<^sub>m g\<^sub>E = g\<^sub>E\<close> \<open>id\<^sub>V \<circ>\<^sub>m f\<^sub>V = f\<^sub>V\<close> \<open>id\<^sub>V \<circ>\<^sub>m g\<^sub>V = g\<^sub>V\<close> \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u''\<^sub>V u''\<^sub>E \<and> u''\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V' \<and> u''\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E' \<and> u''\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u''\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close> \<open>u'\<^sub>E \<circ>\<^sub>m (u\<^sub>E \<circ>\<^sub>m f\<^sub>E) = id\<^sub>E \<circ>\<^sub>m f\<^sub>E\<close> \<open>u'\<^sub>E \<circ>\<^sub>m (u\<^sub>E \<circ>\<^sub>m g\<^sub>E) = id\<^sub>E \<circ>\<^sub>m g\<^sub>E\<close> \<open>u'\<^sub>V \<circ>\<^sub>m (u\<^sub>V \<circ>\<^sub>m f\<^sub>V) = id\<^sub>V \<circ>\<^sub>m f\<^sub>V\<close> \<open>u'\<^sub>V \<circ>\<^sub>m (u\<^sub>V \<circ>\<^sub>m g\<^sub>V) = id\<^sub>V \<circ>\<^sub>m g\<^sub>V\<close> ex map_comp_assoc)


          moreover have \<open>(x\<^sub>V, x\<^sub>E) = (?u'''\<^sub>V, ?u'''\<^sub>E)\<close> if
            \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H x\<^sub>V x\<^sub>E 
            \<and> x\<^sub>V \<circ>\<^sub>m p\<^sub>V = p\<^sub>V' \<and> x\<^sub>E \<circ>\<^sub>m p\<^sub>E = p\<^sub>E' 
            \<and> x\<^sub>V \<circ>\<^sub>m q\<^sub>V = t\<^sub>V \<and> x\<^sub>E \<circ>\<^sub>m q\<^sub>E = t\<^sub>E\<close> for x\<^sub>V and x\<^sub>E
            using pushout_diagram.universal_property[of 
                V\<^sub>A E\<^sub>A s\<^sub>A t\<^sub>A l\<^sub>A m\<^sub>A
                V\<^sub>B E\<^sub>B s\<^sub>B t\<^sub>B l\<^sub>B m\<^sub>B
                V\<^sub>C E\<^sub>C s\<^sub>C t\<^sub>C l\<^sub>C m\<^sub>C
                V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>'
                b\<^sub>V b\<^sub>E c\<^sub>V c\<^sub>E
                p\<^sub>V p\<^sub>E q\<^sub>V q\<^sub>E
                V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H
                p\<^sub>V' p\<^sub>E' t\<^sub>V t\<^sub>E]
          proof -
            have \<open>x\<^sub>V \<circ>\<^sub>m u\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V'\<close>
              by (simp add: ex map_comp_assoc that)
            moreover have \<open>x\<^sub>E \<circ>\<^sub>m u\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E'\<close>
            by (simp add: ex map_comp_assoc that)

          moreover have \<open>x\<^sub>V \<circ>\<^sub>m u\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V\<close>
            by (simp add: ex map_comp_assoc that)
          moreover have \<open>x\<^sub>E \<circ>\<^sub>m u\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close>
            by (simp add: ex map_comp_assoc that)

          moreover have \<open>x\<^sub>V \<circ>\<^sub>m u\<^sub>V = u''\<^sub>V\<close>
          proof -
            have \<open>\<exists>!x. morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H (fst x) (snd x)
            \<and> (fst x) \<circ>\<^sub>m f\<^sub>V = p\<^sub>V' \<and> (snd x) \<circ>\<^sub>m f\<^sub>E = p\<^sub>E' \<and> (fst x) \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> (snd x) \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close>
              using universal_property[of V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H p\<^sub>V' p\<^sub>E' t\<^sub>V t\<^sub>E]
              apply auto
              using \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u''\<^sub>V u''\<^sub>E \<and> u''\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V' \<and> u''\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E' \<and> u''\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u''\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close> apply auto[1]
              using \<open>graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H\<close> \<open>morphism V\<^sub>B E\<^sub>B s\<^sub>B t\<^sub>B l\<^sub>B m\<^sub>B V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H p\<^sub>V' p\<^sub>E'\<close> \<open>morphism V\<^sub>C E\<^sub>C s\<^sub>C t\<^sub>C l\<^sub>C m\<^sub>C V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H t\<^sub>V t\<^sub>E\<close> \<open>p\<^sub>E' \<circ>\<^sub>m b\<^sub>E = t\<^sub>E \<circ>\<^sub>m c\<^sub>E\<close> \<open>p\<^sub>V' \<circ>\<^sub>m b\<^sub>V = t\<^sub>V \<circ>\<^sub>m c\<^sub>V\<close> by auto
             
              then show ?thesis
                by (smt (z3) \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u''\<^sub>V u''\<^sub>E \<and> u''\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V' \<and> u''\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E' \<and> u''\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u''\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close> bijective_morphism.axioms(1) calculation(1) calculation(2) calculation(3) calculation(4) ex fst_conv injective_morphism_def morph_composition snd_conv that)
            qed

          moreover have \<open>x\<^sub>E \<circ>\<^sub>m u\<^sub>E = u''\<^sub>E\<close>
          proof -
            have \<open>\<exists>!x. morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H (fst x) (snd x)
            \<and> (fst x) \<circ>\<^sub>m f\<^sub>V = p\<^sub>V' \<and> (snd x) \<circ>\<^sub>m f\<^sub>E = p\<^sub>E' \<and> (fst x) \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> (snd x) \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close>
              using universal_property[of V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H p\<^sub>V' p\<^sub>E' t\<^sub>V t\<^sub>E]
              apply auto
              using \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u''\<^sub>V u''\<^sub>E \<and> u''\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V' \<and> u''\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E' \<and> u''\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u''\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close> apply auto[1]
              using \<open>graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H\<close> \<open>morphism V\<^sub>B E\<^sub>B s\<^sub>B t\<^sub>B l\<^sub>B m\<^sub>B V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H p\<^sub>V' p\<^sub>E'\<close> \<open>morphism V\<^sub>C E\<^sub>C s\<^sub>C t\<^sub>C l\<^sub>C m\<^sub>C V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H t\<^sub>V t\<^sub>E\<close> \<open>p\<^sub>E' \<circ>\<^sub>m b\<^sub>E = t\<^sub>E \<circ>\<^sub>m c\<^sub>E\<close> \<open>p\<^sub>V' \<circ>\<^sub>m b\<^sub>V = t\<^sub>V \<circ>\<^sub>m c\<^sub>V\<close> by auto
             
              then show ?thesis
                by (smt (z3) \<open>morphism V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u''\<^sub>V u''\<^sub>E \<and> u''\<^sub>V \<circ>\<^sub>m f\<^sub>V = p\<^sub>V' \<and> u''\<^sub>E \<circ>\<^sub>m f\<^sub>E = p\<^sub>E' \<and> u''\<^sub>V \<circ>\<^sub>m g\<^sub>V = t\<^sub>V \<and> u''\<^sub>E \<circ>\<^sub>m g\<^sub>E = t\<^sub>E\<close> bijective_morphism.axioms(1) calculation(1) calculation(2) calculation(3) calculation(4) ex fst_conv injective_morphism_def morph_composition snd_conv that)
            qed

          moreover have \<open>x\<^sub>V = x\<^sub>V \<circ>\<^sub>m (u\<^sub>V \<circ>\<^sub>m u'\<^sub>V)\<close>
            using \<open>graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H\<close> \<open>identity_morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' id'\<^sub>V id'\<^sub>E\<close> \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D u'\<^sub>V u'\<^sub>E \<and> u'\<^sub>V \<circ>\<^sub>m u\<^sub>V = id\<^sub>V \<and> u\<^sub>V \<circ>\<^sub>m u'\<^sub>V = id'\<^sub>V \<and> u'\<^sub>E \<circ>\<^sub>m u\<^sub>E = id\<^sub>E \<and> u\<^sub>E \<circ>\<^sub>m u'\<^sub>E = id'\<^sub>E\<close> comp_id_morph(1) id_morphI that by fastforce
          moreover have \<open>\<dots> = u''\<^sub>V \<circ>\<^sub>m u'\<^sub>V\<close>
            by (metis calculation(5) map_comp_assoc)
          moreover have \<open>\<dots> = ?u'''\<^sub>V\<close>
            by simp

          moreover have \<open>x\<^sub>E = x\<^sub>E \<circ>\<^sub>m (u\<^sub>E \<circ>\<^sub>m u'\<^sub>E)\<close>
            using \<open>graph V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H\<close> \<open>identity_morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' id'\<^sub>V id'\<^sub>E\<close> \<open>morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>D E\<^sub>D s\<^sub>D t\<^sub>D l\<^sub>D m\<^sub>D u'\<^sub>V u'\<^sub>E \<and> u'\<^sub>V \<circ>\<^sub>m u\<^sub>V = id\<^sub>V \<and> u\<^sub>V \<circ>\<^sub>m u'\<^sub>V = id'\<^sub>V \<and> u'\<^sub>E \<circ>\<^sub>m u\<^sub>E = id\<^sub>E \<and> u\<^sub>E \<circ>\<^sub>m u'\<^sub>E = id'\<^sub>E\<close> comp_id_morph(2) id_morphI that by fastforce
          moreover have \<open>\<dots> = u''\<^sub>E \<circ>\<^sub>m u'\<^sub>E\<close>
            by (metis calculation(6) map_comp_assoc)
          moreover have \<open>\<dots> = ?u'''\<^sub>E\<close>
            by simp


          ultimately show ?thesis
            by simp
        qed       
          show \<open>\<exists>!(u\<^sub>V, u\<^sub>E).
           morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and>
           u\<^sub>V \<circ>\<^sub>m p\<^sub>V = p\<^sub>V' \<and> u\<^sub>E \<circ>\<^sub>m p\<^sub>E = p\<^sub>E' \<and> u\<^sub>V \<circ>\<^sub>m q\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m q\<^sub>E = t\<^sub>E\<close>
          proof
            show \<open>case (?u'''\<^sub>V, ?u'''\<^sub>E) of
    (u\<^sub>V, u\<^sub>E) \<Rightarrow>
      morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and>
      u\<^sub>V \<circ>\<^sub>m p\<^sub>V = p\<^sub>V' \<and> u\<^sub>E \<circ>\<^sub>m p\<^sub>E = p\<^sub>E' \<and> u\<^sub>V \<circ>\<^sub>m q\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m q\<^sub>E = t\<^sub>E\<close>
            using \<open>u''\<^sub>V \<circ>\<^sub>m u'\<^sub>V \<circ>\<^sub>m p\<^sub>V = p\<^sub>V' \<and> u''\<^sub>E \<circ>\<^sub>m u'\<^sub>E \<circ>\<^sub>m p\<^sub>E = p\<^sub>E' \<and> u''\<^sub>V \<circ>\<^sub>m u'\<^sub>V \<circ>\<^sub>m q\<^sub>V = t\<^sub>V \<and> u''\<^sub>E \<circ>\<^sub>m u'\<^sub>E \<circ>\<^sub>m q\<^sub>E = t\<^sub>E\<close> calculation by blast
        next
          show \<open>(case x of
         (u\<^sub>V, u\<^sub>E) \<Rightarrow>
           morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H u\<^sub>V u\<^sub>E \<and>
           u\<^sub>V \<circ>\<^sub>m p\<^sub>V = p\<^sub>V' \<and> u\<^sub>E \<circ>\<^sub>m p\<^sub>E = p\<^sub>E' \<and> u\<^sub>V \<circ>\<^sub>m q\<^sub>V = t\<^sub>V \<and> u\<^sub>E \<circ>\<^sub>m q\<^sub>E = t\<^sub>E) \<Longrightarrow>
         x = (u''\<^sub>V \<circ>\<^sub>m u'\<^sub>V, u''\<^sub>E \<circ>\<^sub>m u'\<^sub>E)\<close> for x
            using \<open>\<And>x\<^sub>V x\<^sub>E. morphism V\<^sub>D\<^sub>' E\<^sub>D\<^sub>' s\<^sub>D\<^sub>' t\<^sub>D\<^sub>' l\<^sub>D\<^sub>' m\<^sub>D\<^sub>' V\<^sub>H E\<^sub>H s\<^sub>H t\<^sub>H l\<^sub>H m\<^sub>H x\<^sub>V x\<^sub>E \<and> x\<^sub>V \<circ>\<^sub>m p\<^sub>V = p\<^sub>V' \<and> x\<^sub>E \<circ>\<^sub>m p\<^sub>E = p\<^sub>E' \<and> x\<^sub>V \<circ>\<^sub>m q\<^sub>V = t\<^sub>V \<and> x\<^sub>E \<circ>\<^sub>m q\<^sub>E = t\<^sub>E \<Longrightarrow> (x\<^sub>V, x\<^sub>E) = (u''\<^sub>V \<circ>\<^sub>m u'\<^sub>V, u''\<^sub>E \<circ>\<^sub>m u'\<^sub>E)\<close> by blast
        qed
      qed
    qed
  qed
  qed
qed
end

end

