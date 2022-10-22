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

end