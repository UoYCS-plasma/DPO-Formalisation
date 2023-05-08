theory Rule
  imports Morphism
begin

record ('v\<^sub>1,'e\<^sub>1,'v\<^sub>2,'e\<^sub>2,'v\<^sub>3,'e\<^sub>3,'l,'m) pre_rule =
  lhs    :: "('v\<^sub>1,'e\<^sub>1,'l,'m) pre_graph"
  interf :: "('v\<^sub>2,'e\<^sub>2,'l,'m) pre_graph"
  rhs    :: "('v\<^sub>3,'e\<^sub>3,'l,'m) pre_graph"

locale rule =
  k: injective_morphism "interf r" "lhs r" b +
  r: injective_morphism "interf r" "rhs r" b'
  for r :: "('v\<^sub>1::countable,'e\<^sub>1::countable
            ,'v\<^sub>2::countable,'e\<^sub>2::countable
            ,'v\<^sub>3::countable,'e\<^sub>3::countable
            ,'l,'m) pre_rule" and b b'

end