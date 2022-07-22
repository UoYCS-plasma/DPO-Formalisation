theory Rule
  imports Morphism
begin

locale rule =
  k: injective_morphism K L k +
  r: injective_morphism K R r 
  for L K R k r

notation rule ("_\<leftarrow>_\<rightarrow>_")

end