theory DirectDerivation
  imports Rule Gluing Deletion
begin

locale direct_derivation =
  r: rule L K R +
  d: deletion K G L g idM +
  g: gluing K d.D R g idM for G l L K R g

end