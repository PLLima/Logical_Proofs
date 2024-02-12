// Exemplo de Soma Gaussiana

method Soma (x:int) returns (y:int)
  requires x >= 0
  ensures  y == (x*(x+1))/2
{
  var i:int := 0;
  y := 0;
  while (i!=x)
    invariant y==(i*(i+1))/2
    invariant x-i>=0
    decreases x-i 
  { 
    i := i + 1;
    assert i>0;
    y := y + i;
  }
}
