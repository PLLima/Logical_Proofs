method SomaGaussiana (x:int) returns (y:int)
  requires x >= 0
  ensures  y == (x*(x+1))/2
{
  var i:int := 0;
  y := 0;
  while (i != x)
    invariant y == (i*(i+1))/2 && x - i >= 0 && x >= 0
    decreases x - i
  { 
    i := i + 1;
    y := y + i;
  }
}
