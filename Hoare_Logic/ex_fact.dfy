function factorial(n:nat) : nat
  decreases n
{
  if (n == 0) then 1
  else n * factorial(n - 1)
}

method Fact (x:int) returns (y:int)
  requires x >= 0
  ensures  y == factorial(x)
{
    y := 1;
    var z:int := 0;
    while (z != x)
      invariant y == factorial(z)
      invariant x >= z
      decreases x - z
    {
        z := z + 1;
        y := y * z;
    }
}
