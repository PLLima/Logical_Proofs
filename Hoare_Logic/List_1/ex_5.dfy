method Div (x0:int, y:int) returns (z:int, r:int)
  requires x0 > 0
  requires y > 0
  ensures  x0 == z * y + r
{
  r := x0;
  z := 0;
  while (y <= r)
    invariant x0 - r == y * z
    invariant r >= 0
    decreases r
  {
    z := z+1;
    r := r-y;
  }
}
