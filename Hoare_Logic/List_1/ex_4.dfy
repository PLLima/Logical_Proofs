function fib(n: nat): nat
  decreases n
{
  if n == 0 then 0 
  else if n == 1 then 1 
  else fib(n - 1) + fib(n - 2)
}

method Fibonacci (n:int) returns (f:int)
  requires n > 0
  ensures  f == fib(n)
{
  var i:int := n;
  var p:int := 1;
  var h:int := 1;
  while (i > 1)
    invariant p == fib(n - i + 1)
    invariant h == fib(n - i + 2)
    invariant i >= 1
    decreases i - 1
  {
    h := h+p;
    p := h-p;
    i := i-1;
  }
  f := p;
}
