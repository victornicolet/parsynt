function Sum(s: seq<int>): int
{ if s == [] then  0 else  (Sum(s[..|s|-1]) + s[|s|-1]) 
}

function Mps(s: seq<int>): int
{ if s == [] then
    0
   else 
   if ((Sum(s[..|s|-1]) + s[|s|-1]) > Mps(s[..|s|-1])) then
     (Sum(s[..|s|-1]) + s[|s|-1]) else Mps(s[..|s|-1])
   
}

function SumJoin(leftSum : int, rightSum : int): int
{
  (leftSum + rightSum)
}

function MpsJoin(leftMps : int, leftSum : int, rightMps : int, rightSum : int): int
{
  if (((-3940 + leftMps) + 3940) > (rightMps + leftSum)) then
    ((-3940 + leftMps) + 3940) else (rightMps + leftSum)
}


lemma HomSum(s : seq<int>, t : seq<int>)
  ensures Sum(s + t) == SumJoin(Sum(s), Sum(t))
  {
    if t == [] 
    {
    assert(s + [] == s);
    } else {
    calc{
    Sum(s + t);
    =={ assert(s + t[..|t|-1]) + [t[|t|-1]] == s + t; }
    SumJoin(Sum(s), Sum(t));
    } // End calc.
  } // End else.
} // End lemma.

lemma HomMps(s : seq<int>, t : seq<int>)
  ensures Mps(s + t) == MpsJoin(Mps(s), Sum(s), Mps(t), Sum(t))
  {
    if t == [] 
    {
    assert(s + [] == s);
    } else {
    calc{
    Mps(s + t);
    =={
      HomSum(s, t[..|t| - 1]);
      assert(s + t[..|t|-1]) + [t[|t|-1]] == s + t;
      }
    MpsJoin(Mps(s), Sum(s), Mps(t), Sum(t));
    } // End calc.
  } // End else.
} // End lemma.

