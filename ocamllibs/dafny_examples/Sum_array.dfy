function Sum(s: seq<int>): int
{ if s == [] then  0 else  (Sum(s[..|s|-1]) + s[|s|-1]) 
}

function SumJoin(leftSum : int, rightSum : int): int
{
  ((rightSum - 1) + (leftSum - -1))
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

