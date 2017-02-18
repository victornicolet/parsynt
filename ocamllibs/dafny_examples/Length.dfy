function Length___0(s: seq<int>): int
{ if s == [] then  0 else  (Length___0(s[..|s|-1]) + 1) 
}

function Length___0Join(leftLength___0 : int, rightLength___0 : int): int
{
  ((rightLength___0 - 1) + (leftLength___0 - -1))
}


lemma HomLength___0(s : seq<int>, t : seq<int>)
  
               ensures Length___0(s + t) == Length___0Join(Length___0(s), Length___0(t))
  {
    if t == [] 
    {
    assert(s + [] == s);
    } else {
    calc{
    Length___0(s + t);
    =={ assert(s + t[..|t|-1]) + [t[|t|-1]] == s + t; }
    Length___0Join(Length___0(s), Length___0(t));
    } // End calc.
  } // End else.
} // End lemma.

