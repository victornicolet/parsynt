function DfMax(x: int, y: int): int { if x > y then x else y}

function Aux_1(s: seq<int>): int
{ if s == [] then  1 else  (s[|s|-1] + Aux_1(s[..|s|-1])) 
}

function Mts___0(s: seq<int>): int
{ if s == [] then  0 else  DfMax(0, (Mts___0(s[..|s|-1]) + s[|s|-1])) 
}

function Aux_1Join(leftAux_1 : int, rightAux_1 : int): int
{
  ((8124 + rightAux_1) + (-8125 + leftAux_1))
}

function Mts___0Join(leftAux_1 : int, leftMts___0 : int, rightAux_1 : int, rightMts___0 : int): int
{
  DfMax(rightMts___0, (leftMts___0 + (rightAux_1 - 1)))
}


lemma HomAux_1(s : seq<int>, t : seq<int>)
  
               ensures Aux_1(s + t) == Aux_1Join(Aux_1(s), Aux_1(t))
  {
    if t == [] 
    {
    assert(s + [] == s);
    } else {
    calc{
    Aux_1(s + t);
    =={ assert(s + t[..|t|-1]) + [t[|t|-1]] == s + t; }
    Aux_1Join(Aux_1(s), Aux_1(t));
    } // End calc.
  } // End else.
} // End lemma.

lemma HomMts___0(s : seq<int>, t : seq<int>)
  
               ensures Mts___0(s + t) == Mts___0Join(Aux_1(s), Mts___0(s), Aux_1(t), Mts___0(t))
  {
    if t == [] 
    {
    assert(s + [] == s);
    } else {
    calc{
    Mts___0(s + t);
    =={
      HomAux_1(s, t[..|t| - 1]);
      assert(s + t[..|t|-1]) + [t[|t|-1]] == s + t;
      }
    Mts___0Join(Aux_1(s), Mts___0(s), Aux_1(t), Mts___0(t));
    } // End calc.
  } // End else.
} // End lemma.

