function DfMin(x: int, y: int): int { if x > y then y else x}

function Aux_3(s: seq<bool>): int
{ if s == [] then  0 else  DfMin(Cnt(s[..|s|-1]), Aux_3(s[..|s|-1])) 
}

function Bal(s: seq<bool>): bool
{ if s == [] then
    true
   else 
   (Bal(s[..|s|-1]) && ((Cnt(s[..|s|-1]) + if s[|s|-1] then 1 else -1) >= 0))
   
}

function Cnt(s: seq<bool>): int
{ if s == [] then  0 else  (Cnt(s[..|s|-1]) + if s[|s|-1] then 1 else -1) 
}

function Aux_3Join(leftAux_3 : int, leftCnt : int, rightAux_3 : int, rightCnt : int): int
{
  DfMin((leftCnt + rightAux_3), leftAux_3)
}

function BalJoin(leftAux_3 : int, leftCnt : int, leftBal : bool, rightAux_3 : int, rightCnt : int, rightBal : bool): bool
{
  (leftBal && (((leftCnt + 1) + if rightBal then 0 else -6) > (-6 - rightAux_3)))
}

function CntJoin(leftAux_3 : int, leftCnt : int, rightAux_3 : int, rightCnt : int): int
{
  ((leftCnt + 1) + if true then (-1 + rightCnt) else rightAux_3)
}


lemma HomAux_3(s : seq<bool>, t : seq<bool>)
  
               ensures Aux_3(s + t) == Aux_3Join(Aux_3(s), Cnt(s), Aux_3(t), Cnt(t))
  {
    if t == [] 
    {
    assert(s + [] == s);
    } else {
    calc{
    Aux_3(s + t);
    =={
      HomCnt(s, t[..|t| - 1]);
      assert(s + t[..|t|-1]) + [t[|t|-1]] == s + t;
      }
    Aux_3Join(Aux_3(s), Cnt(s), Aux_3(t), Cnt(t));
    } // End calc.
  } // End else.
} // End lemma.

lemma HomBal(s : seq<bool>, t : seq<bool>)
  
               ensures Bal(s + t) == BalJoin(Aux_3(s), Cnt(s), Bal(s), Aux_3(t), Cnt(t), Bal(t))
  {
    if t == [] 
    {
    assert(s + [] == s);
    } else {
    calc{
    Bal(s + t);
    =={
      HomAux_3(s, t[..|t| - 1]);
      HomCnt(s, t[..|t| - 1]);
      assert(s + t[..|t|-1]) + [t[|t|-1]] == s + t;
      }
    BalJoin(Aux_3(s), Cnt(s), Bal(s), Aux_3(t), Cnt(t), Bal(t));
    } // End calc.
  } // End else.
} // End lemma.

lemma HomCnt(s : seq<bool>, t : seq<bool>)
  
               ensures Cnt(s + t) == CntJoin(Aux_3(s), Cnt(s), Aux_3(t), Cnt(t))
  {
    if t == [] 
    {
    assert(s + [] == s);
    } else {
    calc{
    Cnt(s + t);
    =={
      HomAux_3(s, t[..|t| - 1]);
      assert(s + t[..|t|-1]) + [t[|t|-1]] == s + t;
      }
    CntJoin(Aux_3(s), Cnt(s), Aux_3(t), Cnt(t));
    } // End calc.
  } // End else.
} // End lemma.

