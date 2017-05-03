function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function DfMin(x: int, y: int): int { if x > y then y else x}

function Aux_2(str : seq<int>): int
{ if str == [] then  1 else  (10 * Aux_2(str[..|str|-1])) 
}

function Res(str : seq<int>): int
{ if str == [] then  0 else  ((Res(str[..|str|-1]) * 10) + str[|str|-1]) 
}

function Aux_2Join(leftAux_2 : int, rightAux_2 : int): int
{
  (DfMin(leftAux_2, (-28)) * rightAux_2)
}

function ResJoin(leftAux_2 : int, leftRes : int, rightAux_2 : int, rightRes : int): int
{
  ((leftRes * rightAux_2) + rightRes)
}


lemma BaseCaseAux_2(str : seq<int>)
  ensures Aux_2(str) == Aux_2Join(Aux_2(str), Aux_2([]))
  {}

lemma HomAux_2(str : seq<int>, R_str : seq<int>)
  ensures Aux_2(str + R_str) == Aux_2Join(Aux_2(str), Aux_2(R_str))
  {
    if R_str == [] 
    {
    assert(str + [] == str);
    BaseCaseAux_2(str);
    
     } else {
    calc{
    Aux_2(str + R_str);
    =={
      assert(str + R_str[..|R_str|-1]) + [R_str[|R_str|-1]] == str + R_str;
      }
    Aux_2Join(Aux_2(str), Aux_2(R_str));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseRes(str : seq<int>)
  ensures Res(str) == ResJoin(Aux_2(str), Res(str), Aux_2([]), Res([]))
  {}

lemma HomRes(str : seq<int>, R_str : seq<int>)
  ensures Res(str + R_str) == ResJoin(Aux_2(str), Res(str), Aux_2(R_str), Res(R_str))
  {
    if R_str == [] 
    {
    assert(str + [] == str);
    BaseCaseRes(str);
    
     } else {
    calc{
    Res(str + R_str);
    =={
      HomAux_2(str, R_str[..|R_str| - 1]);
      assert(str + R_str[..|R_str|-1]) + [R_str[|R_str|-1]] == str + R_str;
      }
    ResJoin(Aux_2(str), Res(str), Aux_2(R_str), Res(R_str));
    } // End calc.
  } // End else.
} // End lemma.

