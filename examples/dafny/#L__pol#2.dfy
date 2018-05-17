function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function Res(coeffs : seq<int>): int
{
  if coeffs == [] then
    0
    else
    (Res(coeffs[..|coeffs|-1]) + (Factor(coeffs[..|coeffs|-1]) * coeffs[|coeffs|-1]))
}

function Factor(x : int): int
{
  if coeffs == [] then 1 else (x * Factor(coeffs[..|coeffs|-1]))
}

function ResJoin(leftFactor : int, leftRes : int, rightFactor : int, rightRes : int): int
{
  (((rightRes + 1) * leftFactor) + (leftRes - leftFactor))
}

function FactorJoin(leftFactor : int, rightFactor : int): int
{
  (leftFactor * rightFactor)
}


lemma BaseCaseRes(coeffs : seq<int>)
  ensures Res(coeffs) == ResJoin(Factor(coeffs), Res(coeffs), Factor([]), Res([]))
  {}

lemma HomRes(coeffs : seq<int>, R_coeffs : seq<int>)
  ensures Res(coeffs + R_coeffs) == ResJoin(Factor(coeffs), Res(coeffs), Factor(R_coeffs), Res(R_coeffs))
  {
    if R_coeffs == [] 
    {
    assert(coeffs + [] == coeffs);
    BaseCaseRes(coeffs);
    
     } else {
    calc{
    Res(coeffs + R_coeffs);
    =={
      HomFactor(coeffs, R_coeffs[..|R_coeffs| - 1]);
      assert(coeffs + R_coeffs[..|R_coeffs|-1]) + [R_coeffs[|R_coeffs|-1]] == coeffs + R_coeffs;
      }
    ResJoin(Factor(coeffs), Res(coeffs), Factor(R_coeffs), Res(R_coeffs));
    } // End calc.
  } // End else.
} // End lemma.

lemma BaseCaseFactor(x : int)
  ensures Factor(coeffs) == FactorJoin(Factor(coeffs), Factor([]))
  {}

lemma HomFactor(x : int, R_x : int)
  ensures Factor(coeffs + R_coeffs) == FactorJoin(Factor(coeffs), Factor(R_coeffs))
  {
    if R_coeffs == [] 
    {
    assert(coeffs + [] == coeffs);
    BaseCaseFactor(coeffs);
    
     } else {
    calc{
    Factor(coeffs + R_coeffs);
    =={
      assert(coeffs + R_coeffs[..|R_coeffs|-1]) + [R_coeffs[|R_coeffs|-1]] == coeffs + R_coeffs;
      }
    FactorJoin(Factor(coeffs), Factor(R_coeffs));
    } // End calc.
  } // End else.
} // End lemma.

