function DfLength(s: seq<int>): int
{if s == [] then 0 else DfLength(s[..|s|-1]) + 1}

function Length(dafny_seq_ : seq<int>): int
{
  if dafny_seq_ == [] then 0 else (Length(dafny_seq_[..|dafny_seq_|-1]) + 1)
}

function LengthJoin(leftLength : int, rightLength : int): int
{
  ((rightLength - 1) + (leftLength + 1))
}


lemma BaseCaseLength(dafny_seq_ : seq<int>)
  ensures Length(dafny_seq_) == LengthJoin(Length(dafny_seq_), Length([]))
  {}

lemma HomLength(dafny_seq_ : seq<int>, R_dafny_seq_ : seq<int>)
  ensures Length(dafny_seq_ + R_dafny_seq_) == LengthJoin(Length(dafny_seq_), Length(R_dafny_seq_))
  {
    if R_dafny_seq_ == [] 
    {
    assert(dafny_seq_ + [] == dafny_seq_);
    BaseCaseLength(dafny_seq_);
    
     } else {
    calc{
    Length(dafny_seq_ + R_dafny_seq_);
    =={
      assert(dafny_seq_ + R_dafny_seq_[..|R_dafny_seq_|-1]) + [R_dafny_seq_[|R_dafny_seq_|-1]] == dafny_seq_ + R_dafny_seq_;
      }
    LengthJoin(Length(dafny_seq_), Length(R_dafny_seq_));
    } // End calc.
  } // End else.
} // End lemma.

