#include <iostream>
#include <tbb/tbb.h>
#include "ExampleUnit.h"
#include "Examples.h"

using namespace tbb;

typedef long a_size;

class SumFoo {
    int* my_a;
public:
    int my_sum;
    a_size b, e;

    SumFoo(int a[]) : my_a(a), my_sum(0), b(-1), e(-1)  {}
    SumFoo(SumFoo& x, split ) : my_a(x.my_a), my_sum(0), b(-1), e(-1) {}


    void operator()( const blocked_range<a_size>& r )
    {
        int *a = my_a;
        int sum = my_sum;
        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            sum +=  a[i];
        }

        my_sum = sum;
    }

    void join(const SumFoo& y) {
        my_sum = my_sum + y.my_sum;
        e = y.e;
    }
};


int ExampleSum::parallel_apply() const {
    SumFoo sf(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), sf );
    return sf.my_sum;
}

int ExampleSum::seq_apply() const {
    int sum = 0;
    for (a_size i = 0L; i < n; i++)
        sum += a[i];
    return sum;
}

int ExampleSum::full_seq_apply() const {return seq_apply();}

/** Example : compute length */

class LengthCore {
    int* my_a;
public:
    a_size my_length;
    a_size b, e;

    LengthCore(int a[]) : my_a(a), my_length(0), b(-1), e(-1)  {}
    LengthCore(LengthCore& x, split ) : my_a(x.my_a), my_length(0), b(-1), e(-1) {}


    void operator()( const blocked_range<a_size>& r )
    {
        int *a = my_a;
        a_size length = my_length;
        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            length+=1;
        }

        my_length = length;
    }

    void join(const LengthCore& rhs) {
        my_length = my_length + rhs.my_length;
        e = rhs.e;
    }
};


a_size ExampleLength::parallel_apply() const {
    LengthCore sf(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), sf );
    return sf.my_length;
}

a_size ExampleLength::seq_apply() const {
    a_size length = 0;
    for (a_size i = 0; i < n; i++)
        length += 1;
    return length;
}

a_size ExampleLength::full_seq_apply() const {return seq_apply();}

/** Other simple example : Max */
class MaxCore {
    int* my_a;
public:
    int amax;
    a_size b, e;

    MaxCore(int a[]) : my_a(a), amax(INT32_MIN), b(-1), e(-1)  {}
    MaxCore(MaxCore& x, split ) : my_a(x.my_a), amax(INT32_MIN), b(-1), e(-1) {}


    void operator()( const blocked_range<a_size>& r )
    {
        int *a = my_a;
        int tmp_amax = amax;
        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            tmp_amax = (tmp_amax > a[i]) ? tmp_amax : a[i];
        }

        amax = tmp_amax;
    }

    void join(const MaxCore& y) {
        amax = (amax > y.amax) ? amax : y.amax;
        e = y.e;
    }
};


int ExampleMax::parallel_apply() const{
    MaxCore maxc(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), maxc);
    return  maxc.amax;
}
int ExampleMax::seq_apply() const {
    int amax = INT32_MIN;
    for(a_size i =0; i < n; i++) {
        amax = (amax > a[i]) ? amax : a[i];
    }
    return amax;
}
int ExampleMax::full_seq_apply() const {return seq_apply();}

/** Other example : Min */

class MinCore {
    int* my_a;
public:
    int amin;
    a_size b, e;

    MinCore(int a[]) : my_a(a), amin(INT32_MAX), b(-1), e(-1)  {}
    MinCore(MinCore& x, split ) : my_a(x.my_a), amin(INT32_MAX), b(-1), e(-1) {}


    void operator()( const blocked_range<a_size>& r )
    {
        int *a = my_a;
        int tmp_amin = amin;
        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            tmp_amin = (tmp_amin < a[i]) ? tmp_amin : a[i];
        }

        amin = tmp_amin;
    }

    void join(const MinCore& y) {
        amin = (amin > y.amin) ? amin : y.amin;
        e = y.e;
    }
};


int ExampleMin::parallel_apply() const{
    MinCore minc(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), minc);
    return  minc.amin;
}
int ExampleMin::seq_apply() const {
    int amin = INT32_MAX;
    for(a_size i =0; i < n; i++) {
        amin = (amin < a[i]) ? amin : a[i];
    }
    return amin;
}

int ExampleMin::full_seq_apply() const {return seq_apply();}

/** Example : counting the blocks of ones */
struct counting_ones_state {
    int count;
    bool last;
    bool aux;
};

class CountingOnesCore {
    bool* my_a;

public:
    counting_ones_state s;
    a_size b, e;

    CountingOnesCore(bool a[]) :
            my_a(a), b(-1), e(-1)  { s = {0, false, false};}
    CountingOnesCore(CountingOnesCore& x, split) :
    my_a(x.my_a), b(-1), e(-1) { s = {0, false, false};}


    void operator()( const blocked_range<a_size>& r )
    {
        bool *a = my_a;
        int tmp_cnt = s.count;
        bool f = s.last;

        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            tmp_cnt += (a[i] && !f) ? 1 : 0;
            f = a[i];
        }

        s = {tmp_cnt, f, a[b]};
    }

    void join(const CountingOnesCore& rhs) {
        s = {
                rhs.s.count + (s.last && rhs.s.aux) ? s.count - 1 : s.count,
                rhs.s.last,
                s.aux
        };
        e = rhs.e;
    }
};


int ExampleCountingOnes::parallel_apply() const{
    CountingOnesCore coc(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), coc);
    return  coc.s.count;
}
int ExampleCountingOnes::seq_apply() const {
    int cnt = 0;
    bool last = false;
    for(a_size i = 0; i < n; i++) {
        cnt += (a[i] && !last) ? 1 : 0;
        last = a[i];
    }
    return cnt;
}

int ExampleCountingOnes::full_seq_apply() const {
    int cnt = 0;
    bool last = false;
    for(a_size i = 0; i < n; i++) {
        cnt += (a[i] && !last) ? 1 : 0;
        last = a[i];
    }
    cnt = a[n-1] ? cnt : cnt;
    return cnt;
}
/** Example : position of the end of maximum prefix sum */
struct mps_pos_state {
    int mps;
    a_size pos;
    int sum;
};

class MpsPosCore {
    int* my_a;

public:
    mps_pos_state s;
    a_size b, e;

    MpsPosCore(int a[]) :
            my_a(a), b(-1), e(-1)  { s = {0, 0, 0};}
    MpsPosCore(MpsPosCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { s = {0, 0, 0};}


    void operator()( const blocked_range<a_size>& r )
    {
        int *a = my_a;
        int tmp_mps = s.mps;
        int tmp_sum = s.sum;
        a_size tmp_pos = s.pos;

        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            tmp_sum += a[i];
            if (tmp_sum > tmp_mps) {
                tmp_pos = i;
                tmp_mps = tmp_sum;
            }
        }

        s = {tmp_mps, tmp_pos, tmp_sum};
    }

    void join(const MpsPosCore& rhs) {
        s = {
                max(s.mps, rhs.s.mps + s.sum),
                (rhs.s.mps + s.sum > rhs.s.mps) ? rhs.s.pos : s.pos,
                rhs.s.sum + s.sum
        };
        e = rhs.e;
    }
};


a_size ExampleMpsPos::parallel_apply() const{
    MpsPosCore coc(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), coc);
    return  coc.s.pos;
}
a_size ExampleMpsPos::seq_apply() const {
    int sum = 0;
    int mps = 0;
    a_size pos = 0;
    for(a_size i = 0; i < n; i++) {
        sum += a[i];
        if (sum > mps) {
            pos = i;
            mps = sum;
        }
    }
    return pos;
}

a_size ExampleMpsPos::full_seq_apply() const {return seq_apply();}

/** Example : position of start of maximum terminal sum */
struct mts_pos_state {
    int mts;
    a_size pos;
    int sum;
};

class MtsPosCore {
    int* my_a;

public:
    mts_pos_state s;
    a_size b, e;

    MtsPosCore(int a[]) :
            my_a(a), b(-1), e(-1)  { s = {0, 0, 0};}
    MtsPosCore(MtsPosCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { s = {0, 0, 0};}


    void operator()( const blocked_range<a_size>& r )
    {
        int *a = my_a;
        int tmp_mts = s.mts;
        int tmp_sum = s.sum;
        a_size tmp_pos = s.pos;

        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            tmp_sum += a[i];
            if(tmp_mts <= 0)
                tmp_pos = i;
            tmp_mts = max(tmp_mts + a[i], 0);
        }

        s = {tmp_mts, tmp_pos, tmp_sum};
    }

    void join(const MtsPosCore& rhs) {
        s = {
                max(s.mts + rhs.s.sum, rhs.s.mts),
                (rhs.s.sum + s.mts > rhs.s.mts) ? s.pos : rhs.s.pos,
                rhs.s.sum + s.sum
        };
        e = rhs.e;
    }
};

a_size ExampleMtsPos::parallel_apply() const{
    MtsPosCore coc(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), coc);
    return  coc.s.pos;
}
a_size ExampleMtsPos::seq_apply() const {
    int mts = 0;
    a_size pos = 0;
    for(a_size i = 0; i < n; i++) {
        if (mts <= 0)
            pos = i;
        mts = max(mts + a[i], 0);
    }
    return pos;
}
a_size ExampleMtsPos::full_seq_apply() const {
    int mts = 0;
    int sum = 0;
    a_size pos = 0;
    for(a_size i = 0; i < n; i++) {
        if (mts <= 0)
            pos = i;
        mts = max(mts + a[i], 0);
        sum = sum + a[i];
    }
    return pos + sum;
}

/** Example : mts*/
struct mts_state {
    int mts;
    int sum;
};

class MtsCore {
    int* my_a;

public:
    mts_state s;
    a_size b, e;

    MtsCore(int a[]) :
            my_a(a), b(-1), e(-1)  { s = {0, 0};}
    MtsCore(MtsCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { s = {0, 0};}


    void operator()( const blocked_range<a_size>& r )
    {
        int *a = my_a;
        int mts = s.mts;
        int sum = s.sum;

        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            sum = sum + a[i];
            mts = max(0, mts + a[i]);
        }

        s = {mts, sum};
    }

    void join(const MtsCore& rhs) {
        s = {
                max(rhs.s.sum + s.mts, rhs.s.mts),
                s.sum + rhs.s.sum
        };
        e = rhs.e;
    }
};



int ExampleMts::parallel_apply() const{
    MtsCore coc(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), coc);
    return  coc.s.mts;
}

int ExampleMts::seq_apply() const {
    int mts = 0;
    for(a_size i = 0; i < n; i++) {
        mts = max(0, mts + a[i]);
    }
    return mts;
}

int ExampleMts::full_seq_apply() const {
    int mts = 0;
    int sum = 0;
    for(a_size i = 0; i < n; i++) {
        mts = max(0, mts + a[i]);
        sum += a[i];
    }
    return mts + sum;
}

/** Example : Mss*/
struct mss_state {
    int mps;
    int mss;
    int mts;
    int sum;
};

class MssCore {
    int* my_a;

public:
    mss_state s;
    a_size b, e;

    MssCore(int a[]) :
            my_a(a), b(-1), e(-1)  { s = {0, 0, 0, 0};}
    MssCore(MssCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { s = {0, 0, 0, 0};}


    void operator()( const blocked_range<a_size>& r )
    {
        int *a = my_a;
        int mss = s.mss;
        int mts = s.mts;
        int mps = s.mps;
        int sum = s.sum;

        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            sum = sum + a[i];
            mps = max(sum, mps);
            mss = max (mss, mts + a[i]);
            mts = max (0, mts + a[i]);
        }

        s = {mps, mss, mts, sum};
    }

    void join(const MssCore& rhs) {
        s = {
                max(s.mps, s.sum + rhs.s.mps),
                max(s.mss, max(rhs.s.mss, rhs.s.mps + s.mts)),
                max(rhs.s.sum + s.mts, rhs.s.mts),
                s.sum + rhs.s.sum
        };
        e = rhs.e;
    }
};

int ExampleMss::parallel_apply() const{
    MssCore coc(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), coc);
    return  coc.s.mss;
}

int ExampleMss::seq_apply() const {
    int mts = 0;
    int mss = 0;
    for(a_size i = 0; i < n; i++) {
        mss = max (mss, mts + a[i]);
        mts = max (0, mts + a[i]);
    }
    return mss;
}

int ExampleMss::full_seq_apply() const {
    int mts = 0;
    int mss = 0;
    int mps = 0;
    int sum = 0;
    for(a_size i = 0; i < n; i++) {
        mss = max (mss, mts + a[i]);
        mts = max (0, mts + a[i]);
        sum += a[i];
        mps = max(mps, sum);
    }
    return mss + mps + sum;
}

/** Example : Mps*/

struct mps_state {
    int mps;
    int sum;
};

class MpsCore {
    int* my_a;

public:
    mps_state s;
    a_size b, e;

    MpsCore(int a[]) :
            my_a(a), b(-1), e(-1)  { s = {0, 0};}
    MpsCore(MpsCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { s = {0, 0};}


    void operator()( const blocked_range<a_size>& r )
    {
        int *a = my_a;
        int mps = s.mps;
        int sum = s.sum;

        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            sum = sum + a[i];
            mps = max(sum, mps);
        }

        s = {mps, sum};
    }

    void join(const MpsCore& rhs) {
        s = {
                max(s.mps, s.sum + rhs.s.mps),
                s.sum + rhs.s.sum
        };
        e = rhs.e;
    }
};

int ExampleMps::parallel_apply() const{
    MpsCore coc(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), coc);
    return  coc.s.mps;
}

int ExampleMps::seq_apply() const {
    int sum = 0;
    int mps = 0;
    for(a_size i = 0; i < n; i++) {
        sum += a[i];
        mps = max (sum, mps);
    }
    return mps;
}

int ExampleMps::full_seq_apply() const { return seq_apply();}

/** Example : return the second min element of the array */

struct  min2_state {
    int min;
    int min2;
};


class SecondMinCore {
    int* my_a;

public:
    min2_state dropwState;
    a_size b, e;

    SecondMinCore(int a[]) :
            my_a(a), b(-1), e(-1)  { dropwState = {INT32_MAX, INT32_MAX};}
    SecondMinCore(SecondMinCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { dropwState = {INT32_MAX, INT32_MAX};}


    void operator()( const blocked_range<a_size>& r )
    {
        int *a = my_a;
        int amin = dropwState.min;
        int min2 = dropwState.min2;

        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            min2 = min (min2, max(amin, a[i]));
            amin = min (amin, a[i]);
        }

        dropwState = {amin, min2};
    }

    void join(const SecondMinCore& rhs) {
        dropwState = {
                min(dropwState.min, rhs.dropwState.min),
                min(min(dropwState.min2, rhs.dropwState.min2), max(dropwState.min, rhs.dropwState.min))
        };
        e = rhs.e;
    }
};


int ExampleSecondMin::parallel_apply() const{
    SecondMinCore coc(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), coc);
    return  coc.dropwState.min2;
}

int ExampleSecondMin::seq_apply() const {
    int amin = INT32_MAX;
    int min2 = INT32_MAX;
    for(a_size i = 0; i < n; i++) {
        min2 = min (min2, max(amin, a[i]));
        amin = min (amin, a[i]);
    }
    return min2;
}

int ExampleSecondMin::full_seq_apply() const { return seq_apply();}


/** Example : drop the position of the first 1 in the array */

struct  dropw_state {
    bool drop;
    a_size pos;
};


class FirstOneCore {
    int* my_a;

public:
    dropw_state state;
    a_size b, e;

    FirstOneCore(int a[]) :
            my_a(a), b(-1), e(-1)  { state = {false, 0};}
    FirstOneCore(FirstOneCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { state = {false, 0};}


    void operator()(const blocked_range<a_size>& r )
    {
        int *a = my_a;
        bool drop = state.drop;
        a_size _pos = state.pos;

        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            if(a[i] == 1 && !drop){
                _pos = i;
                drop = true;
            }
        }

        state = {drop, _pos};
    }

    void join(const FirstOneCore& rhs) {
        state = {
                state.drop && rhs.state.drop,
                state.drop ? state.pos : rhs.state.pos
        };
        e = rhs.e;
    }
};


a_size ExampleFirstOne::parallel_apply() const{
    FirstOneCore coc(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), coc);
    return  coc.state.pos;
}

a_size ExampleFirstOne::seq_apply() const {
    a_size _pos = 0;
    bool drop = false;
    for(a_size i = 0; i < n; i++) {
        if(a[i] == 1 && !drop){
            _pos = i;
            drop = true;
        }
    }
    return _pos;
}

a_size ExampleFirstOne::full_seq_apply() const { return seq_apply();}

/** Example : return the length of the biggest block of (true) in the array */

struct  block1_state {
    bool conj;
    int current_len;
    int first_len;
    int max_len;
};


class MaxLengthBlockCore {
    bool* my_a;

public:
    block1_state state;
    a_size b, e;

    MaxLengthBlockCore(bool a[]) :
            my_a(a), b(-1), e(-1)  { state = {true, 0, 0, 0};}
    MaxLengthBlockCore(MaxLengthBlockCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { state = {true, 0 ,0 ,0};}


    void operator()(const blocked_range<a_size>& r )
    {
        bool *a = my_a;
        bool conj = state.conj;
        int cl = state.current_len;
        int fl = state.first_len;
        int ml = state.max_len;

        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            cl = a[i] ? cl + 1 : 0;
            ml = max (ml, cl);
            conj = conj && a[i];
            fl = fl + (conj ? 1 : 0);
        }

        state = {conj, cl, fl, ml};
    }

    void join(const MaxLengthBlockCore& rhs) {
        state = {
                state.conj && rhs.state.conj,
                (rhs.state.conj) ? state.current_len + rhs.state.first_len : rhs.state.current_len,
                state.first_len + (state.conj) ? rhs.state.first_len : 0,
                max(state.current_len + rhs.state.first_len, max(state.max_len, rhs.state.max_len))
        };
        e = rhs.e;
    }
};



int ExampleMaxLengthBlock::parallel_apply() const{
    MaxLengthBlockCore coc(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), coc);
    return  coc.state.max_len;
}

int ExampleMaxLengthBlock::full_seq_apply() const {
    int cl = 0;
    int ml = 0;
    bool conj = true;
    int fl = 0;
    for(a_size i = 0; i < n; i++) {
        cl = a[i] ? cl + 1 : 0;
        ml = max (ml, cl);
        conj = conj && a[i];
        fl = fl + (conj ? 1 : 0);
    }
    return ml + fl;
}


int ExampleMaxLengthBlock::seq_apply() const {
    int cl = 0;
    int ml = 0;
    for(a_size i = 0; i < n; i++) {
        cl = a[i] ? cl + 1 : 0;
        ml = max (ml, cl);
    }
    return ml;
}

/** Example : is_sorted */
struct is_sorted_state {
    int prev;
    int aux;
    bool is_sorted;
};

class IsSortedCore {
    int* my_a;

public:
    is_sorted_state s;
    a_size b, e;

    IsSortedCore(int a[]) :
            my_a(a), b(-1), e(-1)  { s = {INT32_MIN, 0, true};}
    IsSortedCore(IsSortedCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { s = {INT32_MIN, 0, true};}


    void operator()( const blocked_range<a_size>& r )
    {
        int *a = my_a;
        int tmp_prev = s.prev;
        bool is_sorted = s.is_sorted;

        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            is_sorted = is_sorted && (tmp_prev < a[i]);
            tmp_prev = a[i];
        }

        s = {tmp_prev, a[b], is_sorted};
    }

    void join(const IsSortedCore& rhs) {
        s = {
                rhs.s.prev,
                s.prev,
                s.is_sorted && (rhs.s.is_sorted && (s.prev < rhs.s.aux))
        };
        e = rhs.e;
    }
};


bool ExampleIsSorted::parallel_apply() const{
    IsSortedCore coc(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), coc);
    return  coc.s.is_sorted;
}

bool ExampleIsSorted::seq_apply() const {
    bool is_sorted = true;
    int prev = INT32_MIN;
    for(a_size i = 0; i < n; i++) {
        is_sorted = is_sorted && (prev < a[i]);
        prev = a[i];
    }
    return is_sorted;
}

bool ExampleIsSorted::full_seq_apply() const {
    bool is_sorted = true;
    int prev = INT32_MIN;
    for(a_size i = 0; i < n; i++) {
        is_sorted = is_sorted && (prev < a[i]);
        prev = a[i];
    }
    int afinal = a[n-1];
    return is_sorted;
}

/** Boolean example : line of sight */
/* We suppose that all buildings have a positive height */

struct line_of_sight_state {
    int amax;
    int aux;
    bool is_visible;
};

class LineOfSightCore {
    int* my_a;

public:
    line_of_sight_state s;
    a_size b, e;

    LineOfSightCore(int a[]) :
            my_a(a), b(-1), e(-1)  { s = {0, 0, true};}
    LineOfSightCore(LineOfSightCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { s = {0, 0, true};}


    void operator()( const blocked_range<a_size>& r )
    {
        int *a = my_a;
        int tmp_amax = s.amax;
        bool tmp_visible = s.is_visible;

        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            tmp_visible = tmp_amax <= a[i];
            tmp_amax = max(tmp_amax, a[i]);
        }

        s = {tmp_amax, a[e], tmp_visible};
    }

    void join(const LineOfSightCore& rhs) {
        s = {
                max(rhs.s.amax, s.amax),
                rhs.s.aux,
                max(rhs.s.amax, s.amax) <= rhs.s.aux
        };
        e = rhs.e;
    }
};



bool ExampleLineOfSight::parallel_apply() const{
    LineOfSightCore coc(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), coc);
    return  coc.s.is_visible;
}

bool ExampleLineOfSight::seq_apply() const {
    bool is_visible = true;
    int amax = 0;
    for (a_size i = 0; i < n; i++) {
        is_visible = amax <= a[i];
        amax = max(amax, a[i]);
    }

    return is_visible;
}

bool ExampleLineOfSight::full_seq_apply() const {
    bool is_visible = true;
    int amax = 0;
    for (a_size i = 0; i < n; i++) {
        is_visible = amax <= a[i];
        amax = max(amax, a[i]);
    }
    int afinal = a[n-1];
    return is_visible;
}




/** Boolean example : balanced parenthesis */
/* We suppose that all buildings have a positive height */

struct bal_par_state {
    int aux;
    bool bal;
    int cnt;
};

class BalancedParenthesisCore {
    bool* my_a;

public:
    bal_par_state parState;
    a_size b, e;

    BalancedParenthesisCore(bool a[]) :
            my_a(a), b(-1), e(-1)  { parState = {INT32_MIN, true, 0};}
    BalancedParenthesisCore(BalancedParenthesisCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { parState = {INT32_MIN, true, 0};}


    void operator()( const blocked_range<a_size>& r )
    {
        bool *a = my_a;

        int _aux = parState.aux;
        bool _bal = parState.bal;
        int _cnt = parState.cnt;

        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            _cnt += (a[i]? 1 : -1);
            _bal = _bal && (_cnt >= 0);
            _aux = min(_aux, _cnt);
        }

        parState = {_aux, _bal, _cnt};
    }

    void join(const BalancedParenthesisCore& rhs) {
        parState = {
                min(parState.aux, parState.cnt + rhs.parState.aux),
                parState.bal && (rhs.parState.aux + parState.cnt > 0),
                parState.cnt + rhs.parState.cnt
        };
        e = rhs.e;
    }
};


bool ExampleBalancedParenthesis::parallel_apply() const{
    BalancedParenthesisCore coc(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), coc);
    return  coc.parState.bal;
}

bool ExampleBalancedParenthesis::seq_apply() const {
    bool bal = true;
    int cnt = 0;
    for (a_size i = 0; i < n; i++) {
        cnt += (a[i]? 1 : -1);
        bal = bal && (cnt >= 0);
    }

    return bal;
}

bool ExampleBalancedParenthesis::full_seq_apply() const {
    bool bal = true;
    int cnt = 0;
    int minc = 0;
    for (a_size i = 0; i < n; i++) {
        cnt += (a[i]? 1 : -1);
        bal = bal && (cnt >= 0);
        minc = min(minc, cnt);
    }

    return bal;
}

/** Boolean example : seen false after true */
/* We suppose that all buildings have a positive height */

struct seen01_state {
    bool res;
    bool seen0;
    bool seen1;
};

class Seen01Core {
    bool* my_a;

public:
    seen01_state state;
    a_size b, e;

    Seen01Core(bool a[]) :
            my_a(a), b(-1), e(-1)  { state = {false, false, false};}
    Seen01Core(Seen01Core& x, split) :
            my_a(x.my_a), b(-1), e(-1) { state = {false, false, false};}


    void operator()( const blocked_range<a_size>& r )
    {
        bool *a = my_a;

        bool res = state.res;
        bool seen0 = state.seen0;
        bool seen1 = state.seen1;

        a_size end = r.end();

        if (b < 0 || r.begin() < b)
            b = r.begin();
        if (e < 0 || r.end() > e)
            e = r.end();

        for (a_size i = r.begin(); i!=end; ++i) {
            if (seen1 && !(a[i]))
                res = true;
            seen1 = seen1 || a[i];
            seen0 = seen0 || (!a[i]);
        }

        state = {res, seen0, seen1};
    }

    void join(const Seen01Core& rhs) {
        state = {
                (state.res || rhs.state.res) || (rhs.state.seen0 && state.seen1),
                (state.seen0 || rhs.state.seen0) || state.res,
                (state.seen1 || rhs.state.seen1) || rhs.state.res,
        };
        e = rhs.e;
    }
};



bool ExampleSeen01::parallel_apply() const{
    Seen01Core coc(a);
    parallel_reduce(blocked_range<a_size>(0,n,1000000), coc);
    return  coc.state.res;
}

bool ExampleSeen01::seq_apply() const {
    bool res = false;
    bool seen1 = true;
    for (a_size i = 0; i < n; i++) {
        if (seen1 && !(a[i]))
            res = true;
        seen1 = seen1 || a[i];
    }

    return res;
}

bool ExampleSeen01::full_seq_apply() const {
    bool res = false;
    bool seen1 = false;
    bool seen0 = false;
    for (a_size i = 0L; i < n; i++) {
        if (seen1 && !(a[i]))
            res = true;
        seen1 = seen1 || a[i];
        seen0 = seen0 || (!a[i]);
    }

    return res && seen0;
}