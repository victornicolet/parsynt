#include <iostream>
#include <tbb/tbb.h>
#include "ExampleUnit.h"
#include "Examples.h"

using namespace tbb;

class SumFoo {
    int* my_a;
public:
    int my_sum;
    int b, e;

    SumFoo(int a[]) : my_a(a), my_sum(0), b(-1), e(-1)  {}
    SumFoo(SumFoo& x, split ) : my_a(x.my_a), my_sum(0), b(-1), e(-1) {}


    void operator()( const blocked_range<size_t>& r )
    {
        int *a = my_a;
        int sum = my_sum;
        size_t end = r.end();

        if (b < 0 || r.begin() < b)
            b = (int) r.begin();
        if (e < 0 || r.end() > e)
            e = (int) r.end();

        for (size_t i = r.begin(); i!=end; ++i) {
            sum +=  a[i];
        }

        my_sum = sum;
    }

    void join(const SumFoo& y) {
        my_sum = my_sum + y.my_sum;
        e = y.e;
    }
};

void ExampleSum::init() {
    if(a == nullptr) {
        cout << "Initialization ..." << endl;
        a = new int[n];
        for (int i = 0; i < n; i++)
            a[i] = i;
        cout << "Initialization terminated." << endl;
    }
}

ExampleSum::~ExampleSum() {
    delete a;
}

int ExampleSum::parallel_apply() const {
    SumFoo sf(a);
    parallel_reduce(blocked_range<size_t>(0,n,1000000), sf );
    return sf.my_sum;
}

int ExampleSum::seq_apply() const {
    int sum = 0;
    for (int i = 0; i < n; i++)
        sum += a[i];
    return sum;
}

/** Example : compute length */

class LengthCore {
    int* my_a;
public:
    int my_length;
    int b, e;

    LengthCore(int a[]) : my_a(a), my_length(0), b(-1), e(-1)  {}
    LengthCore(LengthCore& x, split ) : my_a(x.my_a), my_length(0), b(-1), e(-1) {}


    void operator()( const blocked_range<size_t>& r )
    {
        int *a = my_a;
        int length = my_length;
        size_t end = r.end();

        if (b < 0 || r.begin() < b)
            b = (int) r.begin();
        if (e < 0 || r.end() > e)
            e = (int) r.end();

        for (size_t i = r.begin(); i!=end; ++i) {
            length+=1;
        }

        my_length = length;
    }

    void join(const LengthCore& rhs) {
        my_length = my_length + rhs.my_length;
        e = rhs.e;
    }
};

void ExampleLength::init() {
    if(a == nullptr) {
        cout << "Initialization of " << name << " ..." << endl;
        a = new int[n];
        for (int i = 0; i < n; i++)
            a[i] = i;
        cout << "Initialization terminated." << endl;
    }
}

ExampleLength::~ExampleLength() {
    delete a;
}

int ExampleLength::parallel_apply() const {
    LengthCore sf(a);
    parallel_reduce(blocked_range<size_t>(0,n,1000000), sf );
    return sf.my_length;
}

int ExampleLength::seq_apply() const {
    int length = 0;
    for (int i = 0; i < n; i++)
        length += 1;
    return length;
}



/** Other simple example : Max */
class MaxCore {
    int* my_a;
public:
    int amax;
    int b, e;

    MaxCore(int a[]) : my_a(a), amax(INT32_MIN), b(-1), e(-1)  {}
    MaxCore(MaxCore& x, split ) : my_a(x.my_a), amax(INT32_MIN), b(-1), e(-1) {}


    void operator()( const blocked_range<size_t>& r )
    {
        int *a = my_a;
        int tmp_amax = amax;
        size_t end = r.end();

        if (b < 0 || r.begin() < b)
            b = (int) r.begin();
        if (e < 0 || r.end() > e)
            e = (int) r.end();

        for (size_t i = r.begin(); i!=end; ++i) {
            tmp_amax = (tmp_amax > a[i]) ? tmp_amax : a[i];
        }

        amax = tmp_amax;
    }

    void join(const MaxCore& y) {
        amax = (amax > y.amax) ? amax : y.amax;
        e = y.e;
    }
};

void ExampleMax::init() {
    a = new int[n];
    for(int i = 0; i < n; i++)
        a[i] = rand() % 2000;
}

ExampleMax::~ExampleMax() { delete a;}

int ExampleMax::parallel_apply() const{
    MaxCore maxc(a);
    parallel_reduce(blocked_range<size_t>(0,n,1000000), maxc);
    return  maxc.amax;
}
int ExampleMax::seq_apply() const {
    int amax = INT32_MIN;
    for(size_t i =0; i < n; i++) {
        amax = (amax > a[i]) ? amax : a[i];
    }
    return amax;
}


/** Other example : Min */

class MinCore {
    int* my_a;
public:
    int amin;
    int b, e;

    MinCore(int a[]) : my_a(a), amin(INT32_MAX), b(-1), e(-1)  {}
    MinCore(MinCore& x, split ) : my_a(x.my_a), amin(INT32_MAX), b(-1), e(-1) {}


    void operator()( const blocked_range<size_t>& r )
    {
        int *a = my_a;
        int tmp_amin = amin;
        size_t end = r.end();

        if (b < 0 || r.begin() < b)
            b = (int) r.begin();
        if (e < 0 || r.end() > e)
            e = (int) r.end();

        for (size_t i = r.begin(); i!=end; ++i) {
            tmp_amin = (tmp_amin < a[i]) ? tmp_amin : a[i];
        }

        amin = tmp_amin;
    }

    void join(const MinCore& y) {
        amin = (amin > y.amin) ? amin : y.amin;
        e = y.e;
    }
};


void ExampleMin::init() {
    a = new int[n];
    for(int i = 0; i < n; i++)
        a[i] = (rand() % 2000) - (rand() % 1000);
}

ExampleMin::~ExampleMin() { delete a;}

int ExampleMin::parallel_apply() const{
    MinCore minc(a);
    parallel_reduce(blocked_range<size_t>(0,n,1000000), minc);
    return  minc.amin;
}
int ExampleMin::seq_apply() const {
    int amin = INT32_MAX;
    for(size_t i =0; i < n; i++) {
        amin = (amin < a[i]) ? amin : a[i];
    }
    return amin;
}

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
    int b, e;

    CountingOnesCore(bool a[]) :
            my_a(a), b(-1), e(-1)  { s = {0, false, false};}
    CountingOnesCore(CountingOnesCore& x, split) :
    my_a(x.my_a), b(-1), e(-1) { s = {0, false, false};}


    void operator()( const blocked_range<size_t>& r )
    {
        bool *a = my_a;
        int tmp_cnt = s.count;
        bool f = s.last;

        size_t end = r.end();

        if (b < 0 || r.begin() < b)
            b = (int) r.begin();
        if (e < 0 || r.end() > e)
            e = (int) r.end();

        for (size_t i = r.begin(); i!=end; ++i) {
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

ExampleCountingOnes::~ExampleCountingOnes() { delete a;}


void ExampleCountingOnes::init() {
    a = new bool[n];
    for(int i = 0; i < n; i++) {
        a[i] = (rand() % 2) - 1 > 0;
    }
}


int ExampleCountingOnes::parallel_apply() const{
    CountingOnesCore coc(a);
    parallel_reduce(blocked_range<size_t>(0,n,1000000), coc);
    return  coc.s.count;
}
int ExampleCountingOnes::seq_apply() const {
    int cnt = 0;
    bool first = false;
    bool last = false;
    for(int i = 0; i < n; i++) {
        cnt += (a[i] && !last) ? 1 : 0;
        last = a[i];
    }
    return cnt;
}


/** Example : counting the blocks of ones */
struct mps_pos_state {
    int mps;
    int pos;
    int sum;
};

class MpsPosCore {
    int* my_a;

public:
    mps_pos_state s;
    int b, e;

    MpsPosCore(int a[]) :
            my_a(a), b(-1), e(-1)  { s = {INT32_MIN, 0, 0};}
    MpsPosCore(MpsPosCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { s = {INT32_MIN, 0, 0};}


    void operator()( const blocked_range<size_t>& r )
    {
        int *a = my_a;
        int tmp_mps = s.mps;
        int tmp_sum = s.sum;
        int tmp_pos = s.pos;

        size_t end = r.end();

        if (b < 0 || r.begin() < b)
            b = (int) r.begin();
        if (e < 0 || r.end() > e)
            e = (int) r.end();

        for (size_t i = r.begin(); i!=end; ++i) {
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

ExampleMpsPos::~ExampleMpsPos() { delete a;}


void ExampleMpsPos::init() {
    a = new int[n];
    for(int i = 0; i < n; i++) {
        a[i] = (rand() % 20) - 10;
    }
}


int ExampleMpsPos::parallel_apply() const{
    MpsPosCore coc(a);
    parallel_reduce(blocked_range<size_t>(0,n,1000000), coc);
    return  coc.s.pos;
}
int ExampleMpsPos::seq_apply() const {
    int sum = 0;
    int mps = INT32_MIN;
    int pos = 0;
    for(int i = 0; i < n; i++) {
        sum += a[i];
        if (sum > mps) {
            pos = i;
            mps = sum;
        }
    }
    return pos;
}


/** Example : return the second min element of the array */

struct  min2_state {
    int min;
    int min2;
};


class SecondMinCore {
    int* my_a;

public:
    min2_state s;
    int b, e;

    SecondMinCore(int a[]) :
            my_a(a), b(-1), e(-1)  { s = {INT32_MAX, INT32_MAX};}
    SecondMinCore(SecondMinCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { s = {INT32_MAX, INT32_MAX};}


    void operator()( const blocked_range<size_t>& r )
    {
        int *a = my_a;
        int amin = s.min;
        int min2 = s.min2;

        size_t end = r.end();

        if (b < 0 || r.begin() < b)
            b = (int) r.begin();
        if (e < 0 || r.end() > e)
            e = (int) r.end();

        for (size_t i = r.begin(); i!=end; ++i) {
            min2 = min (min2, max(amin, a[i]));
            amin = min (amin, a[i]);
        }

        s = {amin, min2};
    }

    void join(const SecondMinCore& rhs) {
        s = {
                min(s.min, rhs.s.min),
                min(min(s.min2, rhs.s.min2), max(s.min, rhs.s.min))
        };
        e = rhs.e;
    }
};

ExampleSecondMin::~ExampleSecondMin() { delete a;}


void ExampleSecondMin::init() {
    a = new int[n];
    for(int i = 0; i < n; i++) {
        a[i] = (rand() % 20) - 10;
    }
}


int ExampleSecondMin::parallel_apply() const{
    SecondMinCore coc(a);
    parallel_reduce(blocked_range<size_t>(0,n,1000000), coc);
    return  coc.s.min2;
}

int ExampleSecondMin::seq_apply() const {
    int amin = INT32_MAX;
    int min2 = INT32_MAX;
    for(int i = 0; i < n; i++) {
        min2 = min (min2, max(amin, a[i]));
        amin = min (amin, a[i]);
    }
    return min2;
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
    int b, e;

    IsSortedCore(int a[]) :
            my_a(a), b(-1), e(-1)  { s = {INT32_MIN, 0, true};}
    IsSortedCore(IsSortedCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { s = {INT32_MIN, 0, true};}


    void operator()( const blocked_range<size_t>& r )
    {
        int *a = my_a;
        int tmp_prev = s.prev;
        bool is_sorted = s.is_sorted;

        size_t end = r.end();

        if (b < 0 || r.begin() < b)
            b = (int) r.begin();
        if (e < 0 || r.end() > e)
            e = (int) r.end();

        for (size_t i = r.begin(); i!=end; ++i) {
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

ExampleIsSorted::~ExampleIsSorted() { delete a;}


void ExampleIsSorted::init() {
    a = new int[n];
    for (int i = 0; i < n; i++) {
        a[i] = (rand() % 100);
    }
}


bool ExampleIsSorted::parallel_apply() const{
    IsSortedCore coc(a);
    parallel_reduce(blocked_range<size_t>(0,n,1000000), coc);
    return  coc.s.is_sorted;
}

bool ExampleIsSorted::seq_apply() const {
    bool is_sorted = true;
    int prev = INT32_MIN;
    for(int i = 0; i < n; i++) {
        is_sorted = is_sorted && (prev < a[i]);
        prev = a[i];
    }
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
    int b, e;

    LineOfSightCore(int a[]) :
            my_a(a), b(-1), e(-1)  { s = {0, 0, true};}
    LineOfSightCore(LineOfSightCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { s = {0, 0, true};}


    void operator()( const blocked_range<size_t>& r )
    {
        int *a = my_a;
        int tmp_amax = s.amax;
        bool tmp_visible = s.is_visible;

        size_t end = r.end();

        if (b < 0 || r.begin() < b)
            b = (int) r.begin();
        if (e < 0 || r.end() > e)
            e = (int) r.end();

        for (size_t i = r.begin(); i!=end; ++i) {
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

ExampleLineOfSight::~ExampleLineOfSight() { delete a;}


void ExampleLineOfSight::init() {
    a = new int[n];
    for (int i = 0; i < n; i++) {
        a[i] = abs(rand() % 100);
    }
}


bool ExampleLineOfSight::parallel_apply() const{
    LineOfSightCore coc(a);
    parallel_reduce(blocked_range<size_t>(0,n,1000000), coc);
    return  coc.s.is_visible;
}

bool ExampleLineOfSight::seq_apply() const {
    bool is_visible = true;
    int amax = 0;
    for (int i = 0; i < n; i++) {
        is_visible = amax <= a[i];
        amax = max(amax, a[i]);
    }

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
    int b, e;

    BalancedParenthesisCore(bool a[]) :
            my_a(a), b(-1), e(-1)  { parState = {INT32_MIN, true, 0};}
    BalancedParenthesisCore(BalancedParenthesisCore& x, split) :
            my_a(x.my_a), b(-1), e(-1) { parState = {INT32_MIN, true, 0};}


    void operator()( const blocked_range<size_t>& r )
    {
        bool *a = my_a;

        int _aux = parState.aux;
        bool _bal = parState.bal;
        int _cnt = parState.cnt;

        size_t end = r.end();

        if (b < 0 || r.begin() < b)
            b = (int) r.begin();
        if (e < 0 || r.end() > e)
            e = (int) r.end();

        for (size_t i = r.begin(); i!=end; ++i) {
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

ExampleBalancedParenthesis::~ExampleBalancedParenthesis() { delete a;}


void ExampleBalancedParenthesis::init() {
    a = new bool[n];
    for (int i = 0; i < n; i++) {
        a[i] = (abs(rand() % 100) - 50) > 0;
    }
}


bool ExampleBalancedParenthesis::parallel_apply() const{
    BalancedParenthesisCore coc(a);
    parallel_reduce(blocked_range<size_t>(0,n,1000000), coc);
    return  coc.parState.bal;
}

bool ExampleBalancedParenthesis::seq_apply() const {
    bool bal = true;
    int cnt = 0;
    for (int i = 0; i < n; i++) {
        cnt += (a[i]? 1 : -1);
        bal = bal && (cnt >= 0);
    }

    return bal;
}
