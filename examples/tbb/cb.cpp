#include <iostream>
#include <sstream>
#include <cmath>
#include <tbb/tbb.h>


//  a simple stopwatch class.  It implements functions much like
//      a regular stopwatch:
//          clear()
//          start():    resets stopwatch to zero, and starts it.
//          lap():      returns the elapsed time.
//          stop();     stop the stopwatch
//          resume();   resumes the stopwatch
//          getTime();  returns elapsed time, may be used when stopped.



#include <sys/time.h>

typedef struct timeval TimeVal;

int
SYSgettimeofday(TimeVal *tval)
{
        struct timezone tz;
        return ::gettimeofday(tval, &tz);
}

#define GET_TIMER(tp)           SYSgettimeofday(tp)





class StopWatch
{
public:
    StopWatch();

    void        clear();
    void        start();
    double      lap() const;
    double      stop();
    void        resume();

    double      getTime() const;
    bool        isRunning() const;

    double      operator-( const StopWatch & );


    static double _timeDiff(const TimeVal &later, const TimeVal &sooner);

protected:
    bool        _running;               // the watch is running
    double      _elapsedTime;

    TimeVal     _startTime;
};

double 
StopWatch::_timeDiff( const TimeVal &later, const TimeVal &sooner )
{
    return double( later.tv_sec - sooner.tv_sec ) +
            1.0e-6 * ( later.tv_usec - sooner.tv_usec );
}


StopWatch::StopWatch()
{
    clear();
    _running = false;
}

void
StopWatch::clear()
{
    _elapsedTime = 0;
}

void
StopWatch::start()
{
    clear();
    resume();
}

double
StopWatch::lap() const
{
    if( _running )
    {
        TimeVal now;

        GET_TIMER(&now);
        return _elapsedTime + _timeDiff( now, _startTime );
    }
    return _elapsedTime;
}

double
StopWatch::stop()
{
    if( _running )
    {
        TimeVal now;

        GET_TIMER(&now);
        _running = false;

        return _elapsedTime += _timeDiff( now, _startTime );
    }
    return _elapsedTime;
}

void
StopWatch::resume()
{
    if( _running )
        clear();

    GET_TIMER(&_startTime);
    _running = true;
}

double
StopWatch::getTime() const
{
    return lap();                       // should they be different?
}

bool
StopWatch::isRunning() const
{
    return _running;
}

using namespace tbb;
 

class SumFoo {
    char* my_a;
public:
    int my_count;
    bool my_last; 
    bool my_first;
    int b, e;

    void operator()( const blocked_range<size_t>& r ) 
    {


        char *a = my_a;
        int count = my_count;
        int last = my_last;
        size_t end = r.end();

	if (b < 0 || r.begin() < b)
	    b = r.begin();
	if (e < 0 || r.end() > e)
	    e = r.end();
	   
	    my_first = (a[r.begin()] == '1'); 

        for (size_t i=r.begin(); i!=end; ++i) {
    	  if (a[i] == '1') {
	        if (!last) count++;	 
	        last = true; 
	      } else { last = false;}
	    }
            
        my_count = count;    
        my_last = last; 
    }
 
    SumFoo( SumFoo& x, split ) : my_a(x.my_a), my_count(0), my_first(false), my_last(false), b(-1), e(-1) {}
 
    void join(const SumFoo& y) 
    { 
    
       my_count = my_count + y.my_count;
       if (my_last && y.my_first) my_count--;      
       my_last = y.my_last; 
       
	   e = y.e;
    }
             
    SumFoo(char a[]) :
        my_a(a), my_count(0), my_first(false), my_last(false), b(-1), e(-1)
    {}
};

double ParallelSumFoo(char a[], size_t n) 
{
    SumFoo sf(a);
    parallel_reduce( blocked_range<size_t>(0,n,50000), sf );
    return sf.my_count;
}


class MyCounter {
    char* my_a;
public:
    int my_count;
    int my_count2;
    bool my_last; 
    int b, e;

    void operator()( const blocked_range<size_t>& r ) 
    {


        char *a = my_a;
        int count = my_count;
        int count2 = my_count2;
        int last = my_last;
        size_t end = r.end();

	if (b < 0 || r.begin() < b)
	    b = r.begin();
	if (e < 0 || r.end() > e)
	    e = r.end();
	   
	    if(a[r.begin()] == '1') {count2++; last = true;} 

        for (size_t i=r.begin()+1; i!=end; ++i) {
    	  if (a[i] == '1') {
	        if (!last) {count++; count2++;}	 
	        last = true; 
	      } else { last = false;}
	    }
            
        my_count = count;    
        my_count2 = count2;    
        my_last = last; 
    }
 
    MyCounter( MyCounter& x, split ) : my_a(x.my_a), my_count(0), my_count2(0),  my_last(false), b(-1), e(-1) {}
 
    void join(const MyCounter& y) 
    { 
    
       int tmp;
       if (!my_last) {tmp = y.my_count2;}
       else {tmp = y.my_count;}  
       my_count = my_count + tmp;
       my_count2 = my_count2 + tmp;    
       my_last = y.my_last; 
       
	   e = y.e;
    }
             
    MyCounter(char a[]) :
        my_a(a), my_count(0), my_count2(0), my_last(false), b(-1), e(-1)
    {}
};

double ParallelMyCounter(char a[], size_t n) 
{
    MyCounter mc(a);
    parallel_reduce( blocked_range<size_t>(0,n,50000), mc );
    return mc.my_count;
}



double SerialSumFoo(char a[], size_t n) 
{
    int count = 0;
    bool last = false;
    for (int i = 0; i < n; i++) {
	  if (a[i] == '1') {
	      if (!last) count++;	 
	      last = true; 
	  } else { last = false;}
	}
    return count;
}

int main(int argc, const char *argv[])
{
    //tbb::task_scheduler_init init(3);
    if (argc < 2)
    {
	std::cout << "no array size specified\n";
	exit(1);
    }

    int size = std::atoi(argv[1]);

    std::cout << "array size: " << size << "\n"; 

    char *c_array = new char[size];

    for (int i = 0; i < size; i++) {
	     c_array[i] = '1';
	     if (i % 8 == 0) c_array[i] = '0';
	}
    
    std::cout << "Initialization over.\n";

    StopWatch u; 
    u.start();
    double sum = ParallelSumFoo(c_array, size);
    std::cout << "parallel sum: " << sum << " in time: " << u.stop() << "\n";

    StopWatch v; 
    v.start();
    double msum = ParallelMyCounter(c_array, size);
    std::cout << "my parallel sum: " << sum << " in time: " << v.stop() << "\n";


    StopWatch w; 
    w.start();
    double ssum = SerialSumFoo(c_array, size);
     
    std::cout << "serial sum: " << ssum << " in time: " << w.stop() << "\n";

    delete[] c_array;
}
