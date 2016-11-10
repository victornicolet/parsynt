#include "Stopwatch.h"

//  a simple stopwatch class.  It implements functions much like
//      a regular stopwatch:
//          clear()
//          start():    resets stopwatch to zero, and starts it.
//          lap():      returns the elapsed time.
//          stop();     stop the stopwatch
//          resume();   resumes the stopwatch
//          getTime();  returns elapsed time, may be used when stopped.

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

void StopWatch::clear() { _elapsedTime = 0; }

void StopWatch::start()
{
    clear();
    resume();
}

double StopWatch::lap() const
{
    if( _running )
    {
        TimeVal now;
        getTimer(&now);
        return _elapsedTime + _timeDiff( now, _startTime );
    }
    return _elapsedTime;
}

double StopWatch::stop()
{
    if( _running )
    {
        TimeVal now;
        getTimer(&now);
        _running = false;
        return _elapsedTime += _timeDiff( now, _startTime );
    }
    return _elapsedTime;
}

void StopWatch::resume()
{
    if( _running )
        clear();
    getTimer(&_startTime);
    _running = true;
}

double StopWatch::getTime() const { return lap();}                       // should they be different?

bool StopWatch::isRunning() const { return _running;}
