//
// Created by nicolet on 08/11/16.
//

#ifndef TBB_TESTS_STOPWATCH_H
#define TBB_TESTS_STOPWATCH_H
#include <cmath>
#include <sys/time.h>

typedef struct timeval TimeVal;

class StopWatch
{
public:
    StopWatch();

    static int getTimer (TimeVal* tp) {
        struct timezone tz;
        return ::gettimeofday(tp, &tz);
    }

    void        clear();
    void        start();
    double      lap() const;
    double      stop();
    void        resume();

    double      getTime() const;
    bool        isRunning() const;

    double      operator-(const StopWatch & );

    static double _timeDiff(const TimeVal &later, const TimeVal &sooner);

protected:
    bool        _running;               // the watch is running
    double      _elapsedTime;

    TimeVal     _startTime;
};

#endif //TBB_TESTS_STOPWATCH_H
