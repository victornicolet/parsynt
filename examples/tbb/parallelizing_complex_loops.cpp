#include "tbb/tbb.h"
#include <cfloat>

/*
  Cases where the loops are not simple loops over arrays, but more complex
  data structures such as Linked Lists
*/

/*
  1 -  Parallel do
*/

/*
  1 - Parallel do
*/
// Functional 
void SerialApplyFooToList( const std::list<Item>& list ) {
    for( std::list<Item>::const_iterator i=list.begin() i!=list.end(); ++i ) 
        Foo(*i);
}

int main(int argc, char* argv[]) {
  return 0;
}
