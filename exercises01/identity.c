#include <limits.h>

/*@ requires x < INT_MAX;
    ensures \result == x+1;
    assigns \nothing;*/
int incr(int x){ return x + 1; }

/*@ requires x > INT_MIN;
    ensures \result == x-1;
    assigns \nothing;*/
int decr(int x){ return x - 1; }

/*@ requires x < INT_MAX;
    requires x > INT_MIN;
    ensures \result == x;
    assigns \nothing;*/
int identity(int x){
  int tmp = decr(x);
  tmp = incr(tmp);
  return tmp;
}
