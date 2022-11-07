#include <limits.h>

/*@
  requires \valid(value);
  requires INT_MIN < *value+step < INT_MAX;
  ensures \old(*value)+step == *value;
  assigns *value;
*/
void increment(int * value, int step)
{
  *value += step;
}
