#include <limits.h>

/*@ requires start >= 0;
    requires end >= 0;
    requires start + end <= INT_MAX;
    ensures \result == (start + end)/2;
    assigns \nothing;
 */
int mid(int start, int end)
{
  return (start + end) / 2;
}
