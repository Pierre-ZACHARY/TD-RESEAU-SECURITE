
#include <limits.h>


/*@ ensures a<b==>\result==b;
  @ ensures a>=b==>\result==a;
  @ assigns \nothing;
*/
int max(int a, int b)
{
  if (a < b)
    return b;
  else
    return a;
}
