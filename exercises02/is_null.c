#include <stddef.h>

/*@ ensures \result == 0 <==> p != NULL;
  ensures \result == 1 <==> p == NULL;
  assigns \nothing;

*/
int is_null(void * p)
{
  return p == NULL;
}
