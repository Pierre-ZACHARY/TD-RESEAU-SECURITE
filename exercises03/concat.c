#include <limits.h>
#include <stddef.h>
#include <stdint.h>

void concat(int * t1, size_t size1, int * t2, size_t size2, int * dst)
{
  for(size_t i = 0; i < size1 + size2; i++)
    if (i < size1)
      dst[i] = t1[i];
    else
      dst[i] = t2[i - size1];
}
