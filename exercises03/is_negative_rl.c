#include <stdbool.h>
#include <stddef.h>

/*@ requires 0 <= size && \valid(a + (0..size-1));
    assigns \nothing;
    behavior all_negative:
      assumes \forall integer k; 0 <= k < size ==> a[k] <= 0;
      ensures \result == true;
    behavior one_positive:
      assumes \exists integer k; 0 <= k < size && a[k] > 0;
      ensures \result == false;
    disjoint behaviors;
    complete behaviors; */
bool is_negative(int * a, int size)
{
    /*@ loop invariant -1 <= i < size ;
    @ loop invariant \forall integer k; i < k < size ==> a[k] <= 0;
    @ loop assigns i;
    @ loop variant size + i; */
  for(int i = size - 1; 0 <= i; i--)
    if (a[i] > 0)
      return false;
  return true;
}
