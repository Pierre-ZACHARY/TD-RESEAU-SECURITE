
/*@ requires size >= 0;
    requires \valid(a + (0..size-1));
    assigns \nothing;
    behavior positive:
        assumes \forall integer k; 0<=k<size ==> a[k] >= 0;
        ensures \result == 1;
    behavior negative:
        assumes \exists integer k; 0<=k<size && a[k] < 0;
        ensures \result == 0;

    complete behaviors;
    disjoint behaviors;
 */
int is_positive(int * a, int size)
{
  /*@ loop invariant 0 <= i <= size;
    @ loop invariant \forall integer k; 0 <= k < i ==> 0 <= a[k];
    @ loop assigns i;
    @ loop variant size - i; */
  for(int i = 0; i < size; i++)
    if (a[i] < 0)
      return 0;
  return 1;
}
