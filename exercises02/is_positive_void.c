

/*@ requires size >= 0;
    requires \valid(r);
    requires \valid(a + (0..size-1));
    assigns *r;
    behavior positive:
        assumes \forall integer k; 0<=k<size ==> a[k] >= 0;
        ensures *r == 1;
    behavior negative:
        assumes \exists integer k; 0<=k<size && a[k] < 0;
        ensures *r == 0;
    complete behaviors;
    disjoint behaviors;
 */
void is_positive(int * a, int size, int * r)
{
  int i;
  *r = 1;
  /*@ loop invariant 0 <= i <= size;
    @ loop invariant *r == 1 <==> \forall integer k; 0 <= k <i ==> 0 <= a[k];
    @ loop invariant *r == 0 <==> \exists integer k; 0 <= k <i && 0 > a[k];
    @ loop assigns i, *r;
    @ loop variant size - i; */

  for(i = 0; i < size; i++)
    if (a[i] < 0)
      *r = 0;
}
